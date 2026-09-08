'use strict';
/* ==========================================================================
   JHON PARRILLA · POS — Servidor de sincronización
   --------------------------------------------------------------------------
   Un solo archivo, igual que en INTPLANNER: Express + MongoDB Atlas.

   La aplicación (public/index.html) NO se toca. Ya trae su capa `Sync` con
   un protocolo definido; este servidor simplemente lo responde:

     GET  /salud                 ¿hay servidor aquí?
     POST /sync                  sube la cola y baja lo que hicieron los demás
     GET  /estado                base completa (botón "Traer los datos")
     POST /sembrar               publica la base inicial (botón "Publicar")
     POST /respaldo              copia de seguridad en el servidor
     GET  /respaldos             lista de copias
     GET  /respaldo/:nombre      una copia concreta

   Además sirve el propio HTML en /. Como la app hace `Sync.autoconfigurar()`
   al arrancar y toma `location.origin`, abrir la URL del servidor deja el
   equipo conectado solo: nadie teclea direcciones.
   ========================================================================== */

const path = require('path');
const express = require('express');
const compression = require('compression');
const { MongoClient } = require('mongodb');

const PORT = process.env.PORT || 3000;
const MONGODB_URI = process.env.MONGODB_URI || '';
const DB_NAME = process.env.MONGODB_DB || 'jhonparrilla';
const MAX_RESPALDOS = Number(process.env.MAX_RESPALDOS || 40);
const PERMITIR_FORZAR = String(process.env.PERMITIR_FORZAR || '1') === '1';
const VERSION = '1.0.0';

/* Colecciones que viajan. Todo lo demás que llegue se ignora en silencio.
   `audit` queda fuera a propósito: es la bitácora local de cada equipo. */
const ENTIDADES = new Set([
  'config', 'users', 'categories', 'products', 'meats', 'staff',
  'clients', 'sales', 'orders', 'purchases', 'cash', 'meals',
  'gastos', 'domiciliarios'
]);

/* ── Conexión ───────────────────────────────────────────────────────────── */
let cliente = null, db = null, colReg = null, colCnt = null, colBk = null;
let listo = false, errorConexion = null;

async function conectar() {
  if (!MONGODB_URI) throw new Error('Falta la variable MONGODB_URI');
  cliente = new MongoClient(MONGODB_URI, { maxPoolSize: 10, serverSelectionTimeoutMS: 15000 });
  await cliente.connect();
  db = cliente.db(DB_NAME);
  colReg = db.collection('registros');
  colCnt = db.collection('contadores');
  colBk = db.collection('respaldos');
  await colReg.createIndex({ clave: 1 }, { unique: true });
  await colReg.createIndex({ seq: 1 });
  await colReg.createIndex({ entidad: 1 });
  await colBk.createIndex({ generado: -1 });
  await colBk.createIndex({ nombre: 1 }, { unique: true });
  listo = true;
  errorConexion = null;
  console.log('[mongo] conectado a', DB_NAME);
}

/* ── Cursor incremental ─────────────────────────────────────────────────
   Cada escritura recibe un número `seq` de un contador atómico. El cliente
   guarda el último que vio y pide "lo que pasó después".

   `enVuelo` evita el hueco clásico: si el equipo A reservó el 105 y todavía
   no lo escribió, el equipo B no puede llevarse el cursor hasta el 106,
   porque entonces no vería nunca el 105. Solo se entrega hasta el número
   anterior al menor reservado.
   ------------------------------------------------------------------- */
const enVuelo = new Set();

async function reservar(n) {
  const r = await colCnt.findOneAndUpdate(
    { _id: 'seq' }, { $inc: { valor: n } },
    { upsert: true, returnDocument: 'after' }
  );
  const doc = (r && r.value) ? r.value : r;
  const fin = Number((doc && doc.valor) || n);
  const base = fin - n + 1;
  for (let i = 0; i < n; i++) enVuelo.add(base + i);
  return base;
}
function liberar(base, n) { for (let i = 0; i < n; i++) enVuelo.delete(base + i); }
function techo() {
  let m = Infinity;
  for (const v of enVuelo) if (v < m) m = v;
  return m === Infinity ? Infinity : m - 1;
}
async function seqActual() {
  const c = await colCnt.findOne({ _id: 'seq' });
  return Number((c && c.valor) || 0);
}

/* ── Escritura de un lote de operaciones ────────────────────────────────
   Todo es un upsert idempotente con la clave `entidad:id`. El conflicto se
   resuelve como en el cliente: gana el `act` más reciente. Los borrados de
   la app son lógicos (`borrado:true`), así que entran por el mismo camino.
   ------------------------------------------------------------------- */
async function aplicarOps(ops, sede) {
  const propios = new Set();
  if (!Array.isArray(ops) || !ops.length) return propios;

  const porClave = new Map();
  for (const op of ops) {
    if (!op || !ENTIDADES.has(op.entidad)) continue;
    const data = op.payload;
    if (!data || typeof data !== 'object') continue;
    const id = op.entidad === 'config' ? 'config' : data.id;
    if (!id) continue;
    const v = {
      clave: op.entidad + ':' + id, entidad: op.entidad, id: String(id),
      data, act: String(data.act || '')
    };
    const previo = porClave.get(v.clave);
    if (!previo || v.act >= previo.act) porClave.set(v.clave, v);
  }
  const lista = Array.from(porClave.values());
  if (!lista.length) return propios;

  const previos = await colReg
    .find({ clave: { $in: lista.map(v => v.clave) } }, { projection: { clave: 1, act: 1 } })
    .toArray();
  const mapa = new Map(previos.map(p => [p.clave, p.act || '']));

  const base = await reservar(lista.length);
  const escrituras = [];
  lista.forEach((v, i) => {
    const seq = base + i;
    const actPrevio = mapa.get(v.clave);
    const obsoleto = actPrevio && v.act && actPrevio > v.act;
    if (obsoleto) {
      // El servidor ya tiene algo más nuevo. No se pisa: se le sube el número
      // para que la versión buena vuelva a bajar a todos, incluido quien envió.
      escrituras.push({ updateOne: { filter: { clave: v.clave }, update: { $set: { seq, ts: new Date() } } } });
    } else {
      escrituras.push({
        updateOne: {
          filter: { clave: v.clave },
          update: { $set: { clave: v.clave, entidad: v.entidad, id: v.id, data: v.data, act: v.act, seq, sede: sede || null, ts: new Date() } },
          upsert: true
        }
      });
      propios.add(seq);   // no se le devuelve a quien acaba de mandarlo
    }
  });

  try { await colReg.bulkWrite(escrituras, { ordered: false }); }
  finally { liberar(base, lista.length); }
  return propios;
}

/* ── App ────────────────────────────────────────────────────────────────── */
const app = express();
app.set('trust proxy', 1);          // Render va detrás de un proxy
app.use(compression());
app.use(express.json({ limit: '40mb' }));

app.use((req, res, next) => {
  res.set('Access-Control-Allow-Origin', '*');
  res.set('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  res.set('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  if (req.method === 'OPTIONS') return res.sendStatus(204);
  next();
});

function exigirMongo(req, res, next) {
  if (!listo) return res.status(503).json({ ok: false, error: 'base de datos no disponible', detalle: errorConexion });
  next();
}
const guardia = fn => (req, res) => fn(req, res).catch(err => {
  console.error('[error]', req.method, req.path, err.message);
  res.status(500).json({ ok: false, error: err.message });
});

/* ── GET /salud ─────────────────────────────────────────────────────────
   Lo que la app pregunta para saber si hay servidor. `esEsteEquipo` va en
   falso siempre: el servidor vive en la nube, no en ninguna tablet.
   ------------------------------------------------------------------- */
app.get(['/salud', '/health'], guardia(async (req, res) => {
  let registros = 0;
  if (listo) { try { registros = await colReg.estimatedDocumentCount(); } catch (e) {} }
  res.json({
    ok: listo, servicio: 'jhon-parrilla-pos', version: VERSION,
    db: listo ? 'conectada' : 'sin conexión', registros,
    esEsteEquipo: false, hora: new Date().toISOString()
  });
}));

/* ── POST /sync ─────────────────────────────────────────────────────── */
app.post('/sync', exigirMongo, guardia(async (req, res) => {
  const { sede, cursor, ops } = req.body || {};
  const lote = Array.isArray(ops) ? ops : [];
  const propios = await aplicarOps(lote, sede);

  const desde = Number(cursor) || 0;
  const tope = techo();
  const filtro = { seq: { $gt: desde } };
  if (tope !== Infinity) filtro.seq.$lte = tope;

  const docs = await colReg.find(filtro).sort({ seq: 1 }).limit(500).toArray();
  const cambios = docs
    .filter(d => !propios.has(d.seq))
    .map(d => ({ entidad: d.entidad, data: d.data }));

  res.json({
    ok: true,
    aceptadas: lote.map(o => o && o.opId).filter(Boolean),
    cursor: docs.length ? docs[docs.length - 1].seq : desde,
    cambios,
    faltan: docs.length === 500
  });
}));

/* ── GET /estado ────────────────────────────────────────────────────── */
app.get('/estado', exigirMongo, guardia(async (req, res) => {
  const docs = await colReg.find({}).sort({ seq: 1 }).toArray();
  const estado = {};
  ENTIDADES.forEach(e => { if (e !== 'config') estado[e] = []; });
  let cursor = 0;
  docs.forEach(d => {
    if (d.seq > cursor) cursor = d.seq;
    if (d.entidad === 'config') estado.config = d.data;
    else if (Array.isArray(estado[d.entidad])) estado[d.entidad].push(d.data);
  });
  res.json({ ok: true, estado, cursor, registros: docs.length });
}));

/* ── POST /sembrar ──────────────────────────────────────────────────── */
app.post('/sembrar', exigirMongo, guardia(async (req, res) => {
  const { sede, estado, forzar } = req.body || {};
  if (!estado || !estado.config) return res.status(400).json({ ok: false, error: 'faltan datos' });

  const existentes = await colReg.countDocuments();
  if (existentes > 0 && !forzar) return res.status(409).json({ ok: false, registros: existentes });
  if (existentes > 0 && forzar && !PERMITIR_FORZAR)
    return res.status(403).json({ ok: false, error: 'el servidor está bloqueado contra sobrescrituras (PERMITIR_FORZAR=0)' });

  const filas = [];
  Object.keys(estado).forEach(entidad => {
    if (!ENTIDADES.has(entidad)) return;
    const v = estado[entidad];
    if (entidad === 'config') {
      if (v && typeof v === 'object') filas.push({ entidad, id: 'config', data: Object.assign({ id: 'config' }, v) });
    } else if (Array.isArray(v)) {
      v.forEach(r => { if (r && r.id) filas.push({ entidad, id: String(r.id), data: r }); });
    }
  });
  if (!filas.length) return res.status(400).json({ ok: false, error: 'no hay registros para publicar' });

  if (existentes > 0) await colReg.deleteMany({});
  const base = await reservar(filas.length);
  try {
    await colReg.bulkWrite(filas.map((f, i) => ({
      updateOne: {
        filter: { clave: f.entidad + ':' + f.id },
        update: { $set: { clave: f.entidad + ':' + f.id, entidad: f.entidad, id: f.id, data: f.data, act: String(f.data.act || ''), seq: base + i, sede: sede || null, ts: new Date() } },
        upsert: true
      }
    })), { ordered: false });
  } finally { liberar(base, filas.length); }

  console.log('[sembrar]', filas.length, 'registros publicados');
  res.json({ ok: true, registros: filas.length, cursor: base + filas.length - 1 });
}));

/* ── Respaldos ──────────────────────────────────────────────────────── */
app.post('/respaldo', exigirMongo, guardia(async (req, res) => {
  const { motivo, dump } = req.body || {};
  if (!dump || !dump.datos) return res.status(400).json({ ok: false, error: 'respaldo vacío' });
  const d = new Date();
  const p = n => String(n).padStart(2, '0');
  const nombre = 'respaldo-' + d.getFullYear() + p(d.getMonth() + 1) + p(d.getDate()) +
    '-' + p(d.getHours()) + p(d.getMinutes()) + p(d.getSeconds()) + '-' +
    Math.random().toString(36).slice(2, 6) + '.json';

  await colBk.insertOne({
    nombre, motivo: motivo || dump.motivo || 'automático',
    generado: dump.generado || d.toISOString(),
    usuario: dump.usuario || 'sistema', sede: dump.sede || null,
    equipo: dump.equipo || '', resumen: dump.resumen || {}, dump
  });

  const sobran = await colBk.find({}, { projection: { nombre: 1 } })
    .sort({ generado: -1 }).skip(MAX_RESPALDOS).toArray();
  if (sobran.length) await colBk.deleteMany({ nombre: { $in: sobran.map(s => s.nombre) } });

  res.json({ ok: true, archivo: nombre });
}));

app.get('/respaldos', exigirMongo, guardia(async (req, res) => {
  const docs = await colBk.find({}, { projection: { dump: 0 } }).sort({ generado: -1 }).limit(MAX_RESPALDOS).toArray();
  res.json({
    ok: true,
    archivos: docs.map(d => ({
      archivo: d.nombre, id: d.nombre, fecha: d.generado, motivo: d.motivo,
      usuario: d.usuario, equipo: d.equipo, resumen: d.resumen || {}
    }))
  });
}));

app.get('/respaldo/:nombre', exigirMongo, guardia(async (req, res) => {
  const doc = await colBk.findOne({ nombre: req.params.nombre });
  if (!doc) return res.status(404).json({ ok: false, error: 'no existe' });
  res.json(doc.dump);
}));

/* ── La aplicación ──────────────────────────────────────────────────────
   Se sirve sin caché para que "Buscar actualización" traiga siempre la
   última versión del archivo que esté en el repositorio.
   ------------------------------------------------------------------- */
const PUB = path.join(__dirname, 'public');
app.get('/', (req, res) => {
  res.set('Cache-Control', 'no-cache, must-revalidate');
  res.sendFile(path.join(PUB, 'index.html'));
});
app.use(express.static(PUB, { setHeaders: r => r.set('Cache-Control', 'no-cache') }));

app.use((req, res) => res.status(404).json({ ok: false, error: 'ruta no encontrada' }));

/* ── Arranque ───────────────────────────────────────────────────────────
   El servidor web levanta primero y Mongo se conecta detrás: así Render no
   marca el despliegue como fallido si Atlas tarda en responder.
   ------------------------------------------------------------------- */
app.listen(PORT, () => {
  console.log('[web] escuchando en el puerto', PORT);
  conectar().catch(err => {
    errorConexion = err.message;
    console.error('[mongo] no se pudo conectar:', err.message);
    setInterval(() => {
      if (listo) return;
      conectar().catch(e => { errorConexion = e.message; });
    }, 20000);
  });
});

process.on('unhandledRejection', err => console.error('[promesa]', err && err.message));
process.on('uncaughtException', err => console.error('[excepción]', err && err.message));

'use strict';
/* ==========================================================================
   JHON PARRILLA · POS — Servidor de sincronización sobre MySQL
   --------------------------------------------------------------------------
   Un solo archivo. La aplicación (public/index.html) no se toca: ya habla
   este protocolo y le da igual qué motor haya detrás.

     GET  /salud                 ¿hay servidor aquí?
     POST /sync                  sube la cola y baja lo que hicieron los demás
     GET  /estado                base completa (botón "Traer los datos")
     POST /sembrar               publica la base inicial (botón "Publicar")
     POST /respaldo              copia de seguridad en el servidor
     GET  /respaldos             lista de copias
     GET  /respaldo/:nombre      una copia concreta

   Dónde se gastan los milisegundos, en orden de importancia:

   1. El sondeo sin novedades es el caso normal. Cada tablet pregunta cada
      cinco segundos y casi siempre no hay nada nuevo. Ese camino cuesta
      UNA consulta indexada por `seq` y nada más: ni transacción, ni
      contador, ni escrituras.
   2. Cuando sí hay operaciones, van todas juntas: una reserva de números,
      una lectura de versiones y un INSERT múltiple. Cuatro viajes a la
      base como máximo, sin importar si son 2 o 200 platos.
   3. El pool mantiene las conexiones abiertas. Abrir una conexión TLS a un
      MySQL gestionado cuesta más que la consulta en sí.
   ========================================================================== */

const path = require('path');
const zlib = require('zlib');
const { promisify } = require('util');
const express = require('express');
const compression = require('compression');
const mysql = require('mysql2/promise');

const gzip = promisify(zlib.gzip);
const gunzip = promisify(zlib.gunzip);

const PORT = process.env.PORT || 3000;
const MYSQL_URL = process.env.MYSQL_URL || process.env.DATABASE_URL || '';
const MYSQL_CA = process.env.MYSQL_CA || '';
const MAX_RESPALDOS = Number(process.env.MAX_RESPALDOS || 40);
const PERMITIR_FORZAR = String(process.env.PERMITIR_FORZAR || '1') === '1';
const VERSION = '2.0.0-mysql';

/* Colecciones que viajan. `audit` queda fuera: es la bitácora local de cada
   equipo y no tiene por qué ocupar sitio ni ancho de banda. */
const ENTIDADES = new Set([
  'config', 'users', 'categories', 'products', 'meats', 'staff',
  'clients', 'sales', 'orders', 'purchases', 'cash', 'meals',
  'gastos', 'domiciliarios'
]);

/* ── Diagnóstico de conexión ────────────────────────────────────────────
   Los errores de MySQL son secos. Aquí se traducen a qué hay que tocar.
   ------------------------------------------------------------------- */
function revisarURL(url) {
  if (!url) return { causa: 'No hay cadena de conexión.',
    arreglo: 'Falta la variable MYSQL_URL en el servicio. Se copia entera desde el panel del proveedor: empieza por mysql:// y termina con ?ssl-mode=REQUIRED.' };
  if (/<.*>/.test(url)) return { causa: 'La cadena todavía trae un marcador de plantilla.',
    arreglo: 'Reemplaza el trozo entre < y >, incluidos los signos, por el valor real.' };
  if (!/^mysql:\/\//.test(url)) return { causa: 'La cadena no empieza por mysql://',
    arreglo: 'Usa la URI completa del proveedor, no los datos sueltos de host y puerto.' };
  const cuerpo = url.slice(8);
  if (!cuerpo.includes('@')) return { causa: 'La cadena no trae usuario ni contraseña.',
    arreglo: 'Debe verse así: mysql://usuario:clave@host:puerto/basededatos' };
  const clave = cuerpo.slice(0, cuerpo.lastIndexOf('@')).split(':').slice(1).join(':');
  if (/[@:/?#[\]]/.test(clave)) return { causa: 'La contraseña trae símbolos que parten la cadena.',
    arreglo: 'Los signos @ : / ? # [ ] hay que codificarlos. Lo más simple es regenerar la contraseña en el panel del proveedor.' };
  const trasArroba = cuerpo.slice(cuerpo.lastIndexOf('@') + 1);
  const ruta = trasArroba.split('?')[0];
  if (!ruta.includes('/') || !ruta.split('/')[1]) return { causa: 'La cadena no dice a qué base de datos entrar.',
    arreglo: 'Después del puerto va una barra y el nombre de la base. En Aiven suele llamarse defaultdb.' };
  return null;
}

function diagnosticar(err) {
  const cod = (err && err.code) || '';
  const m = String((err && err.message) || err);
  if (cod === 'ER_ACCESS_DENIED_ERROR' || /Access denied/i.test(m)) return {
    causa: 'El servidor MySQL rechazó el usuario o la contraseña.',
    arreglo: 'Vuelve a copiar la cadena completa desde el panel del proveedor. Si la contraseña se regeneró, la anterior deja de servir al instante.' };
  if (cod === 'ER_BAD_DB_ERROR') return {
    causa: 'La base de datos indicada no existe.',
    arreglo: 'Revisa el nombre que va después del puerto. En Aiven la base que viene creada se llama defaultdb.' };
  if (cod === 'ENOTFOUND' || /getaddrinfo/i.test(m)) return {
    causa: 'El nombre del servidor no resuelve.',
    arreglo: 'El host quedó cortado o mal copiado. Debe verse como algo.aivencloud.com y no llevar espacios.' };
  if (cod === 'ETIMEDOUT' || cod === 'PROTOCOL_SEQUENCE_TIMEOUT' || /timeout/i.test(m)) return {
    causa: 'El servidor no respondió a tiempo.',
    arreglo: 'Suele ser el cortafuegos del proveedor. Autoriza el acceso desde cualquier IP, porque los servicios de despliegue no tienen IP fija. Si el servicio está apagado por inactividad, enciéndelo desde el panel.' };
  if (/self.signed|certificate|SSL|TLS/i.test(m)) return {
    causa: 'El certificado del servidor no se pudo verificar.',
    arreglo: 'Descarga el certificado CA del proveedor y pega su contenido completo en la variable MYSQL_CA. Sin ella la conexión sigue cifrada pero no se verifica quién está al otro lado.' };
  if (cod === 'ECONNREFUSED') return {
    causa: 'El servidor rechazó la conexión.',
    arreglo: 'Revisa el puerto: los MySQL gestionados rara vez usan el 3306, suelen dar uno propio.' };
  return { causa: 'Fallo de conexión no reconocido.',
    arreglo: 'Abajo va el mensaje crudo de MySQL, que es lo que hay que mirar.' };
}

/* ── Conexión ───────────────────────────────────────────────────────────── */
let pool = null, listo = false, errorConexion = null;

function opciones() {
  const url = new URL(MYSQL_URL);
  const conf = {
    host: url.hostname,
    port: Number(url.port || 3306),
    user: decodeURIComponent(url.username),
    password: decodeURIComponent(url.password),
    database: decodeURIComponent(url.pathname.replace(/^\//, '')),
    // El pool es la diferencia entre pagar el saludo TLS en cada consulta o
    // pagarlo una vez. Con dos o tres tablets, cinco conexiones sobran.
    connectionLimit: Number(process.env.MYSQL_POOL || 5),
    waitForConnections: true,
    enableKeepAlive: true,
    keepAliveInitialDelay: 10000,
    connectTimeout: 15000,
    charset: 'utf8mb4_general_ci',
    timezone: 'Z',
    supportBigNumbers: true,
    bigNumberStrings: false
  };
  const modo = (url.searchParams.get('ssl-mode') || 'REQUIRED').toUpperCase();
  if (modo !== 'DISABLED') {
    conf.ssl = MYSQL_CA
      ? { ca: MYSQL_CA.replace(/\\n/g, '\n'), minVersion: 'TLSv1.2' }
      : { rejectUnauthorized: false, minVersion: 'TLSv1.2' };
  }
  return conf;
}

const ESQUEMA = [
  `CREATE TABLE IF NOT EXISTS registros (
     clave   VARCHAR(190) NOT NULL,
     entidad VARCHAR(40)  NOT NULL,
     id_reg  VARCHAR(140) NOT NULL,
     datos   LONGTEXT     NOT NULL,
     act     VARCHAR(40)  NOT NULL DEFAULT '',
     seq     BIGINT       NOT NULL,
     sede    VARCHAR(60)  NULL,
     ts      DATETIME     NOT NULL,
     PRIMARY KEY (clave),
     KEY idx_seq (seq),
     KEY idx_entidad (entidad)
   ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4`,
  `CREATE TABLE IF NOT EXISTS contadores (
     nombre VARCHAR(40) NOT NULL,
     valor  BIGINT NOT NULL DEFAULT 0,
     PRIMARY KEY (nombre)
   ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4`,
  `CREATE TABLE IF NOT EXISTS respaldos (
     nombre   VARCHAR(140) NOT NULL,
     motivo   VARCHAR(160) NULL,
     generado VARCHAR(40)  NULL,
     usuario  VARCHAR(140) NULL,
     sede     VARCHAR(60)  NULL,
     equipo   VARCHAR(140) NULL,
     resumen  LONGTEXT     NULL,
     dump     LONGBLOB     NOT NULL,
     bytes    INT          NOT NULL DEFAULT 0,
     PRIMARY KEY (nombre),
     KEY idx_generado (generado)
   ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4`,
  `INSERT IGNORE INTO contadores (nombre, valor) VALUES ('seq', 0)`
];

async function conectar() {
  const problema = revisarURL(MYSQL_URL);
  if (problema) { const e = new Error(problema.causa); e.diagnostico = problema; throw e; }
  const p = mysql.createPool(opciones());
  const cx = await p.getConnection();
  try { for (const sql of ESQUEMA) await cx.query(sql); }
  finally { cx.release(); }
  pool = p;
  listo = true;
  errorConexion = null;
  console.log('[mysql] conectado y esquema listo');
}

/* ── Numeración de cambios ──────────────────────────────────────────────
   Cada escritura recibe un `seq` creciente; el cliente guarda el último que
   vio y pide "lo que pasó después". LAST_INSERT_ID(expr) reserva un bloque
   de forma atómica y devuelve el valor en el mismo viaje, sin transacción.

   `enVuelo` tapa el hueco entre reservar y escribir: si la tablet A tiene
   reservado el 105 y aún no lo guarda, a la tablet B no se le puede mover
   el cursor hasta el 106, porque entonces nunca vería el 105.
   ------------------------------------------------------------------- */
const enVuelo = new Set();

async function reservar(n) {
  const cx = await pool.getConnection();
  try {
    const [r] = await cx.query(
      'UPDATE contadores SET valor = LAST_INSERT_ID(valor + ?) WHERE nombre = ?', [n, 'seq']);
    const fin = Number(r.insertId);
    const base = fin - n + 1;
    for (let i = 0; i < n; i++) enVuelo.add(base + i);
    return base;
  } finally { cx.release(); }
}
function liberar(base, n) { for (let i = 0; i < n; i++) enVuelo.delete(base + i); }
function techo() {
  let m = Infinity;
  for (const v of enVuelo) if (v < m) m = v;
  return m === Infinity ? Infinity : m - 1;
}

const leerDatos = fila => {
  try { return JSON.parse(fila.datos); } catch (e) { return null; }
};

/* ── Escritura de un lote de operaciones ────────────────────────────────
   Conflictos: gana el `act` más reciente, igual que en el cliente. Los
   borrados son lógicos (`borrado:true`) y entran por el mismo camino.
   ------------------------------------------------------------------- */
async function aplicarOps(ops, sede) {
  const propios = new Set();
  if (!Array.isArray(ops) || !ops.length) return propios;

  const porClave = new Map();
  for (const op of ops) {
    if (!op || !ENTIDADES.has(op.entidad)) continue;
    const datos = op.payload;
    if (!datos || typeof datos !== 'object') continue;
    const id = op.entidad === 'config' ? 'config' : datos.id;
    if (!id) continue;
    const v = { clave: op.entidad + ':' + id, entidad: op.entidad, id: String(id),
                datos, act: String(datos.act || '') };
    const previo = porClave.get(v.clave);
    if (!previo || v.act >= previo.act) porClave.set(v.clave, v);
  }
  const lista = Array.from(porClave.values());
  if (!lista.length) return propios;

  const [previos] = await pool.query(
    'SELECT clave, act FROM registros WHERE clave IN (?)', [lista.map(v => v.clave)]);
  const mapa = new Map(previos.map(p => [p.clave, p.act || '']));

  const base = await reservar(lista.length);
  const ahora = new Date();
  const nuevas = [];      // versiones que ganan y se escriben
  const obsoletas = [];   // versiones viejas: solo se les renueva el número

  lista.forEach((v, i) => {
    const seq = base + i;
    const actPrevio = mapa.get(v.clave);
    if (actPrevio && v.act && actPrevio > v.act) {
      // El servidor ya tiene algo más nuevo. No se pisa, pero se le sube el
      // número para que la versión buena vuelva a bajar a todos, incluido
      // quien acaba de mandar la vieja.
      obsoletas.push({ clave: v.clave, seq });
    } else {
      nuevas.push([v.clave, v.entidad, v.id, JSON.stringify(v.datos), v.act, seq, sede || null, ahora]);
      propios.add(seq);   // no se le devuelve a quien acaba de mandarlo
    }
  });

  try {
    if (nuevas.length) {
      await pool.query(
        `INSERT INTO registros (clave, entidad, id_reg, datos, act, seq, sede, ts)
         VALUES ?
         ON DUPLICATE KEY UPDATE
           datos = VALUES(datos), act = VALUES(act),
           sede  = VALUES(sede),  seq = VALUES(seq), ts = VALUES(ts)`,
        [nuevas]);
    }
    if (obsoletas.length) {
      // Un CASE deja esto en una sola sentencia sin importar cuántas sean.
      const casos = obsoletas.map(() => 'WHEN ? THEN ?').join(' ');
      const args = [];
      obsoletas.forEach(o => { args.push(o.clave, o.seq); });
      await pool.query(
        `UPDATE registros SET ts = ?, seq = CASE clave ${casos} END WHERE clave IN (?)`,
        [ahora, ...args, obsoletas.map(o => o.clave)]);
    }
  } finally { liberar(base, lista.length); }
  return propios;
}

/* ── App ────────────────────────────────────────────────────────────────── */
const app = express();
app.set('trust proxy', 1);
app.use(compression());
app.use(express.json({ limit: '40mb' }));

app.use((req, res, next) => {
  res.set('Access-Control-Allow-Origin', '*');
  res.set('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  res.set('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  if (req.method === 'OPTIONS') return res.sendStatus(204);
  next();
});

function exigirDB(req, res, next) {
  if (!listo) return res.status(503).json({ ok: false, error: 'base de datos no disponible', diagnostico: errorConexion });
  next();
}
const guardia = fn => (req, res) => fn(req, res).catch(err => {
  console.error('[error]', req.method, req.path, err.message);
  res.status(500).json({ ok: false, error: err.message });
});

/* ── GET /salud ─────────────────────────────────────────────────────────
   `esEsteEquipo` va siempre en falso: el servidor vive en la nube, no en
   ninguna de las tablets.
   ------------------------------------------------------------------- */
app.get(['/salud', '/health'], guardia(async (req, res) => {
  const t0 = Date.now();
  let registros = 0, msBase = null;
  if (listo) {
    try {
      const [r] = await pool.query('SELECT COUNT(*) AS n FROM registros');
      registros = Number(r[0].n);
      msBase = Date.now() - t0;
    } catch (e) {}
  }
  const cuerpo = {
    ok: listo, servicio: 'jhon-parrilla-pos', version: VERSION,
    db: listo ? 'conectada' : 'sin conexión', motor: 'mysql', registros,
    esEsteEquipo: false, hora: new Date().toISOString()
  };
  // Cuánto tarda la base en contestar: sirve para saber si la lentitud está
  // en la base o en el servidor web.
  if (msBase !== null) cuerpo.msBase = msBase;
  if (!listo && errorConexion) cuerpo.diagnostico = errorConexion;
  res.json(cuerpo);
}));

/* ── POST /sync ─────────────────────────────────────────────────────────
   Camino caliente. Sin operaciones que subir, esto es una sola consulta.
   ------------------------------------------------------------------- */
app.post('/sync', exigirDB, guardia(async (req, res) => {
  const { sede, cursor, ops } = req.body || {};
  const lote = Array.isArray(ops) ? ops : [];
  const propios = lote.length ? await aplicarOps(lote, sede) : new Set();

  const desde = Number(cursor) || 0;
  const tope = techo();
  const [filas] = await pool.query(
    tope === Infinity
      ? 'SELECT entidad, datos, seq FROM registros WHERE seq > ? ORDER BY seq LIMIT 500'
      : 'SELECT entidad, datos, seq FROM registros WHERE seq > ? AND seq <= ? ORDER BY seq LIMIT 500',
    tope === Infinity ? [desde] : [desde, tope]);

  const cambios = [];
  filas.forEach(f => {
    if (propios.has(Number(f.seq))) return;
    const datos = leerDatos(f);
    if (datos) cambios.push({ entidad: f.entidad, data: datos });
  });

  res.json({
    ok: true,
    aceptadas: lote.map(o => o && o.opId).filter(Boolean),
    cursor: filas.length ? Number(filas[filas.length - 1].seq) : desde,
    cambios,
    faltan: filas.length === 500
  });
}));

/* ── GET /estado ────────────────────────────────────────────────────── */
app.get('/estado', exigirDB, guardia(async (req, res) => {
  const [filas] = await pool.query('SELECT entidad, datos, seq FROM registros ORDER BY seq');
  const estado = {};
  ENTIDADES.forEach(e => { if (e !== 'config') estado[e] = []; });
  let cursor = 0;
  filas.forEach(f => {
    const seq = Number(f.seq);
    if (seq > cursor) cursor = seq;
    const datos = leerDatos(f);
    if (!datos) return;
    if (f.entidad === 'config') estado.config = datos;
    else if (Array.isArray(estado[f.entidad])) estado[f.entidad].push(datos);
  });
  res.json({ ok: true, estado, cursor, registros: filas.length });
}));

/* ── POST /sembrar ──────────────────────────────────────────────────── */
app.post('/sembrar', exigirDB, guardia(async (req, res) => {
  const { sede, estado, forzar } = req.body || {};
  if (!estado || !estado.config) return res.status(400).json({ ok: false, error: 'faltan datos' });

  const [c] = await pool.query('SELECT COUNT(*) AS n FROM registros');
  const existentes = Number(c[0].n);
  if (existentes > 0 && !forzar) return res.status(409).json({ ok: false, registros: existentes });
  if (existentes > 0 && forzar && !PERMITIR_FORZAR)
    return res.status(403).json({ ok: false, error: 'el servidor está bloqueado contra sobrescrituras (PERMITIR_FORZAR=0)' });

  const filas = [];
  Object.keys(estado).forEach(entidad => {
    if (!ENTIDADES.has(entidad)) return;
    const v = estado[entidad];
    if (entidad === 'config') {
      if (v && typeof v === 'object') filas.push({ entidad, id: 'config', datos: Object.assign({ id: 'config' }, v) });
    } else if (Array.isArray(v)) {
      v.forEach(r => { if (r && r.id) filas.push({ entidad, id: String(r.id), datos: r }); });
    }
  });
  if (!filas.length) return res.status(400).json({ ok: false, error: 'no hay registros para publicar' });

  const base = await reservar(filas.length);
  const ahora = new Date();
  const cx = await pool.getConnection();
  try {
    // Borrar y publicar van juntos: si algo falla a mitad, no queda una base
    // a medio vaciar en pleno servicio.
    await cx.beginTransaction();
    if (existentes > 0) await cx.query('DELETE FROM registros');
    const lotes = [];
    for (let i = 0; i < filas.length; i += 500) lotes.push(filas.slice(i, i + 500));
    let n = 0;
    for (const lote of lotes) {
      await cx.query(
        `INSERT INTO registros (clave, entidad, id_reg, datos, act, seq, sede, ts) VALUES ?
         ON DUPLICATE KEY UPDATE datos=VALUES(datos), act=VALUES(act), seq=VALUES(seq), ts=VALUES(ts)`,
        [lote.map((f, j) => [f.entidad + ':' + f.id, f.entidad, f.id, JSON.stringify(f.datos),
                             String(f.datos.act || ''), base + n + j, sede || null, ahora])]);
      n += lote.length;
    }
    await cx.commit();
  } catch (e) {
    await cx.rollback();
    throw e;
  } finally {
    cx.release();
    liberar(base, filas.length);
  }

  console.log('[sembrar]', filas.length, 'registros publicados');
  res.json({ ok: true, registros: filas.length, cursor: base + filas.length - 1 });
}));

/* ── Respaldos ──────────────────────────────────────────────────────────
   Comprimidos: un volcado del POS es JSON repetitivo y baja como diez veces
   de tamaño. En un plan de 1 GB eso decide cuántas copias caben.
   ------------------------------------------------------------------- */
app.post('/respaldo', exigirDB, guardia(async (req, res) => {
  const { motivo, dump } = req.body || {};
  if (!dump || !dump.datos) return res.status(400).json({ ok: false, error: 'respaldo vacío' });
  const d = new Date();
  const p = n => String(n).padStart(2, '0');
  const nombre = 'respaldo-' + d.getFullYear() + p(d.getMonth() + 1) + p(d.getDate()) +
    '-' + p(d.getHours()) + p(d.getMinutes()) + p(d.getSeconds()) + '-' +
    Math.random().toString(36).slice(2, 6) + '.json';

  const crudo = Buffer.from(JSON.stringify(dump), 'utf8');
  const comprimido = await gzip(crudo, { level: 6 });

  await pool.query(
    `INSERT INTO respaldos (nombre, motivo, generado, usuario, sede, equipo, resumen, dump, bytes)
     VALUES (?,?,?,?,?,?,?,?,?)`,
    [nombre, String(motivo || dump.motivo || 'automático').slice(0, 160),
     String(dump.generado || d.toISOString()).slice(0, 40),
     String(dump.usuario || 'sistema').slice(0, 140),
     dump.sede ? String(dump.sede).slice(0, 60) : null,
     String(dump.equipo || '').slice(0, 140),
     JSON.stringify(dump.resumen || {}), comprimido, crudo.length]);

  const [viejos] = await pool.query(
    'SELECT nombre FROM respaldos ORDER BY generado DESC, nombre DESC LIMIT 500 OFFSET ?', [MAX_RESPALDOS]);
  if (viejos.length) await pool.query('DELETE FROM respaldos WHERE nombre IN (?)', [viejos.map(v => v.nombre)]);

  res.json({ ok: true, archivo: nombre, bytes: crudo.length, comprimido: comprimido.length });
}));

app.get('/respaldos', exigirDB, guardia(async (req, res) => {
  // Sin la columna `dump`: la lista no necesita cargar los volcados enteros.
  const [filas] = await pool.query(
    `SELECT nombre, motivo, generado, usuario, equipo, resumen, bytes
     FROM respaldos ORDER BY generado DESC, nombre DESC LIMIT ?`, [MAX_RESPALDOS]);
  res.json({
    ok: true,
    archivos: filas.map(f => {
      let resumen = {};
      try { resumen = JSON.parse(f.resumen || '{}'); } catch (e) {}
      return { archivo: f.nombre, id: f.nombre, fecha: f.generado, motivo: f.motivo,
               usuario: f.usuario, equipo: f.equipo, bytes: f.bytes, resumen };
    })
  });
}));

app.get('/respaldo/:nombre', exigirDB, guardia(async (req, res) => {
  const [filas] = await pool.query('SELECT dump FROM respaldos WHERE nombre = ?', [req.params.nombre]);
  if (!filas.length) return res.status(404).json({ ok: false, error: 'no existe' });
  const crudo = await gunzip(filas[0].dump);
  res.type('application/json').send(crudo);
}));

/* ── La aplicación ──────────────────────────────────────────────────────
   Se sirve sin caché para que "Buscar actualización" traiga siempre la
   última versión que haya en el repositorio.
   ------------------------------------------------------------------- */
const PUB = path.join(__dirname, 'public');
app.get('/', (req, res) => {
  res.set('Cache-Control', 'no-cache, must-revalidate');
  res.sendFile(path.join(PUB, 'index.html'));
});
app.use(express.static(PUB, { setHeaders: r => r.set('Cache-Control', 'no-cache') }));

app.use((req, res) => res.status(404).json({ ok: false, error: 'ruta no encontrada' }));

/* ── Arranque ───────────────────────────────────────────────────────────
   El servidor web levanta primero y MySQL se conecta detrás: así el
   despliegue no se marca como fallido si la base tarda en responder, y
   /salud puede explicar qué pasa en vez de no contestar nada.
   ------------------------------------------------------------------- */
if (require.main === module) {
  app.listen(PORT, () => {
    console.log('[web] escuchando en el puerto', PORT);
    const fallo = err => {
      const d = err.diagnostico || diagnosticar(err);
      errorConexion = { causa: d.causa, arreglo: d.arreglo, mensajeCrudo: String(err.message || err) };
      console.error('\n──────── LA BASE DE DATOS NO CONECTA ────────');
      console.error('  Qué pasa : ' + d.causa);
      console.error('  Qué hacer: ' + d.arreglo);
      console.error('  MySQL dice: ' + String(err.message || err));
      console.error('  (también lo verás en /salud)');
      console.error('─────────────────────────────────────────────\n');
    };
    conectar().catch(err => {
      fallo(err);
      setInterval(() => { if (!listo) conectar().catch(fallo); }, 20000);
    });
  });
}

process.on('unhandledRejection', err => console.error('[promesa]', err && err.message));
process.on('uncaughtException', err => console.error('[excepción]', err && err.message));

module.exports = { app, conectar, revisarURL, diagnosticar };

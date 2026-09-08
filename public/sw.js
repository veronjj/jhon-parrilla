/* Service worker minimo: la aplicacion intenta registrarlo para poder
   instalarse como app. No guarda copias del HTML a proposito, para que
   nadie se quede trabajando con una version vieja. */
self.addEventListener('install', e => self.skipWaiting());
self.addEventListener('activate', e => e.waitUntil(self.clients.claim()));
self.addEventListener('fetch', e => { /* red directa */ });

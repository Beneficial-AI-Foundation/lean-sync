// Development and test server: serves the static site, nothing else. NOT part of the shipped app;
// binds to 127.0.0.1 only. The app needs no server endpoint (devices connect to each other over
// WebRTC after the user pairs them), so any static web server can host build/site.
//   node dev/serve.mjs [--port 8000] [--root build/site] [--base /some/path/]
// `base`: serve the site under that path prefix (the tests check that the app works from a
// sub-path). Responses carry `Cache-Control: no-store` (file names are not versioned).
import { createServer } from 'node:http';
import { readFile, stat } from 'node:fs/promises';
import { join, dirname, normalize, extname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const HOST = '127.0.0.1';
const TYPES = { '.html': 'text/html; charset=utf-8', '.mjs': 'text/javascript', '.js': 'text/javascript',
  '.css': 'text/css', '.wasm': 'application/wasm', '.json': 'application/json', '.svg': 'image/svg+xml', '.md': 'text/plain; charset=utf-8' };

export async function startServer({ port = 0, root, base = '/' } = {}) {
  root = resolve(root ?? join(dirname(fileURLToPath(import.meta.url)), '../build/site'));
  if (!base.startsWith('/') || !base.endsWith('/')) throw new Error('base must start and end with /');
  const stats = { requests: 0, notFound: [] };
  const server = createServer(async (req, res) => {
    stats.requests++;
    try {
      const url = new URL(req.url, 'http://x');
      if (req.method !== 'GET' && req.method !== 'HEAD') { res.writeHead(405); return res.end(); }
      if (!url.pathname.startsWith(base)) throw new Error('outside base');
      let rel = normalize(decodeURIComponent(url.pathname.slice(base.length))).replace(/^\/+/, '');
      if (rel === '' || rel === '.' || rel.endsWith('/')) rel = join(rel === '.' ? '' : rel, 'index.html');
      const file = join(root, rel);
      if (!file.startsWith(root + '/') || !(await stat(file)).isFile()) throw new Error('not found');
      res.writeHead(200, { 'content-type': TYPES[extname(rel)] ?? 'application/octet-stream', 'cache-control': 'no-store' });
      res.end(req.method === 'HEAD' ? undefined : await readFile(file));
    } catch {
      stats.notFound.push(req.url);
      if (!res.headersSent) res.writeHead(404);
      res.end();
    }
  });
  await new Promise((res) => server.listen(port, HOST, res));
  const p = server.address().port;
  return { server, port: p, url: `http://${HOST}:${p}${base.replace(/\/$/, '')}`, stats,
    close: () => new Promise((res) => { server.closeAllConnections?.(); server.close(res); }) };
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const args = process.argv.slice(2);
  const get = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
  const s = await startServer({ port: Number(get('--port', 8000)), root: get('--root'), base: get('--base', '/') });
  console.log(`serving ${s.url}/ ; Ctrl-C to stop`);
}

// Probe (throwaway): does the built site (build/site) run from a sub-path of a plain static server,
// with no /relay endpoint, and with a wrong MIME type for the .wasm? Prints phase and transport log.
//   node test/e2e/probe-static.mjs
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { join, extname, normalize } from 'node:path';
import { launch, hasBrowser } from './driver.mjs';
import { cleanupAll, reportCleanup } from '../proc.mjs';

const root = join(import.meta.dirname, '../../build/site');
const BASE = '/some/sub/path/';
let wasmType = 'application/wasm';
const TYPES = { '.html': 'text/html', '.mjs': 'text/javascript', '.css': 'text/css', '.wasm': null };
const server = createServer(async (req, res) => {
  const u = new URL(req.url, 'http://x');
  if (!u.pathname.startsWith(BASE)) { res.writeHead(404); return res.end(); }
  let rel = normalize(u.pathname.slice(BASE.length)); if (rel === '.' || rel === '') rel = 'index.html';
  try {
    const body = await readFile(join(root, rel));
    res.writeHead(200, { 'content-type': TYPES[extname(rel)] ?? wasmType });
    res.end(body);
  } catch { res.writeHead(404); res.end(); }
});
await new Promise((r) => server.listen(0, '127.0.0.1', r));
const url = `http://127.0.0.1:${server.address().port}${BASE}?device=probe`;
for (const kind of ['chromium', 'firefox'].filter(hasBrowser)) {
  for (const t of ['application/wasm', 'application/octet-stream']) {
    wasmType = t;
    const b = await launch(kind);
    try {
      const p = await b.newPage(url);
      let phase = null;
      for (let i = 0; i < 100 && phase !== 'running'; i++) { phase = await p.eval('window.leansync?.phase ?? null').catch(() => null); await new Promise((r) => setTimeout(r, 100)); }
      await new Promise((r) => setTimeout(r, 2500));
      const log = await p.eval('(window.leansync?.log ?? []).filter((l) => /transport/.test(String(l.msg ?? l))).slice(-4)').catch((e) => e.message);
      console.log(`${kind} wasm served as ${t}: phase=${phase}; transport log: ${JSON.stringify(log)}`);
    } finally { await b.close(); }
  }
}
server.close();
reportCleanup(await cleanupAll());

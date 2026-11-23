// Static server for build/site plus a /report endpoint used by headless browser checks:
// the page (opened with ?report=1) POSTs its input and output; we compare the output with
// the native build of the same Lean code and print PASS/FAIL.
// usage: node wasm/serve.mjs [port]
import { createServer } from 'node:http';
import { readFile, writeFile, mkdtemp } from 'node:fs/promises';
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join, dirname, extname, normalize } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const site = join(root, 'build', 'site');
const native = join(root, '.lake/build/bin/wasm-demo-native');
const port = Number(process.argv[2] ?? 8000);
const types = { '.html': 'text/html', '.mjs': 'text/javascript', '.js': 'text/javascript', '.wasm': 'application/wasm' };

const EXPECTED_PLATFORM = {
  wasm32: 'numBits=32 usizeMax=4294967295 ',
  wasm64: 'numBits=64 usizeMax=18446744073709551615 ',
};

function dropPlatformLine(s) { return s.replace(/\nnumBits=[^\n]*/, ''); }

createServer(async (req, res) => {
  if (req.method === 'POST' && req.url === '/report') {
    // Any failure here must produce a response and a FAIL line, never kill the server.
    let r = {};
    try {
      let body = '';
      for await (const c of req) body += c;
      r = JSON.parse(body);
      let verdict = 'FAIL';
      const platform = r.platform ?? '';
      if (!r.ok) {
        verdict = 'FAIL (page reported an error)';
      } else if (!platform.startsWith(EXPECTED_PLATFORM[r.arch] ?? '\0')) {
        verdict = `FAIL (platform line does not match ${r.arch})`;
      } else {
        const f = join(await mkdtemp(join(tmpdir(), 'lean-wasm-')), 'in');
        await writeFile(f, Buffer.from(r.inputB64, 'base64'));
        const want = execFileSync(native, [f], { maxBuffer: 1 << 26 }).toString('latin1');
        const got = Buffer.from(r.outputB64, 'base64').toString('latin1');
        verdict = dropPlatformLine(got) === dropPlatformLine(want) ? 'PASS' : 'FAIL (output differs from native)';
      }
      console.log(`REPORT ${verdict} run=${r.run ?? '-'} arch=${r.arch} ua="${r.userAgent}" status="${r.status}"` +
        (platform ? ` platform="${platform}"` : '') + (r.error ? ` error="${r.error}"` : ''));
      res.end('ok');
    } catch (e) {
      console.log(`REPORT FAIL (server error: ${String(e).split('\n')[0]}) run=${r.run ?? '-'} arch=${r.arch ?? '-'}`);
      res.writeHead(500); res.end('error');
    }
    return;
  }
  const path = normalize(decodeURIComponent(new URL(req.url, 'http://x').pathname)).replace(/^\/+/, '') || 'index.html';
  try {
    const data = await readFile(join(site, path));
    res.writeHead(200, { 'content-type': types[extname(path)] ?? 'application/octet-stream' });
    res.end(data);
  } catch {
    res.writeHead(404); res.end('not found');
  }
}).on('error', (e) => { console.error(`server error: ${e.message}`); process.exit(1); })
  .listen(port, '127.0.0.1', () => console.log(`serving ${site} on http://127.0.0.1:${port}/`));

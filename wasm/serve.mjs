// Static server for build/site plus a /report endpoint used by headless browser checks:
// the page (opened with ?report=1) POSTs its input, output and displayed text; we check the
// module is 64-bit, compare the output byte for byte with the native build of the same Lean
// code, check what the page displayed, and print PASS/FAIL.
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

// The build is wasm64-only: a module reporting anything else is a wrong artifact.
const EXPECTED_PLATFORM = 'numBits=64 usizeMax=18446744073709551615 ';

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
      } else {
        const input = Buffer.from(r.inputB64, 'base64');
        const f = join(await mkdtemp(join(tmpdir(), 'lean-wasm-')), 'in');
        await writeFile(f, input);
        const want = execFileSync(native, [f], { maxBuffer: 1 << 26 });
        const got = Buffer.from(r.outputB64, 'base64');
        // Normal results are a text report + the reversed input; probe results are text only.
        const isProbe = !want.subarray(0, 6).equals(Buffer.from('bytes='));
        const wantDisplay = (isProbe ? want : want.subarray(0, want.length - input.length)).toString('utf8');
        if (!isProbe && !platform.startsWith(EXPECTED_PLATFORM)) {
          verdict = 'FAIL (platform line is not 64-bit)';
        } else if (!got.equals(want)) {
          verdict = 'FAIL (output differs from native)';
        } else if (r.display !== wantDisplay) {
          verdict = 'FAIL (page displayed the result incorrectly)';
        } else {
          verdict = 'PASS';
        }
      }
      console.log(`REPORT ${verdict} run=${r.run ?? '-'} ua="${r.userAgent}" status="${r.status}"` +
        (platform ? ` platform="${platform}"` : '') + (r.error ? ` error="${r.error}"` : ''));
      res.end('ok');
    } catch (e) {
      console.log(`REPORT FAIL (server error: ${String(e).split('\n')[0]}) run=${r.run ?? '-'}`);
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

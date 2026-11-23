// Stage-1 browser smoke: serve the repo (127.0.0.1 only), open test/browser-smoke.html in each
// headless browser found (Chromium, Firefox, Firefox ESR) with a fresh profile and a per-run path,
// and check each run's report against the path assigned to that run.
// usage: node test/browser-smoke.mjs   (after scripts/wasm/build.sh)
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { execFileSync } from 'node:child_process';
import { spawnTracked, killGroup, tempDir, removeDir, cleanupAll, reportCleanup } from './proc.mjs';
import { join, dirname, normalize, extname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { randomBytes } from 'node:crypto';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const TYPES = { '.html': 'text/html', '.mjs': 'text/javascript', '.js': 'text/javascript', '.wasm': 'application/wasm' };
const ALLOWED = ['app/', 'build/sync/', 'test/'];
const waiters = new Map();
const server = createServer(async (req, res) => {
  try {
    const url = new URL(req.url, 'http://x');
    if (req.method === 'POST' && url.pathname === '/report') {
      const chunks = []; for await (const c of req) chunks.push(c);
      let body = null; try { body = JSON.parse(Buffer.concat(chunks).toString('utf8')); } catch {}
      res.end('ok');
      if (body && typeof body === 'object' && waiters.has(body.run)) waiters.get(body.run)(body);
      return;
    }
    const rel = normalize(decodeURIComponent(url.pathname)).replace(/^\/+/, '');
    if (!ALLOWED.some((p) => rel.startsWith(p)) || rel.includes('..')) { res.writeHead(404); return res.end(); }
    const data = await readFile(join(root, rel));
    res.writeHead(200, { 'content-type': TYPES[extname(rel)] ?? 'application/octet-stream' });
    res.end(data);
  } catch { res.writeHead(404); res.end(); }
});
await new Promise((r) => server.listen(0, '127.0.0.1', r));
const port = server.address().port;

const has = (c) => { try { execFileSync('sh', ['-c', `command -v ${c}`]); return true; } catch { return false; } };
const browsers = ['chromium', 'firefox', 'firefox-esr'].filter(has);
let fail = 0;
for (const b of browsers) {
  const run = randomBytes(6).toString('hex');
  const path = `dir/π-${run}.txt`;
  const profile = tempDir(`smoke-${b}-`);
  const url = `http://127.0.0.1:${port}/test/browser-smoke.html?run=${run}&path=${encodeURIComponent(path)}`;
  const args = b === 'chromium'
    ? ['--headless=new', '--no-sandbox', `--user-data-dir=${profile}`, '--no-first-run', url]
    : ['--headless', '--no-remote', '--profile', profile, url];
  const version = execFileSync(b, ['--version']).toString().trim();
  const proc = spawnTracked(b, args, { stdio: 'ignore' });
  const body = await Promise.race([
    new Promise((r) => waiters.set(run, r)),
    new Promise((r) => setTimeout(() => r({ error: 'timeout (30 s)' }), 30000)),
  ]);
  await killGroup(proc.pid);          // the whole process group, awaited
  removeDir(profile);
  const ok = !body.error && Array.isArray(body.files) && body.files.length === 1 && body.files[0] === path;
  if (!ok) fail++;
  console.log(`${ok ? 'OK  ' : 'FAIL'} ${version}: ${ok ? `startup ${body.startupMs.toFixed(0)} ms` : JSON.stringify(body)}`);
}
server.close();
if (!browsers.length) { console.log('no browsers found'); fail++; }
const c = await cleanupAll();
reportCleanup(c);
process.exit(fail ? 1 : c.ok ? 0 : 2);

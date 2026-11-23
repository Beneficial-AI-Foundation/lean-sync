// Run the end-to-end scenarios in headless browsers (needs scripts/build-site.sh first).
//   node test/e2e/run.mjs [--only name,name] [--browsers chromium,firefox,firefox-esr] [--list]
// Starts the dev server (127.0.0.1, random port) and stops it at the end. Prints, per scenario and
// configuration, the browsers and versions used and the result.
import { startServer } from '../../dev/serve.mjs';
import { openDevice, versionOf } from './lib.mjs';
import { hasBrowser } from './driver.mjs';
import { scenarios } from './scenarios.mjs';
import { cleanupAll, reportCleanup } from '../proc.mjs';

const args = process.argv.slice(2);
const opt = (n) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : null; };
const only = opt('--only')?.split(',');
const allowed = new Set((opt('--browsers') ?? 'chromium,firefox,firefox-esr').split(',').filter(hasBrowser));
const TIMEOUT = Number(opt('--timeout') ?? 240000);

const todo = [];
for (const s of scenarios) {
  if (only && !only.includes(s.name)) continue;
  for (const kinds of s.kinds) if (kinds.every((k) => allowed.has(k))) todo.push({ s, kinds });
}
if (args.includes('--list')) { for (const t of todo) console.log(t.s.name, t.kinds.join('+')); process.exit(0); }

const server = await startServer({ port: 0, admin: true });
console.log(`dev server ${server.url}; ${todo.length} runs`);
const results = [];
let n = 0;
for (const { s, kinds } of todo) {
  const id = `${Date.now().toString(36)}${(n++).toString(36)}`;
  const devs = [];
  const ctx = {
    server, id, room: `room-${id}`, notes: [], cleanup: [],
    note: (m) => ctx.notes.push(m),
    async open(kind, label, o = {}) { const d = await openDevice(server, kind, label, { room: ctx.room, ...o }); devs.push(d); return d; },
  };
  const label = kinds.map((k, i) => `${String.fromCharCode(65 + i)}=${versionOf(k)}`).join(', ');
  const t0 = Date.now();
  let err = null;
  try {
    await Promise.race([s.run(ctx, kinds), new Promise((_, rej) => setTimeout(() => rej(new Error(`scenario timeout ${TIMEOUT} ms`)), TIMEOUT))]);
  } catch (e) { err = e; }
  for (const d of devs) { await Promise.race([d.close(), new Promise((r) => setTimeout(r, 8000))]).catch(() => {}); await d.kill().catch(() => {}); d.destroy(); }
  for (const c of ctx.cleanup) await c().catch(() => {});
  const secs = ((Date.now() - t0) / 1000).toFixed(1);
  results.push({ name: s.name, label, ok: !err, secs, notes: ctx.notes, err });
  console.log(`${err ? 'FAIL' : 'PASS'} ${s.name} [${kinds.join('+')}] ${secs}s`);
  console.log(`     ${label}`);
  for (const m of ctx.notes) console.log(`     note: ${m}`);
  if (err) console.log(`     ${String(err.stack ?? err).split('\n').slice(0, 30).join('\n     ')}`);
}
await server.close();
const failed = results.filter((r) => !r.ok);
console.log(`\n${results.length - failed.length}/${results.length} passed`);
// Hygiene is checked and reported separately from the results: exit 1 for test failures, 2 for a
// cleanup failure alone (so neither can hide the other).
const c = await cleanupAll();
reportCleanup(c);
process.exit(failed.length ? 1 : c.ok ? 0 : 2);

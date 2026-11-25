// Run the end-to-end scenarios in headless browsers (needs scripts/build-site.sh first).
//   node test/e2e/run.mjs [--only name,name] [--browsers chromium,firefox,firefox-esr] [--list] [--host-network]
// Starts the static dev server (127.0.0.1, random port) and stops it at the end. Prints, per
// scenario and configuration, the browsers and versions used and the result.
//
// Network. WebRTC needs a network interface other than loopback: with only `lo`, neither browser
// gathers any candidate (docs/net-design.md §1.8). So the runner re-executes itself inside a new
// user + network namespace (`unshare -rn`, no root needed) holding `lo` and a dummy interface with
// a default route. That also keeps the tests off the real network and the internet. If user
// namespaces are not available, it falls back to the host's network when the host has a
// non-loopback IPv4 address (`--host-network` forces that), and otherwise stops with a message.
import { spawnSync } from 'node:child_process';
import { networkInterfaces } from 'node:os';

const args = process.argv.slice(2);
if (!process.env.LEANSYNC_E2E_NET && !args.includes('--list')) {
  const setup = 'ip link set lo up && ip link add d0 type dummy && ip addr add 10.99.0.1/24 dev d0 && ip link set d0 up && ip route add default dev d0';
  const canNs = !args.includes('--host-network') && spawnSync('unshare', ['-rn', 'sh', '-c', setup], { stdio: 'ignore' }).status === 0;
  if (canNs) {
    const r = spawnSync('unshare', ['-rn', 'sh', '-c', `${setup} && exec "$@"`, 'sh', process.execPath, ...process.argv.slice(1)],
      { stdio: 'inherit', env: { ...process.env, LEANSYNC_E2E_NET: 'namespace (lo + dummy 10.99.0.1)' } });
    process.exit(r.status ?? 1);
  }
  const hostIf = Object.entries(networkInterfaces()).flatMap(([n, as]) => as.filter((a) => !a.internal && a.family === 'IPv4').map((a) => `${n} ${a.address}`));
  if (!hostIf.length) {
    console.error('The end-to-end tests need a network interface for WebRTC, and none is usable:\n' +
      '  - `unshare -rn` (unprivileged user and network namespaces) failed, so a private dummy interface cannot be made;\n' +
      '  - the host has no non-loopback IPv4 address.\n' +
      'Enable unprivileged user namespaces (sysctl kernel.unprivileged_userns_clone=1) or run on a machine with a network interface.');
    process.exit(1);
  }
  process.env.LEANSYNC_E2E_NET = `host network (${hostIf.join(', ')})`;
}

const { startServer } = await import('../../dev/serve.mjs');
const { openDevice, versionOf } = await import('./lib.mjs');
const { hasBrowser } = await import('./driver.mjs');
const { scenarios } = await import('./scenarios.mjs');
const { cleanupAll, reportCleanup } = await import('../proc.mjs');

const opt = (n) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : null; };
const only = opt('--only')?.split(',');
const allowed = new Set((opt('--browsers') ?? 'chromium,firefox,firefox-esr').split(',').filter(hasBrowser));
const TIMEOUT = Number(opt('--timeout') ?? 300000);

const todo = [];
for (const s of scenarios) {
  if (only && !only.includes(s.name)) continue;
  for (const kinds of s.kinds) if (kinds.every((k) => allowed.has(k))) todo.push({ s, kinds });
}
if (args.includes('--list')) { for (const t of todo) console.log(t.s.name, t.kinds.join('+')); process.exit(0); }
if (only && !todo.length) { console.error(`no run matches --only ${only.join(',')} with browsers ${[...allowed].join(',')}`); process.exit(3); }   // 3: nothing ran (not a pass, not a failure)

const server = await startServer({ port: 0 });
console.log(`dev server ${server.url}; network: ${process.env.LEANSYNC_E2E_NET}; ${todo.length} runs`);
const results = [];
let n = 0;
for (const { s, kinds } of todo) {
  const id = `${Date.now().toString(36)}${(n++).toString(36)}`;
  const devs = [];
  const ctx = {
    server, id, notes: [], cleanup: [],
    note: (m) => ctx.notes.push(m),
    async open(kind, label, o = {}) { const d = await openDevice(o.server ?? server, kind, label, o); devs.push(d); return d; },
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

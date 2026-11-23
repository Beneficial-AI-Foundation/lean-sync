// Process and temporary-directory hygiene for every test that starts browsers.
//
// - All temporary profiles live under ONE run directory: $LEANSYNC_TEST_DIR if set (scripts/test-app.sh
//   sets it and removes it at the end), else a fresh `leansync-test-*` under $TMPDIR (removed by
//   cleanupAll()).
// - Every browser is spawned in its own process group (detached), and killed as a group (SIGKILL),
//   so helper processes (Chromium's zygote/GPU/renderers, Firefox content processes) die too.
//   A group is forgotten only once no process of it is left.
// - On exit, SIGINT, SIGTERM and uncaught errors, every group still alive is killed.
// - cleanupAll() kills what is left, removes the run directory (with retries: a browser's last
//   writes can race the removal), and REPORTS leftovers instead of throwing, so a cleanup problem
//   neither fails a passing test nor masks a failing one; runners report it separately.
import { spawn } from 'node:child_process';
import { mkdtempSync, rmSync, existsSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const external = process.env.LEANSYNC_TEST_DIR;
let RUN = null;
export function runDir() {
  if (RUN) return RUN;
  if (external) { mkdirSync(external, { recursive: true }); RUN = mkdtempSync(join(external, 'run-')); }
  else RUN = mkdtempSync(join(process.env.TMPDIR || tmpdir(), 'leansync-test-'));
  return RUN;
}
export const tempDir = (prefix) => mkdtempSync(join(runDir(), prefix));

const groups = new Set();
const alive = (pid) => { try { process.kill(-pid, 0); return true; } catch { return false; } };

export function spawnTracked(cmd, args, opts = {}) {
  const child = spawn(cmd, args, { ...opts, detached: true });
  groups.add(child.pid);
  return child;
}
export async function killGroup(pid, ms = 15000) {
  try { process.kill(-pid, 'SIGKILL'); } catch {}
  const t0 = Date.now();
  while (alive(pid) && Date.now() - t0 < ms) await new Promise((r) => setTimeout(r, 50));
  if (!alive(pid)) groups.delete(pid);
  return !alive(pid);
}
export function removeDir(dir) {
  try { rmSync(dir, { recursive: true, force: true, maxRetries: 20, retryDelay: 100 }); } catch {}
  return !existsSync(dir);
}
export const leftGroups = () => [...groups].filter(alive);

export async function cleanupAll() {
  for (const pid of [...groups]) await killGroup(pid);
  const procs = leftGroups();
  const dirRemoved = RUN ? removeDir(RUN) : true;
  return { procs, dir: RUN, dirRemoved, ok: procs.length === 0 && dirRemoved };
}
export function reportCleanup(c) {
  if (c.ok) console.log(`hygiene: no browser process left; ${c.dir ? `${c.dir} removed` : 'no temporary directory'}`);
  else console.log(`CLEANUP FAILED: ${c.procs.length} process group(s) still alive ${JSON.stringify(c.procs)}; run directory ${c.dir} ${c.dirRemoved ? 'removed' : 'NOT removed'}`);
}

function killAllSync() { for (const pid of groups) { try { process.kill(-pid, 'SIGKILL'); } catch {} } }
process.on('exit', () => { killAllSync(); if (RUN && !external) { try { rmSync(RUN, { recursive: true, force: true, maxRetries: 5, retryDelay: 50 }); } catch {} } });
for (const sig of ['SIGINT', 'SIGTERM', 'SIGHUP']) process.on(sig, () => { killAllSync(); process.exit(130); });
process.on('uncaughtException', (e) => { console.error(e); killAllSync(); process.exit(1); });
process.on('unhandledRejection', (e) => { console.error(e); killAllSync(); process.exit(1); });

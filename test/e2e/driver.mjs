// Minimal headless-browser driver for the end-to-end tests, on Node built-ins only:
// Chromium over the Chrome DevTools Protocol, Firefox over WebDriver BiDi (Node's global WebSocket).
//
//   const b = await launch('chromium' | 'firefox' | 'firefox-esr', { profile, prefs });
//   const p = await b.newPage(url);          // a tab
//   await p.eval('expr')                     // evaluates `expr` (awaited), returns JSON-decoded value
//   await p.reload(); await p.close(); await b.close();  // b.kill() = SIGKILL (crash)
// Each browser is a separate process with its own profile directory (= its own storage).
import { spawn, execFileSync } from 'node:child_process';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { createServer } from 'node:net';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

export const browserVersion = (bin) => execFileSync(bin, ['--version']).toString().trim();
export function hasBrowser(bin) { try { execFileSync('sh', ['-c', `command -v ${bin}`]); return true; } catch { return false; } }

const freePort = () => new Promise((res) => { const s = createServer(); s.listen(0, '127.0.0.1', () => { const p = s.address().port; s.close(() => res(p)); }); });

function rpc(ws, onEvent) {
  let id = 0; const pend = new Map();
  ws.addEventListener('message', (m) => {
    const d = JSON.parse(m.data);
    if (d.id != null && pend.has(d.id)) {
      const { res, rej } = pend.get(d.id); pend.delete(d.id);
      if (d.error) rej(new Error(typeof d.error === 'string' ? `${d.error}: ${d.message}` : JSON.stringify(d.error))); else res(d.result);
    } else onEvent?.(d);
  });
  ws.addEventListener('close', () => { for (const { rej } of pend.values()) rej(new Error('browser connection closed')); pend.clear(); });
  return (method, params = {}, extra = {}) => new Promise((res, rej) => {
    const i = ++id; pend.set(i, { res, rej });
    ws.send(JSON.stringify({ id: i, method, params, ...extra }));
  });
}

function waitLine(proc, re, ms = 20000) {
  return new Promise((res, rej) => {
    let buf = '';
    const t = setTimeout(() => rej(new Error(`browser did not print ${re} within ${ms} ms:\n${buf.slice(-2000)}`)), ms);
    const on = (d) => { buf += d; const m = buf.match(re); if (m) { clearTimeout(t); res(m); } };
    proc.stderr.on('data', on); proc.stdout.on('data', on);
    proc.once('exit', (c) => { clearTimeout(t); rej(new Error(`browser exited (${c}) before ready:\n${buf.slice(-2000)}`)); });
  });
}

const unwrapJson = (s) => (s === undefined || s === 'undefined' ? undefined : JSON.parse(s));
// Evaluate `expr`, await it, return JSON.stringify of the result (strings cross both protocols cleanly).
const wrap = (expr) => `(async () => { const __v = await (${expr}); return __v === undefined ? 'undefined' : JSON.stringify(__v); })()`;

export async function launch(kind, { profile, prefs = {}, keepProfile = false } = {}) {
  const dir = profile ?? mkdtempSync(join(tmpdir(), `e2e-${kind}-`));
  let proc, send, close;
  if (kind === 'chromium') {
    proc = spawn('chromium', ['--headless=new', '--no-sandbox', `--user-data-dir=${dir}`, '--no-first-run',
      '--no-default-browser-check', '--remote-debugging-port=0', '--remote-allow-origins=*', 'about:blank'],
    { stdio: ['ignore', 'pipe', 'pipe'] });
    const [, wsUrl] = await waitLine(proc, /DevTools listening on (ws:\/\/\S+)/);
    const ws = new WebSocket(wsUrl);
    await new Promise((r, j) => { ws.onopen = r; ws.onerror = j; });
    send = rpc(ws); close = () => ws.close();
  } else {
    // Firefox: user.js prefs (quota limits etc.) are read at start-up.
    const lines = Object.entries({ 'browser.shell.checkDefaultBrowser': false, 'datareporting.policy.dataSubmissionEnabled': false, ...prefs })
      .map(([k, v]) => `user_pref(${JSON.stringify(k)}, ${JSON.stringify(v)});`);
    writeFileSync(join(dir, 'user.js'), lines.join('\n') + '\n');
    const port = await freePort();
    proc = spawn(kind, ['--headless', '--no-remote', '--profile', dir, `--remote-debugging-port=${port}`, 'about:blank'],
      { stdio: ['ignore', 'pipe', 'pipe'] });
    await waitLine(proc, /WebDriver BiDi listening on ws:\/\//);
    const ws = new WebSocket(`ws://127.0.0.1:${port}/session`);
    await new Promise((r, j) => { ws.onopen = r; ws.onerror = j; });
    send = rpc(ws);
    await send('session.new', { capabilities: { alwaysMatch: { acceptInsecureCerts: true, unhandledPromptBehavior: { default: 'accept' } } } });
    close = () => ws.close();
  }
  const exited = new Promise((r) => proc.once('exit', r));

  async function newPage(url) {
    if (kind === 'chromium') {
      const { targetId } = await send('Target.createTarget', { url: 'about:blank' });
      const { sessionId } = await send('Target.attachToTarget', { targetId, flatten: true });
      const s = (m, p) => send(m, p, { sessionId });
      await s('Page.enable');
      await s('Runtime.enable');
      const page = {
        targetId, sessionId,
        async eval(expr) {
          const r = await s('Runtime.evaluate', { expression: wrap(expr), awaitPromise: true, returnByValue: true });
          if (r.exceptionDetails) throw new Error(`page exception: ${r.exceptionDetails.exception?.description ?? r.exceptionDetails.text}`);
          return unwrapJson(r.result.value);
        },
        async navigate(u) { await s('Page.navigate', { url: u }); await waitReady(page); },
        async reload() { await s('Page.reload', {}); await new Promise((r) => setTimeout(r, 200)); await waitReady(page); },
        close: () => send('Target.closeTarget', { targetId }),
        cdp: s,
      };
      await page.navigate(url);
      return page;
    }
    const { context } = await send('browsingContext.create', { type: 'tab' });
    const page = {
      context,
      async eval(expr) {
        const r = await send('script.evaluate', { expression: wrap(expr), target: { context }, awaitPromise: true, resultOwnership: 'none' });
        if (r.type === 'exception') throw new Error(`page exception: ${r.exceptionDetails?.text}`);
        return unwrapJson(r.result.value);
      },
      async navigate(u) { await send('browsingContext.navigate', { context, url: u, wait: 'complete' }); },
      async reload() { await send('browsingContext.reload', { context, wait: 'complete' }); },
      close: () => send('browsingContext.close', { context }),
    };
    await page.navigate(url);
    return page;
  }
  async function waitReady(page) {
    for (let i = 0; i < 200; i++) {
      try { if ((await page.eval('document.readyState')) === 'complete') return; } catch {}
      await new Promise((r) => setTimeout(r, 50));
    }
    throw new Error('page did not load');
  }
  return {
    kind, profile: dir, newPage, send,
    async close() { try { close(); } catch {} proc.kill('SIGTERM'); await Promise.race([exited, new Promise((r) => setTimeout(r, 5000))]); proc.kill('SIGKILL'); await exited; if (!keepProfile && !profile) rmSync(dir, { recursive: true, force: true }); },
    async kill() { try { close(); } catch {} proc.kill('SIGKILL'); await exited; },
  };
}

// Development and test server. NOT part of the shipped app; binds to 127.0.0.1 only.
//   node dev/serve.mjs [--port 8000] [--root build/site]
// Serves the static site and runs the test transport: a WebSocket relay that links devices
// (browser profiles) in the same room, plus an admin HTTP API used by the end-to-end tests to
// shape the topology and inject faults. No dependencies: the WebSocket protocol (RFC 6455) is
// implemented here on node:http / node:net.
//
// Relay protocol, one WebSocket per device, at /relay?room=<room>&label=<label> (only from pages of
// this server's origin; without `room`, a random room fixed at start-up):
//   server -> client (text JSON): {op:'welcome', id} · {op:'devices', list:[{id,label}]} ·
//                                 {op:'link-up', link, remote:{id,label}} · {op:'link-down', link}
//   client -> server (text JSON): {op:'link', to} (ask for a link; created if allowed and both
//                                 online) · {op:'unlink', link} · {op:'online', value}
//   binary, both ways:            [link:u32 LE][frame]  (frames are the host's, opaque here, except
//                                 for the fault injection below, which reads the frame type byte)
// Admin API (POST JSON, all 127.0.0.1): /admin/topology {room, allow:[[labelA,labelB],...]|null}
//   /admin/cut {room, a, b, afterBytes?}  /admin/corrupt {room, from, to}  (flip a byte in the next
//   BLOB_DATA frame from->to)  /admin/garbage {room, from, to}  (inject a garbage Lean message)
//   GET /admin/state   (only with --admin / {admin:true}; requests with a foreign Origin are refused)
import { createServer } from 'node:http';
import { readFile, stat } from 'node:fs/promises';
import { createHash, randomBytes } from 'node:crypto';
import { join, dirname, normalize, extname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const HOST = '127.0.0.1';
const TYPES = { '.html': 'text/html; charset=utf-8', '.mjs': 'text/javascript', '.js': 'text/javascript',
  '.css': 'text/css', '.wasm': 'application/wasm', '.json': 'application/json', '.svg': 'image/svg+xml' };

export async function startServer({ port = 0, root, admin: adminEnabled = false, anyOrigin = false } = {}) {
  // anyOrigin: tests only (a stand-in for someone else's relay); never with the app's own server.
  const stats = { upgrades: 0 };
  // Loopback is not an access control: any page open in the user's browser can reach 127.0.0.1.
  // So the relay accepts WebSocket upgrades only from pages of this server's own origin (browsers
  // always send Origin on WebSocket handshakes), devices without an explicit room join a random
  // room chosen at start-up, and the admin API (fault injection, used by the tests) is off unless
  // asked for, and refuses any request that carries a foreign Origin.
  const defaultRoom = randomBytes(16).toString('hex');
  let ownOrigins = new Set();
  const originOk = (o) => anyOrigin || (o !== undefined && ownOrigins.has(o));
  root = resolve(root ?? join(dirname(fileURLToPath(import.meta.url)), '../build/site'));
  const rooms = new Map();          // room -> { devices: Map id -> dev, links: Map linkId -> link, allow: Set|null }
  let nextDevice = 1, nextLink = 1;
  const room = (name) => { if (!rooms.has(name)) rooms.set(name, { devices: new Map(), links: new Map(), allow: null, cuts: 0 }); return rooms.get(name); };
  const pairKey = (a, b) => [a, b].sort().join('\u0000');
  const allowed = (r, a, b) => !r.allow || r.allow.has(pairKey(a.label, b.label));
  const log = (...a) => { if (process.env.RELAY_LOG) console.log('[relay]', ...a); };

  // ---------------------------------------------------------------- static files and admin API
  const server = createServer(async (req, res) => {
    try {
      const url = new URL(req.url, 'http://x');
      if (url.pathname.startsWith('/admin/')) {
        if (!adminEnabled || (req.headers.origin !== undefined && !originOk(req.headers.origin))) { res.writeHead(403); return res.end(); }
        return await admin(req, res, url);
      }
      let rel = normalize(decodeURIComponent(url.pathname)).replace(/^\/+/, '');
      if (rel === '' || rel.endsWith('/')) rel += 'index.html';
      const file = join(root, rel);
      if (!file.startsWith(root + '/') || !(await stat(file)).isFile()) throw new Error('not found');
      res.writeHead(200, { 'content-type': TYPES[extname(rel)] ?? 'application/octet-stream', 'cache-control': 'no-store' });
      res.end(await readFile(file));
    } catch { if (!res.headersSent) res.writeHead(404); res.end(); }
  });

  async function admin(req, res, url) {
    let body = {};
    if (req.method === 'POST') {
      const chunks = []; for await (const c of req) chunks.push(c);
      try { body = JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}') ?? {}; } catch { res.writeHead(400); return res.end('bad json'); }
      if (typeof body !== 'object') { res.writeHead(400); return res.end('bad body'); }
    }
    const r = room(body.room ?? url.searchParams.get('room') ?? defaultRoom);
    const byLabel = (l) => [...r.devices.values()].find((d) => d.label === l);
    const linkBetween = (a, b) => [...r.links.values()].find((k) => (k.a === a && k.b === b) || (k.a === b && k.b === a));
    const reply = (o) => { res.writeHead(200, { 'content-type': 'application/json' }); res.end(JSON.stringify(o)); };
    switch (url.pathname) {
      case '/admin/state':
        return reply({ devices: [...r.devices.values()].map((d) => ({ id: d.id, label: d.label, online: d.online })),
          links: [...r.links.values()].map((k) => ({ id: k.id, a: k.a.label, b: k.b.label, bytes: k.bytes })), cuts: r.cuts, upgrades: stats.upgrades });
      case '/admin/topology':
        r.allow = body.allow ? new Set(body.allow.map(([a, b]) => pairKey(a, b))) : null;
        for (const k of [...r.links.values()]) if (!allowed(r, k.a, k.b)) dropLink(r, k, 'topology');
        broadcastDevices(r);
        return reply({ ok: true });
      case '/admin/cut': {
        const a = byLabel(body.a), b = byLabel(body.b); const k = a && b && linkBetween(a, b);
        if (!k) return reply({ ok: false, error: 'no such link' });
        if (body.afterBytes) k.cutAt = k.bytes + body.afterBytes; else dropLink(r, k, 'cut');
        return reply({ ok: true });
      }
      case '/admin/corrupt': case '/admin/garbage': {
        const a = byLabel(body.from), b = byLabel(body.to); const k = a && b && linkBetween(a, b);
        if (!k) return reply({ ok: false, error: 'no such link' });
        if (url.pathname === '/admin/corrupt') { (k.corrupt ??= new Set()).add(a.id); return reply({ ok: true }); }
        // A complete, undecodable Lean message: host frame MSG (1), more=0, then garbage bytes.
        const frame = Buffer.concat([Buffer.from([1, 0]), Buffer.from([1, 2, 99, 1, 2, 3])]);
        sendBin(b, k.id, frame);
        return reply({ ok: true });
      }
      default: res.writeHead(404); res.end();
    }
  }

  // ---------------------------------------------------------------- relay
  function broadcastDevices(r) {
    for (const d of r.devices.values()) {
      const list = [...r.devices.values()].filter((o) => o !== d && o.online && d.online && allowed(r, d, o)).map((o) => ({ id: o.id, label: o.label }));
      sendText(d, { op: 'devices', list });
    }
  }
  function dropLink(r, k, why) {
    if (!r.links.delete(k.id)) return;
    log('link-down', k.id, k.a.label, k.b.label, why);
    for (const d of [k.a, k.b]) { d.links.delete(k.id); sendText(d, { op: 'link-down', link: k.id }); d.sock.resume(); }
  }
  function tryLink(r, a, b) {
    if (!a.online || !b.online || !allowed(r, a, b)) return;
    if ([...r.links.values()].some((k) => (k.a === a && k.b === b) || (k.a === b && k.b === a))) return;
    const k = { id: nextLink++, a, b, bytes: 0 };
    r.links.set(k.id, k); a.links.add(k.id); b.links.add(k.id);
    log('link-up', k.id, a.label, b.label);
    sendText(a, { op: 'link-up', link: k.id, remote: { id: b.id, label: b.label } });
    sendText(b, { op: 'link-up', link: k.id, remote: { id: a.id, label: a.label } });
  }
  function onText(r, d, msg) {
    let m; try { m = JSON.parse(msg); } catch { return; }
    if (m?.op === 'link') { const o = r.devices.get(m.to); if (o) tryLink(r, d, o); }
    else if (m?.op === 'unlink') { const k = r.links.get(m.link); if (k && (k.a === d || k.b === d)) dropLink(r, k, 'unlink'); }
    else if (m?.op === 'online') {
      d.online = !!m.value;
      if (!d.online) for (const id of [...d.links]) dropLink(r, r.links.get(id), 'offline');
      broadcastDevices(r);
    }
  }
  function onBinary(r, d, buf) {
    if (buf.length < 4) return;
    const k = r.links.get(buf.readUInt32LE(0));
    if (!k || (k.a !== d && k.b !== d)) return;             // stale link: drop silently
    const to = k.a === d ? k.b : k.a;
    let frame = buf.subarray(4);
    if (k.corrupt?.has(d.id) && frame[0] === 3 && frame.length > 33) {   // BLOB_DATA: flip one payload byte
      frame = Buffer.from(frame); frame[33] ^= 0xff; k.corrupt.delete(d.id);
    }
    k.bytes += frame.length;
    sendBin(to, k.id, frame);
    // Backpressure: while the receiver's socket is congested, stop reading from the sender.
    if (to.sock.writableNeedDrain) { d.sock.pause(); to.sock.once('drain', () => d.sock.resume()); }
    if (k.cutAt != null && k.bytes >= k.cutAt) { r.cuts++; dropLink(r, k, 'cut at byte offset'); }
  }

  server.on('upgrade', (req, sock) => {
    stats.upgrades++;
    const url = new URL(req.url, 'http://x');
    const key = req.headers['sec-websocket-key'];
    if (url.pathname !== '/relay' || !key) { sock.destroy(); return; }
    if (!originOk(req.headers.origin)) { sock.end('HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\n'); return; }
    const accept = createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
    sock.write(`HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ${accept}\r\n\r\n`);
    sock.setNoDelay(true);
    const r = room(url.searchParams.get('room') || defaultRoom);
    const d = { id: `d${nextDevice++}-${randomBytes(3).toString('hex')}`, label: url.searchParams.get('label') || 'device', sock, links: new Set(), online: true };
    r.devices.set(d.id, d);
    log('device', d.id, d.label);
    sendText(d, { op: 'welcome', id: d.id });
    broadcastDevices(r);
    const gone = () => {
      if (!r.devices.delete(d.id)) return;
      for (const id of [...d.links]) dropLink(r, r.links.get(id), 'device gone');
      broadcastDevices(r);
    };
    readFrames(sock, (op, payload) => {
      if (op === 1) onText(r, d, payload.toString('utf8'));
      else if (op === 2) onBinary(r, d, payload);
      else if (op === 8) { try { sock.end(Buffer.from([0x88, 0])); } catch {} gone(); }
      else if (op === 9) writeFrame(sock, 10, payload);
    }, gone);
    sock.on('close', gone); sock.on('error', gone);
  });

  await new Promise((res) => server.listen(port, HOST, res));
  ownOrigins = new Set([`http://${HOST}:${server.address().port}`, `http://localhost:${server.address().port}`]);
  return { server, port: server.address().port, url: `http://${HOST}:${server.address().port}`,
    close: () => new Promise((res) => { for (const r of rooms.values()) for (const d of r.devices.values()) d.sock.destroy(); server.close(res); }) };
}

// ---------------------------------------------------------------- RFC 6455 framing
function writeFrame(sock, op, payload) {
  const n = payload.length;
  const head = n < 126 ? Buffer.from([0x80 | op, n]) : n < 65536 ? Buffer.from([0x80 | op, 126, n >> 8, n & 255])
    : (() => { const h = Buffer.alloc(10); h[0] = 0x80 | op; h[1] = 127; h.writeBigUInt64BE(BigInt(n), 2); return h; })();
  if (!sock.destroyed) { sock.write(head); sock.write(payload); }
}
const sendText = (d, o) => writeFrame(d.sock, 1, Buffer.from(JSON.stringify(o)));
function sendBin(d, link, frame) {
  const h = Buffer.alloc(4); h.writeUInt32LE(link);
  writeFrame(d.sock, 2, Buffer.concat([h, frame]));
}
const MAX_WS_MESSAGE = 1 << 20;   // frames are <= 16 KiB + header; anything bigger is a broken client
function readFrames(sock, onMessage, onError) {
  let buf = Buffer.alloc(0); let parts = []; let partOp = 0; let partLen = 0;
  sock.on('data', (chunk) => {
    buf = buf.length ? Buffer.concat([buf, chunk]) : chunk;
    for (;;) {
      if (buf.length < 2) return;
      const fin = buf[0] & 0x80, op = buf[0] & 0x0f, masked = buf[1] & 0x80;
      let len = buf[1] & 0x7f, off = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (buf.length < 10) return; const big = buf.readBigUInt64BE(2); if (big > BigInt(MAX_WS_MESSAGE)) { sock.destroy(); return onError(); } len = Number(big); off = 10; }
      if (len > MAX_WS_MESSAGE) { sock.destroy(); return onError(); }
      const need = off + (masked ? 4 : 0) + len;
      if (buf.length < need) return;
      let payload = buf.subarray(off + (masked ? 4 : 0), need);
      if (masked) { const m = buf.subarray(off, off + 4); payload = Buffer.from(payload); for (let i = 0; i < payload.length; i++) payload[i] ^= m[i & 3]; }
      buf = buf.subarray(need);
      if (op === 0) { parts.push(payload); partLen += payload.length; if (partLen > MAX_WS_MESSAGE) { sock.destroy(); return onError(); } if (fin) { onMessage(partOp, Buffer.concat(parts)); parts = []; partLen = 0; } }
      else if (op >= 8) onMessage(op, payload);
      else if (fin) onMessage(op, payload);
      else { partOp = op; parts = [payload]; partLen = payload.length; }
    }
  });
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const args = process.argv.slice(2);
  const get = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
  const s = await startServer({ port: Number(get('--port', 8000)), root: get('--root'), admin: args.includes('--admin') });
  console.log(`serving ${s.url}/ (relay at ws://127.0.0.1:${s.port}/relay); Ctrl-C to stop`);
}

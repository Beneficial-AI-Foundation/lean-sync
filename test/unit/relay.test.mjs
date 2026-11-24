// Dev relay access rules (dev/serve.mjs): loopback is not access control.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { request } from 'node:http';
import { startServer } from '../../dev/serve.mjs';

function upgrade(port, origin) {
  return new Promise((res) => {
    const headers = { Connection: 'Upgrade', Upgrade: 'websocket', 'Sec-WebSocket-Version': '13', 'Sec-WebSocket-Key': 'dGhlIHNhbXBsZSBub25jZQ==' };
    if (origin) headers.Origin = origin;
    const r = request({ host: '127.0.0.1', port, path: '/relay?label=x', headers });
    r.on('upgrade', (resp, sock) => { sock.destroy(); res(resp.statusCode); });
    r.on('response', (resp) => { res(resp.statusCode); resp.resume(); });
    r.on('error', () => res('error'));
    r.end();
  });
}
const post = (port, path, origin) => new Promise((res) => {
  const r = request({ host: '127.0.0.1', port, path, method: 'POST', headers: origin ? { Origin: origin } : {} }, (resp) => { resp.resume(); res(resp.statusCode); });
  r.end('{}');
});

test('the relay accepts WebSocket upgrades only from its own origin', async () => {
  const s = await startServer({ port: 0, root: '/nonexistent' });
  try {
    assert.equal(await upgrade(s.port, `http://127.0.0.1:${s.port}`), 101);
    assert.equal(await upgrade(s.port, `http://localhost:${s.port}`), 101);
    assert.equal(await upgrade(s.port, 'https://evil.example'), 403);
    assert.equal(await upgrade(s.port, `http://127.0.0.1:${s.port + 1}`), 403);
    assert.equal(await upgrade(s.port, null), 403, 'no Origin header: refused');
  } finally { await s.close(); }
});

test('the admin API is off by default and refuses foreign origins when on', async () => {
  const off = await startServer({ port: 0, root: '/nonexistent' });
  try { assert.equal(await post(off.port, '/admin/state'), 403); } finally { await off.close(); }
  const on = await startServer({ port: 0, root: '/nonexistent', admin: true });
  try {
    assert.equal(await post(on.port, '/admin/topology'), 200);
    assert.equal(await post(on.port, '/admin/topology', 'https://evil.example'), 403);
  } finally { await on.close(); }
});

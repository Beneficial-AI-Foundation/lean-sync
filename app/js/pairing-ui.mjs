// Devices panel and pairing dialog (docs/net-design.md §6). Plain DOM. Element ids and data-*
// attributes are stable: the end-to-end tests drive the real UI through them.
//
// Invite (device A): an invitation QR and text → then read the reply (camera or paste).
// Join (device B): read the invitation (camera or paste) → a reply QR and text, renewed every
// few seconds while shown (a reply must be fresh when A reads it: §1.2) → connected.
import { encodeQR } from '../vendor/qr/index.js';
import { decodeQR } from '../vendor/qr/decode.js';
import { groupCode, CodeError } from './netcode.mjs';

export const DEFAULT_STUN = ['stun:stun.l.google.com:19302'];
const SCAN_EVERY_MS = 200;
const CONNECT_HELP = 'Could not connect to the other device. Both devices must keep this page open. Devices on different networks ' +
  'connect only if their routers allow direct connections: this app does not relay data through a server. ' +
  'Try with both devices on the same Wi-Fi network, or start again.';

const $ = (sel) => document.querySelector(sel);
const el = (tag, attrs = {}, ...kids) => {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k.startsWith('on')) e.addEventListener(k.slice(2), v);
    else if (k === 'class') e.className = v;
    else if (v !== null && v !== undefined && v !== false) e.setAttribute(k, v === true ? '' : v);
  }
  for (const k of kids.flat()) if (k !== null && k !== undefined && k !== false) e.append(k);
  return e;
};

/** Draw `text` as a QR code (error correction M, quiet zone 4) on a canvas, black on white. */
export function qrCanvas(text) {
  const m = encodeQR(text, 'raw', { ecc: 'medium', border: 4 });
  const n = m.length, scale = Math.max(3, Math.floor(320 / n));
  const c = el('canvas', { id: 'pair-qr', 'data-code': text, width: n * scale, height: n * scale, 'aria-label': 'QR code of the code below' });
  const g = c.getContext('2d');
  g.fillStyle = '#fff'; g.fillRect(0, 0, c.width, c.height); g.fillStyle = '#000';
  for (let y = 0; y < n; y++) for (let x = 0; x < n; x++) if (m[y][x]) g.fillRect(x * scale, y * scale, scale, scale);
  return c;
}
/** Read a QR code from an ImageData-like {width, height, data}; null if none is found. */
export function readQR(img) { try { return decodeQR(img); } catch { return null; } }

export function createPairingUI({ transport, links, message, getStun, setStun }) {
  const dialog = () => $('#pair');
  let session = null;            // { inv?, resp?, stopCamera?, closed }
  const labels = new Map();      // connection id -> last label seen
  let shown = new Set();         // connection ids listed last time
  const userClosed = new Set();

  // ---------------------------------------------------------------- devices list
  function renderConnections() {
    const list = transport.connections();
    const ul = $('#connections'); ul.replaceChildren();
    for (const c of list) {
      const lbl = (c.linkId != null && links.labelOfLink(c.linkId)) || labels.get(c.id) || null;
      if (lbl) labels.set(c.id, lbl);
      const state = c.state === 'interrupted' ? 'reconnecting…' : !transport.online ? 'paired (you are offline)'
        : !c.remoteOnline ? 'paired (the other device is offline)' : c.linkId != null ? 'connected' : 'connecting…';
      ul.append(el('li', { 'data-conn': c.id, 'data-state': c.state, 'data-linked': c.linkId != null ? '1' : '0' },
        el('span', { class: 'label' }, lbl ?? 'paired device'), ' ', el('span', { class: 'muted' }, state), ' ',
        el('button', { 'data-action': 'disconnect', onclick: () => { userClosed.add(c.id); transport.disconnect(c.id); } }, 'Disconnect')));
    }
    if (!list.length) ul.append(el('li', { class: 'muted', id: 'no-connections' }, 'No paired device. Use “Invite a device” on one device and “Join a device” on the other.'));
    const now = new Set(list.map((c) => c.id));
    for (const id of shown) if (!now.has(id) && !userClosed.has(id)) {
      message(`The connection to ${labels.get(id) ?? 'a paired device'} ended (lost, or closed by the other device). Pair again to reconnect.`, 'error');
    }
    shown = now;
  }

  // ---------------------------------------------------------------- the dialog
  function open(flow) {
    closeSession();
    const d = dialog();
    d.dataset.flow = flow;
    d.replaceChildren();
    session = { closed: false };
    // The close event is queued: a late one from the previous dialog must not end this session.
    d.onclose = () => { if (!d.open) closeSession(); };
    if (!d.open) d.showModal();
    return session;
  }
  function closeSession() {
    if (!session) return;
    const s = session; session = null; s.closed = true;
    s.stopCamera?.();
    if (s.inv && s.inv.state === 'waiting') s.inv.cancel();
    if (s.resp && (s.resp.state === 'waiting' || s.resp.state === 'preparing')) s.resp.cancel();
    clearInterval(s.timer);
  }
  const head = (title, ...intro) => [el('div', { class: 'pair-head' }, el('h3', {}, title),
    el('button', { id: 'pair-close', type: 'button', onclick: () => dialog().close() }, 'Close')), ...intro.map((p) => el('p', {}, p))];
  function setStatus(text, state) { const s = $('#pair-status'); if (s) { s.textContent = text; s.dataset.state = state; } }
  function setError(text, reason = '') { const e = $('#pair-error'); if (e) { e.textContent = text; e.dataset.reason = reason; e.hidden = !text; } }
  function codeBlock(code) {
    const box = el('div', { class: 'code-box' },
      el('textarea', { id: 'pair-code', readonly: true, rows: 4, spellcheck: 'false', 'data-code': code }, groupCode(code)),
      el('div', {}, el('button', { id: 'pair-copy', type: 'button', onclick: async () => {
        try { await navigator.clipboard.writeText(code); setStatus('Copied.', $('#pair-status')?.dataset.state ?? ''); }
        catch { $('#pair-code').select(); setStatus('Select the text and copy it.', $('#pair-status')?.dataset.state ?? ''); }
      } }, 'Copy'), ' ', navigator.share ? el('button', { id: 'pair-share', type: 'button', onclick: () => navigator.share({ text: code }).catch(() => {}) }, 'Share…') : null));
    return box;
  }
  function showCode(code) {
    const q = $('#pair-qr'); if (q) q.replaceWith(qrCanvas(code)); else $('#pair-qr-slot').append(qrCanvas(code));
    const t = $('#pair-code'); if (t) { t.value = groupCode(code); t.dataset.code = code; }
  }

  /** A reader: camera (if any) and a paste field. `onText(text)` may throw CodeError (shown). */
  function reader(what, onText) {
    const box = el('div', { class: 'reader' });
    const video = el('video', { id: 'pair-video', playsinline: true, hidden: true });
    video.muted = true; video.autoplay = true;          // the property, not the attribute: else play() is refused
    const scanBtn = el('button', { id: 'pair-scan', type: 'button', hidden: true, onclick: () => startCamera() }, `Scan the ${what} with the camera`);
    const stopBtn = el('button', { id: 'pair-scan-stop', type: 'button', hidden: true, onclick: () => stopCamera() }, 'Stop the camera');
    const camNote = el('p', { id: 'pair-camera-note', class: 'muted', hidden: true });
    const input = el('textarea', { id: 'pair-input', rows: 3, spellcheck: 'false', autocomplete: 'off', placeholder: `Paste the ${what} here` });
    const submit = el('button', { id: 'pair-submit', type: 'button', onclick: () => use(input.value) }, `Use this ${what}`);
    box.append(scanBtn, stopBtn, video, camNote, el('label', { for: 'pair-input' }, `Or paste the ${what}:`), input, submit,
      el('p', { id: 'pair-error', class: 'error', role: 'alert', hidden: true }));
    const mine = session;
    let stream = null, loop = null;
    async function use(text) {
      setError('');
      try { await onText(text); }
      catch (e) { if (e instanceof CodeError) setError(e.message, e.reason); else setError(e.message || String(e), 'error'); }
    }
    const noCamera = (text) => { camNote.textContent = text; camNote.hidden = false; scanBtn.hidden = true; stopBtn.hidden = true; video.hidden = true; };
    async function detect() {
      try {
        const devs = await navigator.mediaDevices?.enumerateDevices?.() ?? [];
        if (devs.some((d) => d.kind === 'videoinput')) scanBtn.hidden = false;
        else noCamera('No camera found on this device: paste the code instead.');
      } catch { noCamera('No camera available: paste the code instead.'); }
    }
    async function startCamera() {
      setError('');
      try {
        stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: 'environment' }, audio: false });
      } catch (e) {
        noCamera(e?.name === 'NotAllowedError' || e?.name === 'SecurityError' ? 'Camera access was refused: paste the code instead.'
          : e?.name === 'NotFoundError' || e?.name === 'OverconstrainedError' ? 'No camera found on this device: paste the code instead.'
            : `The camera could not be started (${e?.name ?? e}): paste the code instead.`);
        camNote.dataset.reason = e?.name ?? 'error';
        return;
      }
      if (!mine || mine.closed) { stopCamera(); return; }
      video.srcObject = stream; video.hidden = false; scanBtn.hidden = true; stopBtn.hidden = false;
      try { await video.play(); } catch {}
      const canvas = document.createElement('canvas'), g = canvas.getContext('2d', { willReadFrequently: true });
      let busy = false;
      loop = setInterval(async () => {
        if (busy || !video.videoWidth) return;
        busy = true;
        try {
          const k = Math.min(1, 640 / video.videoWidth);
          canvas.width = Math.round(video.videoWidth * k); canvas.height = Math.round(video.videoHeight * k);
          g.drawImage(video, 0, 0, canvas.width, canvas.height);
          const text = readQR(g.getImageData(0, 0, canvas.width, canvas.height));
          if (text && /^LS/i.test(text)) { stopCamera(); input.value = text; await use(text); }
        } finally { busy = false; }
      }, SCAN_EVERY_MS);
    }
    function stopCamera() {
      clearInterval(loop); loop = null;
      for (const tr of stream?.getTracks() ?? []) tr.stop();
      stream = null; video.srcObject = null; video.hidden = true; stopBtn.hidden = true;
      if (camNote.hidden) scanBtn.hidden = false;
    }
    if (mine) mine.stopCamera = stopCamera;
    detect();
    return box;
  }

  async function invite() {
    const s = open('invite');
    const d = dialog();
    d.append(...head('Invite a device', 'Preparing an invitation…'));
    let inv;
    try { inv = await transport.invite(); } catch (e) { d.append(el('p', { class: 'error' }, `Could not make an invitation: ${e.message}`)); return; }
    if (s.closed) { inv.cancel(); return; }
    s.inv = inv;
    const until = new Date(inv.expiresAt).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    d.replaceChildren(...head('Invite a device',
      'On the other device choose “Join a device” and scan this code. If that device has no camera, send it this code as text and paste it there.'),
    inv.noSrflx ? el('p', { id: 'pair-warn', class: 'warn' }, 'The connection helper (STUN) could not be reached: devices on different networks may not be able to connect. On the same Wi-Fi it works.') : null,
    el('div', { id: 'pair-qr-slot', class: 'qr' }, qrCanvas(inv.code)),
    codeBlock(inv.code),
    el('p', { id: 'pair-expires', class: 'muted' }, `Valid for one device, until ${until}.`),
    el('h4', {}, 'Then read the reply that the other device shows'),
    reader('reply', async (text) => {
      setStatus('Connecting…', 'connecting');
      try { await inv.accept(text); }
      catch (e) {
        if (e instanceof CodeError) { setStatus('', inv.state); throw e; }
        setStatus('', 'failed'); setError(CONNECT_HELP, 'connect'); return;
      }
      connected();
    }),
    el('p', { id: 'pair-status', 'data-state': 'waiting', role: 'status' }));
  }

  async function join() {
    const s = open('join');
    const d = dialog();
    d.append(...head('Join a device', 'Scan the invitation shown by the other device, or paste it. (If one of your two devices has no camera, start the invitation on the device that has one.)'),
      reader('invitation', (text) => { respond(s, text); }),
      el('p', { id: 'pair-status', 'data-state': 'reading', role: 'status' }));
  }
  function respond(s, text) {
    const resp = transport.respond(text);            // throws CodeError: shown by the reader
    s.stopCamera?.();
    s.resp = resp;
    const d = dialog();
    d.replaceChildren(...head('Join a device', 'Now let the first device scan this reply.'),
      el('div', { id: 'pair-qr-slot', class: 'qr' }, el('p', { class: 'muted' }, 'Preparing the reply…')),
      el('p', { id: 'pair-renew', class: 'muted' }, 'The reply is renewed every few seconds while it is shown; scan the one on screen. ' +
        'Sending it as text instead? Paste it on the first device right away: when the devices are on different networks a reply is good for only about 10 seconds.'),
      el('div', { id: 'pair-code-slot' }),
      el('p', { id: 'pair-warn', class: 'warn', hidden: true }, 'The connection helper (STUN) could not be reached: devices on different networks may not be able to connect. On the same Wi-Fi it works.'),
      el('p', { id: 'pair-status', 'data-state': 'waiting', role: 'status' }, 'Waiting for the first device…'),
      el('p', { id: 'pair-error', class: 'error', role: 'alert', hidden: true }));
    resp.onCode((code) => {
      if (s.closed) return;
      const slot = $('#pair-qr-slot');
      if (!$('#pair-qr')) slot.replaceChildren(qrCanvas(code)); else showCode(code);
      if (!$('#pair-code')) $('#pair-code-slot').append(codeBlock(code));
      $('#pair-warn').hidden = !resp.noSrflx;
      d.dataset.replies = String(resp.attempts);
    });
    resp.done.then(() => { if (!s.closed) connected(); }, (e) => {
      if (s.closed || resp.state === 'cancelled') return;
      setStatus('', 'failed'); setError(e.message, 'timeout');
    });
  }
  function connected() {
    setStatus('Connected. You can close this window.', 'connected');
    const c = $('#pair-close'); if (c) c.textContent = 'Done';
    message('A device was paired.');
  }

  // ---------------------------------------------------------------- settings: STUN
  function renderStun() { $('#stun').value = getStun().join('\n'); }
  async function saveStun() {
    const list = $('#stun').value.split(/\s+/).map((x) => x.trim()).filter(Boolean);
    const st = $('#stun-status');
    for (const urls of list) {
      let ok = /^stuns?:[^\s/?#]+$/i.test(urls);
      // Firefox throws from the constructor for some addresses (e.g. blocked ports): try it here
      if (ok) { try { new RTCPeerConnection({ iceServers: [{ urls }] }).close(); } catch { ok = false; } }
      if (!ok) { st.textContent = `Not saved: “${urls}” is not a usable STUN address (example: stun:stun.example.org:3478).`; st.dataset.state = 'error'; return; }
    }
    try { await setStun(list); } catch (e) { st.textContent = `Not saved: ${e.message}`; st.dataset.state = 'error'; return; }
    st.textContent = list.length ? 'Saved. Used for the next pairing.' : 'Saved: no STUN server. Devices connect only on the same network.';
    st.dataset.state = 'saved';
  }

  function mount() {
    $('#invite').addEventListener('click', () => invite());
    $('#join').addEventListener('click', () => join());
    $('#stun-save').addEventListener('click', () => saveStun());
    transport.onChange(renderConnections);
    renderStun();
    renderConnections();
  }
  return { mount, renderConnections };
}

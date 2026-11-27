// Devices panel and pairing dialog (docs/net-design.md §6). Plain DOM. Element ids and data-*
// attributes are stable: the end-to-end tests drive the real UI through them.
//
// Invite (device A): an invitation code (text, with Copy) → then paste the reply.
// Join (device B): paste the invitation → a reply code, renewed every few seconds until it is
// copied (a reply must be fresh when A uses it: §1.2) → connected.
import { groupCode, CodeError } from './netcode.mjs';

export const DEFAULT_STUN = ['stun:stun.l.google.com:19302'];
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

export function createPairingUI({ transport, links, message, getStun, setStun }) {
  const dialog = () => $('#pair');
  let session = null;            // { inv?, resp?, closed }
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
    if (s.inv && s.inv.state === 'waiting') s.inv.cancel();
    if (s.resp && (s.resp.state === 'waiting' || s.resp.state === 'preparing')) s.resp.cancel();
    clearInterval(s.timer);
  }
  const head = (title, ...intro) => [el('div', { class: 'pair-head' }, el('h3', {}, title),
    el('button', { id: 'pair-close', type: 'button', onclick: () => dialog().close() }, 'Close')), ...intro.map((p) => el('p', {}, p))];
  function setStatus(text, state) { const s = $('#pair-status'); if (s) { s.textContent = text; s.dataset.state = state; } }
  function setError(text, reason = '') { const e = $('#pair-error'); if (e) { e.textContent = text; e.dataset.reason = reason; e.hidden = !text; } }
  /** The code shown with a Copy button. Copy always copies the code on screen (a reply is
   *  renewed while shown); `onCopy` runs when it is copied (Copy, or a copy from the box). */
  function codeBlock(code, onCopy = () => {}) {
    const box = el('div', { class: 'code-box' },
      el('textarea', { id: 'pair-code', readonly: true, rows: 4, spellcheck: 'false', 'data-code': code, oncopy: () => onCopy() }, groupCode(code)),
      el('div', {}, el('button', { id: 'pair-copy', type: 'button', onclick: async () => {
        const t = $('#pair-code'), shown = t.dataset.code;
        onCopy();
        try { await navigator.clipboard.writeText(shown); setStatus('Copied.', $('#pair-status')?.dataset.state ?? ''); }
        catch { t.select(); setStatus('Select the text and copy it.', $('#pair-status')?.dataset.state ?? ''); }
      } }, 'Copy')));
    return box;
  }
  function showCode(code) {
    const t = $('#pair-code'); if (t) { t.value = groupCode(code); t.dataset.code = code; }
  }

  /** A paste field. `onText(text)` may throw CodeError (shown). */
  function reader(what, onText) {
    const box = el('div', { class: 'reader' });
    const input = el('textarea', { id: 'pair-input', rows: 3, spellcheck: 'false', autocomplete: 'off', placeholder: `Paste the ${what} here` });
    const submit = el('button', { id: 'pair-submit', type: 'button', onclick: () => use(input.value) }, `Use this ${what}`);
    box.append(el('label', { for: 'pair-input' }, `Paste the ${what}:`), input, submit,
      el('p', { id: 'pair-error', class: 'error', role: 'alert', hidden: true }));
    const mine = session;
    async function use(text) {
      setError('');
      try { await onText(text); }
      catch (e) {
        if (mine?.closed) return;             // this dialog was closed meanwhile: never touch a newer one
        if (e instanceof CodeError) setError(e.message, e.reason); else setError(e.message || String(e), 'error');
      }
    }
    return box;
  }

  async function invite() {
    const s = open('invite');
    const d = dialog();
    d.append(...head('Invite a device', 'Preparing an invitation…'));
    let inv;
    try { inv = await transport.invite(); } catch (e) { if (!s.closed) d.append(el('p', { class: 'error' }, `Could not make an invitation: ${e.message}`)); return; }
    if (s.closed) { inv.cancel(); return; }
    s.inv = inv;
    const until = new Date(inv.expiresAt).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
    d.replaceChildren(...head('Invite a device',
      'Copy this invitation and send it to the other device (any way you like: a message, a note, an e-mail). There, choose “Join a device” and paste it.'),
    inv.noSrflx ? el('p', { id: 'pair-warn', class: 'warn' }, 'The connection helper (STUN) could not be reached: devices on different networks may not be able to connect. On the same Wi-Fi it works.') : null,
    codeBlock(inv.code),
    el('p', { id: 'pair-expires', class: 'muted' }, `Valid for one device, until ${until}.`),
    el('h4', {}, 'Then paste the reply that the other device shows'),
    reader('reply', async (text) => {
      setStatus('Connecting…', 'connecting');
      try { await inv.accept(text); }
      catch (e) {
        if (e instanceof CodeError) { if (!s.closed) setStatus('', inv.state); throw e; }
        if (!s.closed) { setStatus('', 'failed'); setError(CONNECT_HELP, 'connect'); }
        return;
      }
      if (!s.closed) connected();
    }),
    el('p', { id: 'pair-status', 'data-state': 'waiting', role: 'status' }));
  }

  async function join() {
    const s = open('join');
    const d = dialog();
    d.append(...head('Join a device', 'Paste the invitation made by the other device.'),
      reader('invitation', (text) => { respond(s, text); }),
      el('p', { id: 'pair-status', 'data-state': 'reading', role: 'status' }));
  }
  function respond(s, text) {
    const resp = transport.respond(text);            // throws CodeError: shown by the reader
    s.resp = resp;
    const d = dialog();
    const RENEWING = 'The reply changes every few seconds until you copy it. Copy it, then paste it on the first device soon: ' +
      'when the devices are on different networks a reply may be good for only about 10 seconds.';
    let copied = false;
    // Copying keeps the reply on screen (no more renewals), so the code pasted on the first device
    // is the one this device keeps waiting with.
    const onCopy = () => { if (s.closed || copied) return; copied = true; resp.keep(); $('#pair-renew').textContent = 'Copied: this reply now stays as it is. Paste it on the first device.'; };
    d.replaceChildren(...head('Join a device', 'Now copy this reply and paste it on the first device.'),
      el('p', { id: 'pair-renew', class: 'muted' }, RENEWING),
      el('div', { id: 'pair-code-slot' }, el('p', { class: 'muted' }, 'Preparing the reply…')),
      el('p', { id: 'pair-warn', class: 'warn', hidden: true }, 'The connection helper (STUN) could not be reached: devices on different networks may not be able to connect. On the same Wi-Fi it works.'),
      el('p', { id: 'pair-status', 'data-state': 'waiting', role: 'status' }, 'Waiting for the first device…'),
      el('p', { id: 'pair-error', class: 'error', role: 'alert', hidden: true }));
    resp.onCode((code) => {
      if (s.closed) return;
      if (!$('#pair-code')) $('#pair-code-slot').replaceChildren(codeBlock(code, onCopy)); else showCode(code);
      if (copied) {                                  // the copied reply expired: renewal resumed
        copied = false;
        const r = $('#pair-renew'); r.textContent = 'The copied reply expired before it was used. Copy this new one. ' + RENEWING; r.dataset.expired = '1';
      }
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

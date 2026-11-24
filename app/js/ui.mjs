// DOM rendering. Plain DOM, no framework. Element ids and data-* attributes are stable (the
// end-to-end tests drive and read the page through them).
import { buildRows, uniqueName, STATUS_TEXT } from './view.mjs';
import { replicaKey } from './codec.mjs';
import { MAX_FILE_BYTES } from './storage.mjs';

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
const fmtSize = (n) => n == null ? '' : n < 1024 ? `${n} B` : n < 1048576 ? `${(n / 1024).toFixed(1)} KB` : `${(n / 1048576).toFixed(1)} MB`;

export function createUI({ storage, getCore, transport, label }) {
  const state = { files: [], pending: [], status: null, peers: [], summary: null, sizes: new Map(),
    saveFailed: false, rollback: false, restarts: 0, refused: [], messages: [], phase: 'idle', phaseInfo: null, renders: 0 };

  function message(text, kind = 'info') {
    state.messages.push({ text, kind, at: Date.now() });
    if (state.messages.length > 6) state.messages.shift();
    renderMessages();
  }

  // ------------------------------------------------------------ callbacks from the core
  const callbacks = {
    onPhase(p, info) { state.phase = p; state.phaseInfo = info; renderPhase(); },
    onFiles(files) { state.files = files; renderFiles(); loadSizes(); },
    onPending(items) { state.pending = items; renderFiles(); },
    onStatus(s) { state.status = s; state.saveFailed = s.saveFailed; state.rollback = s.rollback; renderBanners(); renderHeader(); renderFiles(); },
    onPeers(peers) { state.peers = peers; renderPeers(); },
    onNotice(n) {
      switch (n.notice) {
        case 'pendingSummary': state.summary = n; renderPeers(); renderBanners(); break;
        case 'saveFailed': state.saveFailed = true; renderBanners(); renderHeader(); break;
        case 'saveRecovered': state.saveFailed = false; renderBanners(); renderHeader(); message('Changes are saved again.'); break;
        case 'rollbackDetected': state.rollback = true; renderBanners(); renderHeader(); renderFiles(); break;
        case 'opRejected': message(`The change was refused: ${n.why}`, 'error'); break;
        case 'engineRestarted': state.restarts = n.count; renderBanners(); break;
      }
    },
    onLog(line) { const pre = $('#log'); if (pre) { pre.textContent += line + '\n'; if (pre.textContent.length > 60000) pre.textContent = pre.textContent.slice(-40000); } },
  };

  // Sizes come from OPFS, one lookup per present version. They are collected first and the table is
  // rendered once per batch (not once per file: that was quadratic on a cold load of many files).
  let sizesLoading = false;
  async function loadSizes() {
    if (sizesLoading) return;
    sizesLoading = true;
    try {
      for (;;) {
        const todo = new Set();                   // per hash, not per path
        for (const f of state.files) for (const v of f.versions) {
          if (!v.present) continue;
          const hx = Array.from(v.hash, (x) => x.toString(16).padStart(2, '0')).join('');
          if (!state.sizes.has(hx)) todo.add(hx);
        }
        if (!todo.size) return;
        for (const hx of todo) { try { state.sizes.set(hx, (await storage.blobFile(hx)).size); } catch { state.sizes.set(hx, null); } }
        renderFiles();
      }
    } finally { sizesLoading = false; }
  }

  // ------------------------------------------------------------ rendering
  function renderPhase() {
    const fatal = $('#fatal');
    $('#app').hidden = !(state.phase === 'running' || state.phase === 'starting' || state.phase === 'running-startup');
    fatal.hidden = !(state.phase === 'startupFailed' || state.phase === 'failed');
    fatal.dataset.phase = state.phase;
    fatal.replaceChildren();
    if (state.phase === 'startupFailed') {
      fatal.append(
        el('h2', {}, 'The saved file list could not be read'),
        el('p', {}, `This device's stored index is damaged or unreadable (${state.phaseInfo}). Nothing has been changed.`),
        el('p', {}, el('button', { id: 'retry-start', onclick: () => getCore().retryStart() }, 'Try again'), ' ',
          el('button', { id: 'reset', class: 'danger', onclick: confirmReset }, 'Reset this device…')));
    } else if (state.phase === 'failed') {
      fatal.append(el('h2', {}, 'Sync is stopped'), el('p', { id: 'fatal-text' }, String(state.phaseInfo)),
        el('p', {}, el('button', { id: 'retry-start', onclick: () => getCore().retryStart() }, 'Try again'), ' ',
          el('button', { onclick: () => location.reload() }, 'Reload the page')));
    }
    $('#busy').hidden = state.phase !== 'starting' && state.phase !== 'running-startup';
    renderHeader(); renderBanners(); renderFiles();
  }

  function renderHeader() {
    const core = getCore();
    const r = core?.replica();
    $('#device').textContent = `${label}${r ? ` (${replicaKey(r).slice(0, 8)})` : ''}`;
    const s = state.status;
    $('#saving').textContent = state.saveFailed ? 'not saved' : s && (s.dirty || s.persistInFlight) ? 'saving…' : s ? 'saved' : '';
    $('#saving').dataset.state = state.saveFailed ? 'failed' : s && (s.dirty || s.persistInFlight) ? 'saving' : 'saved';
    const editable = core?.canEdit() ?? false;
    $('#add-button').disabled = !editable;
  }

  function renderBanners() {
    const b = $('#banners'); b.replaceChildren();
    if (state.rollback) b.append(el('div', { class: 'banner danger', id: 'banner-rollback' },
      el('strong', {}, 'This device\'s storage was rolled back, or another device uses its identity. '),
      'To protect your other devices, editing is blocked here until this device restarts under a new identity. ',
      el('button', { id: 'new-identity', onclick: confirmNewIdentity }, 'Restart under a new identity…')));
    if (state.saveFailed) b.append(el('div', { class: 'banner danger', id: 'banner-save' },
      el('strong', {}, 'Changes could not be saved. '),
      'Recent changes on this device are not stored yet and are not sent to other devices. Retrying automatically. ',
      el('button', { id: 'retry-save', onclick: () => getCore().retrySave() }, 'Retry now')));
    // Only received contents failed (the index is saved): same retry, without claiming unsaved changes.
    if (!state.saveFailed && state.summary?.localFailure > 0) b.append(el('div', { class: 'banner warn', id: 'banner-store' },
      `${state.summary.localFailure} received file content(s) could not be stored on this device. Retrying automatically. `,
      el('button', { id: 'retry-store', onclick: () => getCore().retrySave() }, 'Retry now')));
    if (state.restarts) b.append(el('div', { class: 'banner', id: 'banner-restart' },
      `The sync engine hit an internal error and was restarted from the last saved state (${state.restarts}×).`));
    for (const r of state.refused) b.append(el('div', { class: 'banner warn' },
      `Refused to sync with "${r.label}": it presents this device's own identity (were two browsers restored from the same storage?).`));
  }

  function renderPeers() {
    const p = $('#peers');
    p.replaceChildren(el('span', {}, 'Peers: '), ...(state.peers.length ? state.peers.map((x, i) =>
      el('span', { class: 'peer', 'data-status': x.status }, `${i ? ' · ' : ''}${x.label ?? 'peer ' + x.peer}${x.replica ? ` (${replicaKey(x.replica).slice(0, 6)})` : ''} ${x.status === 'inSync' ? 'in sync' : x.status}`))
      : [el('span', { class: 'muted' }, transport.online ? 'none connected' : 'offline')]));
    const s = state.summary;
    $('#summary').textContent = s && (s.fetching + s.queued + s.waiting + s.localFailure)
      ? `Missing file contents: ${s.fetching} fetching · ${s.queued} queued · ${s.waiting} waiting` +
        (s.localFailure ? ` · ${s.localFailure} could not be stored on this device (retrying)` : '')
      : '';
  }

  function renderFiles() {
    state.renders++;
    const tbody = $('#files'); tbody.replaceChildren();
    const rows = buildRows(state.files, state.pending);
    const editable = getCore()?.canEdit() ?? false;
    $('#empty').hidden = rows.length > 0;
    for (const row of rows) {
      const name = el('td', { class: 'name' }, row.dir ? el('span', { class: 'dir' }, row.dir) : null, row.base);
      const tr = el('tr', { 'data-path': row.path, 'data-status': row.status, 'data-hashes': row.versions.map((v) => v.hex).join(',') });
      if (row.status !== 'conflicted') {
        const v = row.versions[0];
        tr.append(name, el('td', { class: 'size' }, fmtSize(state.sizes.get(v.hex))),
          el('td', { class: 'status', 'data-status': v.status }, statusText(v)),
          el('td', { class: 'actions' },
            el('button', { 'data-action': 'download', disabled: !v.present, onclick: () => download(row, v) }, 'Download'), ' ',
            el('button', { 'data-action': 'delete', disabled: !editable, onclick: () => getCore().deleteFiles([{ path: row.path, versions: row.versions.map((x) => x.hash) }]) }, 'Delete')));
        tbody.append(tr);
      } else {
        tr.append(name, el('td', {}), el('td', { class: 'status', 'data-status': 'conflicted' }, `conflict: ${row.versions.length} versions`),
          el('td', { class: 'actions' },
            el('button', { 'data-action': 'keep-both', disabled: !editable || row.versions.length !== 2 || row.versions.some((v) => !v.present),
              onclick: () => keepBoth(row) }, 'Keep both'), ' ',
            el('button', { 'data-action': 'delete', disabled: !editable, onclick: () => getCore().deleteFiles([{ path: row.path, versions: row.versions.map((x) => x.hash) }]) }, 'Delete')));
        tbody.append(tr);
        row.versions.forEach((v, i) => tbody.append(el('tr', { class: 'version', 'data-path': row.path, 'data-version': v.hex, 'data-status': v.status },
          el('td', { class: 'name' }, `version ${String.fromCharCode(97 + i)} · ${v.hex.slice(0, 8)}`),
          el('td', { class: 'size' }, fmtSize(state.sizes.get(v.hex))),
          el('td', { class: 'status', 'data-status': v.status }, statusText(v)),
          el('td', { class: 'actions' },
            el('button', { 'data-action': 'keep', disabled: !editable || !v.present, onclick: () => getCore().keepVersion(row.path, v.hash, row.versions.map((x) => x.hash)) }, 'Keep this one'), ' ',
            el('button', { 'data-action': 'download', disabled: !v.present, onclick: () => download(row, v, v.hex.slice(0, 8)) }, 'Download')))));
      }
    }
  }
  const statusText = (v) => v.status === 'fetching' && v.peer != null
    ? `fetching from ${getCore()?.st && state.peers.find((p) => p.peer === v.peer)?.label || 'peer ' + v.peer}` : STATUS_TEXT[v.status];

  function renderMessages() {
    $('#messages').replaceChildren(...state.messages.map((m) => el('div', { class: `msg ${m.kind}` }, m.text)));
  }

  // ------------------------------------------------------------ actions
  async function download(row, v, suffix) {
    try {
      const blob = await getCore().readVerified(v.hash);
      let name = row.base;
      if (suffix) { const d = name.lastIndexOf('.'); name = d > 0 ? `${name.slice(0, d)} (${suffix})${name.slice(d)}` : `${name} (${suffix})`; }
      const url = URL.createObjectURL(blob);
      const a = el('a', { href: url, download: name });
      document.body.append(a); a.click(); a.remove();
      setTimeout(() => URL.revokeObjectURL(url), 60000);
    } catch (e) { message(`Could not download ${row.path}: ${e.message}`, 'error'); }
  }
  function keepBoth(row) {
    const [a, b] = row.versions;
    const taken = new Set(state.files.map((f) => f.path));
    const other = uniqueName(row.path, taken);
    try { getCore().keepBoth(row.path, a.hash, b.hash, other, row.versions.map((x) => x.hash)); message(`Kept both: version b is now "${other}".`); }
    catch (e) { message(e.message, 'error'); }
  }

  async function addFiles(fileList) {
    const files = [];
    for (const f of fileList) {
      const name = f.name.normalize('NFC');
      if (f.size > MAX_FILE_BYTES) { message(`"${name}" was not added: it is ${fmtSize(f.size)}, and this version accepts files up to ${MAX_FILE_BYTES / 1048576} MB (each file is hashed in memory).`, 'error'); continue; }
      if (!name) { message('A file without a name was not added.', 'error'); continue; }
      // the versions of this name the user is looking at right now (superseded by the add)
      const shownFile = state.files.find((x) => x.path === name);
      files.push({ name, blob: f, supersedes: shownFile ? shownFile.versions.map((v) => v.hash) : [] });
    }
    if (!files.length) return;
    try {
      const r = await getCore().addFiles(files);
      for (const e of r.errors) message(`"${e.name}" was not added: ${e.error}`, 'error');
    } catch (e) { message(e.message, 'error'); }
  }

  function confirmDialog(title, paragraphs, okText) {
    return new Promise((resolve) => {
      const d = $('#confirm');
      d.replaceChildren(el('form', { method: 'dialog' }, el('h3', {}, title), ...paragraphs.map((p) => el('p', {}, p)),
        el('menu', {}, el('button', { value: 'cancel', id: 'confirm-cancel' }, 'Cancel'), ' ', el('button', { value: 'ok', id: 'confirm-ok', class: 'danger' }, okText))));
      d.onclose = () => resolve(d.returnValue === 'ok');
      d.returnValue = '';
      d.showModal();
    });
  }
  async function confirmNewIdentity() {
    const ok = await confirmDialog('Restart under a new identity?', [
      'You keep: every file and version this device shows now, and the file contents stored on it. Nothing shown here is deleted.',
      'You lose: edits made on this device before its storage was rolled back that never reached another device; they cannot be recovered from here.',
      'Other devices will see this device as a new one. Editing works again after the restart.'], 'Restart under a new identity');
    if (ok) await getCore().newIdentity();
  }
  async function confirmReset() {
    const ok = await confirmDialog('Reset this device?', [
      'This starts an empty file list under a new identity. The file list will be filled again from your other devices.',
      'You lose: every change made on this device that never reached another device.',
      'You keep: the file contents stored on this device; they are offered to your other devices.'], 'Reset');
    if (ok) await getCore().resetIndex();
  }

  // ------------------------------------------------------------ wiring
  function mount() {
    const input = $('#add-input');
    $('#add-button').addEventListener('click', () => input.click());
    input.addEventListener('change', () => { const fs = [...input.files]; input.value = ''; addFiles(fs); });
    const online = $('#online');
    online.addEventListener('change', () => { transport.setOnline(online.checked); renderPeers(); });
    document.addEventListener('dragover', (e) => { e.preventDefault(); document.body.classList.add('dropping'); });
    document.addEventListener('dragleave', (e) => { if (!e.relatedTarget) document.body.classList.remove('dropping'); });
    document.addEventListener('drop', (e) => {
      e.preventDefault(); document.body.classList.remove('dropping');
      if (!(getCore()?.canEdit())) { message('Files cannot be added right now.', 'error'); return; }
      const files = [];
      for (const item of e.dataTransfer.items ?? []) {
        if (item.kind !== 'file') continue;
        const entry = item.webkitGetAsEntry?.();
        if (entry?.isDirectory) { message(`"${entry.name}" is a folder; folders are not supported in this version, drop the files themselves.`, 'error'); continue; }
        const f = item.getAsFile(); if (f) files.push(f);
      }
      addFiles(files);
    });
    renderPhase(); renderPeers();
  }

  return { callbacks, mount, message, onRefused: (r) => { if (!state.refused.some((x) => x.label === r.label)) state.refused.push(r); renderBanners(); }, state };
}

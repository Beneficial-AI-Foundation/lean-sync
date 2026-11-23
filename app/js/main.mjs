// Boot: one tab owns the storage (Web Lock), then storage, engine, core, links, transport, UI.
// URL parameters: device=<name> (this device's name, remembered), room=<relay room>,
// The transport is the /relay endpoint of the serving origin (dev/serve.mjs), never another one.
import { createEngine } from './engine.mjs';
import { openStorage } from './storage.mjs';
import { createCore } from './core.mjs';
import { createLinks } from './links.mjs';
import { createUI } from './ui.mjs';
import { createRelayTransport } from './transport/relay.mjs';

const params = new URLSearchParams(location.search);
const show = (id) => { for (const s of ['#locked', '#app', '#fatal', '#unsupported']) document.querySelector(s).hidden = s !== id; };

async function main() {
  if (!navigator.locks || !navigator.storage?.getDirectory || !indexedDB) {
    show('#unsupported'); return;
  }
  // One active tab per profile: two tabs on one storage would be two devices with one replica id.
  // The lock is held until the tab closes (or crashes: the browser releases it then).
  const owner = await new Promise((resolve) => {
    navigator.locks.request('leansync-owner', { ifAvailable: true }, async (lock) => {
      resolve(!!lock);
      if (lock) await new Promise(() => {});
    }).catch(() => resolve(false));
  });
  if (!owner) { show('#locked'); window.leansync = { phase: 'locked' }; return; }
  await run();
}

async function run() {
  show('#app');
  const storage = await openStorage();
  let label = params.get('device') || await storage.getLabel();
  if (!label) label = `device-${Math.random().toString(36).slice(2, 6)}`;
  if (label !== await storage.getLabel()) await storage.setLabel(label).catch(() => {});
  // Ask the browser not to evict our storage. Firefox asks the user, so this must not block
  // start-up (in a headless browser the prompt never resolves).
  const showPersist = (p) => { document.querySelector('#persist').textContent = p ? 'storage: persistent' : 'storage: may be evicted by the browser'; };
  navigator.storage.persisted().then((p) => { showPersist(p); if (!p) navigator.storage.persist().then(showPersist, () => {}); }, () => {});

  // The transport is always the relay of the serving origin. There is deliberately no parameter to
  // name another endpoint: the relay decides which peers this device syncs with, so a crafted link
  // could otherwise send the user's files elsewhere.
  const relayUrl = `${location.protocol === 'https:' ? 'wss' : 'ws'}://${location.host}/relay`;
  const transport = createRelayTransport({ url: relayUrl, room: params.get('room') || '', label });
  let core = null;
  const ui = createUI({ storage, getCore: () => core, transport, label });
  const links = createLinks({
    emit: (ev, ep) => core.emit(ev, ep), storage, epoch: () => core.epoch(),
    self: () => ({ replica: core?.replica(), label }),
    onRefused: (r) => ui.onRefused(r),
    onStorageError: (e) => ui.message(`A received file could not be stored: ${e.message}`, 'error'),
    log: (m) => core.log(m),
  });
  const { default: createLeanSync } = await import('../lean/lean_sync.mjs');
  core = createCore({ makeEngine: () => createEngine(createLeanSync), storage, links, ui: ui.callbacks });
  ui.mount();
  // Read-only diagnostics (also what the end-to-end tests observe).
  window.leansync = {
    get phase() { return core.st.phase; }, get epoch() { return core.st.epoch; },
    get instances() { return core.st.instances; }, get traps() { return core.st.traps.length; },
    get replica() { const r = core.replica(); return r ? `${r.hi.toString(16)}:${r.lo.toString(16)}` : null; },
    get heapBytes() { return core.st.engine?.heapBytes() ?? null; }, get log() { return core.st.log.slice(); },
    label,
  };
  await core.start();
  transport.start({ onLink: (l) => links.attach(l), onStatus: (s) => core.log(`transport: ${s}`) });
}

main().catch((e) => { console.error(e); document.querySelector('#fatal').hidden = false; document.querySelector('#fatal').textContent = `Could not start: ${e.message}`; });

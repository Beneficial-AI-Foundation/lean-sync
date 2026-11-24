// Pure view model: Lean's `snapshot` and `pending` replies -> the rows the UI shows.
//
// A file is `complete` only if Lean reports every version present, and Lean marks a blob present
// only after the host reported it verified and durably stored (blobStored / blobsStored / the
// local put that follows the store). Missing versions take the status of their hash in the
// `pending` reply: requested -> fetching, queued, waiting; a hash the reply does not list yet
// (the reply is a few ms older than the snapshot) shows as `pending`, never as complete.
//
// Names: the CRDT allows any string as a path. This version adds files by flat name only, but a
// name containing '/' that arrives from another device is shown in full, the part up to the last
// '/' dimmed as a folder prefix; downloading it saves the last component.
import { hex } from './hash.mjs';

export function splitPath(path) {
  const i = path.lastIndexOf('/');
  return i < 0 ? { dir: '', base: path } : { dir: path.slice(0, i + 1), base: path.slice(i + 1) || path };
}

export function buildRows(files, pendingItems) {
  const pend = new Map((pendingItems ?? []).map((it) => [hex(it.hash), it]));
  return (files ?? []).map((f) => {
    const versions = f.versions.map((v) => {
      const hx = hex(v.hash);
      let status = 'complete', peer = null;
      if (!v.present) {
        const p = pend.get(hx);
        status = !p ? 'pending' : p.status === 'requested' ? 'fetching' : p.status;   // fetching | queued | waiting
        peer = p?.peer ?? null;
      }
      return { hash: v.hash, hex: hx, present: v.present, status, peer };
    });
    const { dir, base } = splitPath(f.path);
    let status;
    if (versions.length >= 2) status = 'conflicted';
    else status = versions[0]?.status ?? 'pending';
    return { path: f.path, dir, base, status, versions };
  });
}

/** `name (2).ext`, `name (3).ext`, ... not already in `taken` (same folder prefix kept). */
export function uniqueName(path, taken) {
  const { dir, base } = splitPath(path);
  const dot = base.lastIndexOf('.');
  const stem = dot > 0 ? base.slice(0, dot) : base, ext = dot > 0 ? base.slice(dot) : '';
  for (let i = 2; ; i++) {
    const candidate = `${dir}${stem} (${i})${ext}`;
    if (!taken.has(candidate)) return candidate;
  }
}

export const STATUS_TEXT = {
  complete: 'complete',
  fetching: 'fetching',
  queued: 'queued',
  waiting: 'waiting: nobody reachable has it',
  pending: 'not yet available',
  conflicted: 'conflict',
};

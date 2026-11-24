// Demand reads use fixed, page-aligned blocks. Keep smaller databases in
// multiple blocks when possible, so opening them need not read the whole file.
const DEFAULT_VFS_CHUNK = 1024 * 1024;
function vfsChunkSize(setting, pageSize, size) {
  if (setting === "page") return pageSize;
  const bytes = Number(setting);
  const valid = Number.isSafeInteger(bytes) && bytes >= pageSize && bytes <= 4 * DEFAULT_VFS_CHUNK && bytes % pageSize === 0;
  const target = valid ? bytes : DEFAULT_VFS_CHUNK;
  return size > target ? target : Math.max(pageSize, Math.floor(size / (2 * pageSize)) * pageSize);
}

// Adapter for the SRI-checked sql.js-httpvfs 0.8.12 worker. Each patch must
// match exactly once. Recheck against lazyFile.ts and sqlite.worker.ts on upgrade.
function adaptVfsWorker(source, profile) {
  const patch = (from, to) => {
    const at = source.indexOf(from);
    if (at === -1 || source.indexOf(from, at + from.length) !== -1) {
      throw new Error("unsupported sql.js-httpvfs worker; could not apply its adapter");
    }
    source = source.slice(0, at) + to + source.slice(at + from.length);
  };
  // One virtual server chunk. Its length was validated by the GET probe.
  patch("checkServer(){var", "checkServer(){if(this._length){this.serverChecked=true;return}var");
  // Cap sequential read-ahead at one block and disable upstream's unbounded page log.
  patch("logPageReads:!0,maxReadHeads:3", "logPageReads:!1,maxReadSpeed:e.requestChunkSize,maxReadHeads:3");
  // Even a one-block database uses Range. The worker checks the physical SQLite page size separately.
  patch("this.length!==this.chunkSize&&i.setRequestHeader", "i.setRequestHeader");
  patch("e!==u.requestChunkSize&&console.warn", "e!==silVfsPageSize&&console.warn");
  patch("this.requestLimiter(t-e),this.totalFetchedBytes+=t-e", "this.requestLimiter(t-e+1),this.totalFetchedBytes+=t-e+1");
  if (profile) {
    patch("copyInto(e,t,r,n){", "copyInto(e,t,r,n){silVfsTrace.read(n,Math.min(r,this.length-n));");
  }
  return source;
}

// Inside the worker. Keep a bounded buffer and transfer it only on request.
function makeVfsTrace(pageSize) {
  const limit = 8192;
  let events = [], dropped = 0;
  function record(event) {
    if (events.length === limit) { dropped++; return; }
    if (event.start !== null && event.end > event.start) {
      event.firstPage = Math.floor(event.start / pageSize) + 1;
      event.lastPage = Math.ceil(event.end / pageSize);
    }
    events.push(event);
  }
  return {
    record,
    read(start, bytes) {
      if (bytes > 0) record({ type: "read", atMs: performance.now(), start, end: start + bytes, bytes });
    },
    take() {
      const trace = { timeOrigin: performance.timeOrigin, events, dropped };
      events = [];
      dropped = 0;
      return trace;
    },
  };
}

const VFS_SNAPSHOT_ERROR = "silmaril snapshot: ";
class SourceChanged extends Error {
  constructor(url, was, now, why) {
    super(`${url} changed on the server after this page opened it` + (now ? ` (version ${was}; the server now has ${now})` : ` (${why || "version " + was})`) +
      ". Nothing read since was used.");
    this.name = "SourceChanged"; Object.assign(this, { url, was, now, why });
  }
}
async function lazyBackend(url, pageSize, { size, etag }) {
  if (typeof createDbWorker !== "function") throw new Error("sql.js-httpvfs did not load");
  const tag = versionOf(etag, size), prefix = vfsRangePrefix(url, tag);
  const chunkSize = vfsChunkSize(PARAMS.get("vfs-chunk"), pageSize, size);
  const profile = PARAMS.get("vfs-profile") === "1";
  const snapshot = { rangeUrl: prefix + "0", etag, size };
  const [code, wasmBytes] = await Promise.all([
    sriAsset(HTTPVFS + "sqlite.worker.js", HTTPVFS_WORKER_SRI).then(r => r.text()),
    sriAsset(HTTPVFS + "sql-wasm.wasm", HTTPVFS_WASM_SRI).then(r => r.arrayBuffer()),
  ]);
  const setup = `const silVfsPageSize = ${pageSize};
const silVfsTrace = ${profile ? `(${makeVfsTrace})(silVfsPageSize)` : "null"};
const silVfsRangeFailure = (${guardVfsRanges})(${JSON.stringify(snapshot)}, ${strongETag}, ${versionOf}, silVfsTrace?.record);
`;
  const worker = URL.createObjectURL(new Blob([setup, adaptVfsWorker(code, profile)], { type: "text/javascript" }));
  const wasm = URL.createObjectURL(new Blob([wasmBytes], { type: "application/wasm" }));

  const fromError = async (error, failure) => {
    if (failure) return new SourceChanged(url, tag, failure.now, failure.why);
    const now = await probeVersion(url);
    if (now && now !== tag) return new SourceChanged(url, tag, now);
    const message = String(error?.message || error);
    if (message.startsWith(VFS_SNAPSHOT_ERROR)) return new SourceChanged(url, tag, null, message.slice(VFS_SNAPSHOT_ERROR.length));
    if (/malformed|not a database|corrupt/i.test(message) && now === tag) {
      return new Error(message + ". The server still serves the version this page opened; this is not a mix of two versions " +
        "(check the file with `sqlite3 <file> 'PRAGMA integrity_check'`).");
    }
    return error;
  };

  let w;
  try {
    w = await createDbWorker([{ from: "inline", config: { serverMode: "chunked", urlPrefix: prefix,
      serverChunkSize: size, databaseLengthBytes: size, suffixLength: 1, requestChunkSize: chunkSize } }], worker, wasm);
  } catch (error) {
    throw await fromError(error);
  } finally {
    URL.revokeObjectURL(worker);
    URL.revokeObjectURL(wasm);
  }

  let changed = null;
  const run = async (f) => {
    if (changed) throw changed;
    try {
      return await f();
    } catch (error) {
      const failure = await w.worker.evalCode("return silVfsRangeFailure()").catch(() => null);
      const reported = await fromError(error, failure);
      if (reported instanceof SourceChanged && !changed) {
        changed = reported;
        noteChanged(changed);
      }
      throw changed || reported;
    }
  };
  return {
    mode: `lazy (HTTP Range, ${pageSize} B pages, ${chunkSize} B chunks, version ${tag})`, pageSize, chunkSize, size, tag,
    query: (sql, params) => run(() => w.db.query(sql, params)),
    exec: (sql) => run(() => w.db.exec(sql)),
    stats: () => w.worker.getStats(),
    profile: profile ? async () => ({ pageSize, chunkSize, size, version: tag,
      ...(await w.worker.evalCode("return silVfsTrace.take()")) }) : null,
    changed: () => changed,
    // Let previously posted queries settle before shutting down the worker.
    close() { w.worker.evalCode("setTimeout(() => self.close(), 0)").catch(() => {}); },
  };
}

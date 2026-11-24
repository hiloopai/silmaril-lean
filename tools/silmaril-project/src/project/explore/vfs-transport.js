// HTTP reads for a single SQLite snapshot. The no-store GET probe supplies both
// the raw length and the strong validator of the identity representation.
const DB_HEADER_RANGE = "bytes=0-99";
function fetchDbHeader(url) {
  return fetch(url, { headers: { Range: DB_HEADER_RANGE }, cache: "no-store" });
}
function strongETag(value) {
  return /^"[\x21\x23-\x7e\x80-\xff]*"$/.test(value || "") ? value : null;
}
function versionOf(etag, size) {
  // Preserve every byte of the opaque ETag, including punctuation.
  return etag.slice(1, -1) + "-" + size;
}
function dbHeaderMetadata(response) {
  const enc = response.headers.get("content-encoding");
  const range = /^bytes 0-99\/(\d+)$/.exec(response.headers.get("content-range") || "");
  const size = range ? Number(range[1]) : null;
  return {
    size: Number.isSafeInteger(size) && size >= 100 ? size : null,
    etag: strongETag(response.headers.get("etag")),
    identity: !enc || enc === "identity",
  };
}
async function probeVersion(url) {
  try {
    const r = await fetchDbHeader(url);
    const { size, etag, identity } = dbHeaderMetadata(r);
    r.body?.cancel().catch(() => {});
    return r.status === 206 && size && etag && identity ? versionOf(etag, size) : null;
  } catch {
    return null;
  }
}
function vfsRangePrefix(url, version) {
  const target = new URL(url);
  target.hash = "";
  target.searchParams.set("__sil_v", version);
  target.searchParams.delete("__sil_part");
  return target.href + "&__sil_part=";
}

// Runs inside the dedicated worker. Validate before synchronous XHR returns to
// SQLite, including when the service worker reconstructed the 206 from cache.
function guardVfsRanges(snapshot, strongETag, versionOf, emit) {
  const X = self.XMLHttpRequest.prototype;
  const { open, setRequestHeader, send } = X;
  let failure = null;
  const fail = (why, now = null) => {
    failure ||= { why, now };
    throw new Error("silmaril snapshot: " + failure.why);
  };
  X.open = function (method, url) {
    this.silDbRead = method === "GET" && url === snapshot.rangeUrl;
    this.silRange = null;
    return open.apply(this, arguments);
  };
  X.setRequestHeader = function (name, value) {
    if (this.silDbRead && /^range$/i.test(name)) this.silRange = value;
    return setRequestHeader.apply(this, arguments);
  };
  function checkedSend() {
    if (failure) fail(failure.why);
    const want = /^bytes=(\d+)-(\d+)$/.exec(this.silRange || "");
    if (!want) fail("the worker did not request a byte range");
    const out = send.apply(this, arguments);
    const got = /^bytes (\d+)-(\d+)\/(\d+)$/.exec(this.getResponseHeader("content-range") || "");
    const enc = this.getResponseHeader("content-encoding");
    if (this.status !== 206 || !got || (enc && enc !== "identity")) {
      fail(`the range received HTTP ${this.status}${got ? "" : " without Content-Range"}${enc && enc !== "identity" ? " (" + enc + " encoded)" : ""}`);
    }
    const etag = strongETag(this.getResponseHeader("etag"));
    if (+got[3] !== snapshot.size || etag !== snapshot.etag) {
      fail("the database length or strong ETag changed", etag ? versionOf(etag, got[3]) : null);
    }
    if (got[1] !== want[1] || got[2] !== want[2]) fail(`bytes ${got[1]}-${got[2]} came back for ${want[1]}-${want[2]}`);
    if (this.response?.byteLength !== +want[2] - +want[1] + 1) fail("the range body had the wrong length");
    return out;
  }
  if (emit) {
    X.send = function () {
      if (!this.silDbRead) return send.apply(this, arguments);
      const atMs = performance.now();
      let accepted = false;
      try {
        const out = checkedSend.apply(this, arguments);
        accepted = true;
        return out;
      } finally {
        const requested = /^bytes=(\d+)-(\d+)$/.exec(this.silRange || "");
        const returned = /^bytes (\d+)-(\d+)\//.exec(this.getResponseHeader("content-range") || "");
        emit({ type: "fetch", atMs, durationMs: performance.now() - atMs,
          start: requested ? +requested[1] : null, end: requested ? +requested[2] + 1 : null,
          responseStart: returned ? +returned[1] : null, responseEnd: returned ? +returned[2] + 1 : null,
          bytes: this.response?.byteLength ?? 0, status: this.status, accepted,
          source: this.getResponseHeader("x-silmaril-cache") === "hit" ? "cache-storage" : "http" });
      }
    };
  } else {
    X.send = function () {
      return (this.silDbRead ? checkedSend : send).apply(this, arguments);
    };
  }
  return () => failure;
}

// The worker is optional on hosts that only serve the HTML or on browsers
// without service workers. Its cache survives beyond a single VFS instance.
async function registerPageCache() {
  if (!("serviceWorker" in navigator) || !/^https?:$/.test(location.protocol) || PARAMS.get("cache") === "off") return false;
  try {
    await navigator.serviceWorker.register("explore-sw.js");
    await navigator.serviceWorker.ready;
    if (!navigator.serviceWorker.controller) await new Promise((resolve) => {
      navigator.serviceWorker.addEventListener("controllerchange", resolve, { once: true });
      setTimeout(resolve, 1500);
    });
    return !!navigator.serviceWorker.controller;
  } catch {
    return false;
  }
}

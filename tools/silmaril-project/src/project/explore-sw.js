// Written by sil project explore. Store exact, validated ranges across visits.
"use strict";
const CACHE = "silmaril-explore-db-pages-v3";
self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", (e) => e.waitUntil((async () => {
  for (const k of await caches.keys()) if (k.startsWith("silmaril-explore-db-pages-") && k !== CACHE) await caches.delete(k);
  await self.clients.claim();
})()));

function strongETag(value) {
  return /^"[\x21\x23-\x7e\x80-\xff]*"$/.test(value || "") ? value : null;
}
function versionOf(etag, size) {
  // Preserve every byte of the opaque ETag, including punctuation.
  return etag.slice(1, -1) + "-" + size;
}
function sourceKey(url) {
  const u = new URL(url);
  for (const p of ["__sil_v", "__sil_part", "__sil_range"]) u.searchParams.delete(p);
  return u.href;
}
self.addEventListener("fetch", (e) => {
  const req = e.request;
  if (req.method !== "GET") return;
  const key = new URL(req.url);
  const version = key.searchParams.get("__sil_v");
  const range = req.headers.get("range");
  const want = /^bytes=(\d+)-(\d+)$/.exec(range || "");
  if (!version || key.searchParams.get("__sil_part") !== "0" || !want) return;
  key.searchParams.set("__sil_range", range);

  e.respondWith((async () => {
    const cache = await caches.open(CACHE).catch(() => null);
    const hit = cache && await cache.match(key.href).catch(() => null);
    if (hit) {
      const h = new Headers(hit.headers);
      h.set("content-range", h.get("x-content-range"));
      h.set("x-silmaril-cache", "hit");
      return new Response(hit.body, { status: 206, headers: h });
    }
    const r = await fetch(req);
    const cr = /^bytes (\d+)-(\d+)\/(\d+)$/.exec(r.headers.get("content-range") || "");
    const etag = strongETag(r.headers.get("etag"));
    const enc = r.headers.get("content-encoding");
    const same = cr && etag && versionOf(etag, cr[3]) === version;
    if (r.status !== 206 || !same || cr[1] !== want[1] || cr[2] !== want[2] || (enc && enc !== "identity")) {
      if (!r.status) return r;
      // A host that stops honoring Range could otherwise send the whole DB to
      // the synchronous XHR. Send the response metadata so its guard can report the failure.
      r.body?.cancel().catch(() => {});
      const headers = new Headers(r.headers);
      headers.delete("content-length");
      return new Response(null, { status: r.status, headers });
    }
    if (cache) {
      try {
        const body = await r.clone().arrayBuffer();
        if (body.byteLength === +want[2] - +want[1] + 1) {
          const headers = { "x-content-range": cr[0], "content-type": r.headers.get("content-type") || "application/octet-stream", etag };
          // Cache.put refuses 206 responses. Store as 200 and reconstruct on a hit.
          await cache.put(key.href, new Response(body, { headers }));
          const source = sourceKey(key);
          for (const k of await cache.keys()) {
            if (sourceKey(k.url) === source && new URL(k.url).searchParams.get("__sil_v") !== version) await cache.delete(k);
          }
        }
      } catch {
        // Quota or cache failures leave the validated network response usable.
      }
    }
    return r;
  })());
});

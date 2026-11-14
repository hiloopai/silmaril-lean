// Written by `sil project explore` next to the page (tools/silmaril-project/src/project/explore-sw.js).
// A service worker that keeps the database pages the explorer reads lazily, across reloads.
// It only touches GET requests that carry a Range header and the page's version-tagged query
// (`?v=<version>&part=<n>`); everything else goes to the network untouched. Entries are keyed
// by path, version and range, so pages of two versions are never mixed; when a new version of a
// file is read, the entries of its other versions are deleted.
"use strict";
const CACHE = "silmaril-explore-db-pages-v1";
self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", (e) => e.waitUntil(self.clients.claim()));
self.addEventListener("fetch", (e) => {
  const req = e.request;
  if (req.method !== "GET") return;
  const u = new URL(req.url);
  const v = u.searchParams.get("v"), part = u.searchParams.get("part");
  const range = req.headers.get("range");
  if (!v || part === null || !range) return;
  const key = `${u.origin}${u.pathname}?v=${encodeURIComponent(v)}&part=${encodeURIComponent(part)}&range=${encodeURIComponent(range)}`;
  e.respondWith((async () => {
    const cache = await caches.open(CACHE);
    const hit = await cache.match(key);
    if (hit) {
      const h = new Headers(hit.headers);
      h.set("content-range", h.get("x-content-range") || "");
      h.set("x-silmaril-cache", "hit");
      return new Response(await hit.arrayBuffer(), { status: 206, headers: h });
    }
    const r = await fetch(req);
    if (r.status === 206 && !(r.headers.get("content-encoding") || "").match(/gzip|br|deflate/)) {
      const body = await r.clone().arrayBuffer();
      const h = new Headers({ "x-content-range": r.headers.get("content-range") || "",
        "content-type": r.headers.get("content-type") || "application/octet-stream" });
      // Cache.put refuses 206 responses: store the bytes as a 200 and rebuild the 206 on a hit.
      await cache.put(key, new Response(body, { status: 200, headers: h }));
      for (const k of await cache.keys()) {
        const ku = new URL(k.url);
        if (ku.origin + ku.pathname === u.origin + u.pathname && ku.searchParams.get("v") !== v) await cache.delete(k);
      }
    }
    return r;
  })());
});

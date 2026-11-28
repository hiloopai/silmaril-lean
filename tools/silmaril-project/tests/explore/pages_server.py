"""A static server that behaves like GitHub Pages for the explorer's database (checked against
https://hiloopai.github.io/silmaril-lean/ on 2026-11-13):

* a request that accepts gzip and has no Range gets a gzip body (and a HEAD the gzip length),
  with a weak ETag; this is what hid the file length from sql.js-httpvfs;
* a Range request gets the identity bytes, `206` and `Content-Range: bytes a-b/<length>`, with a
  strong ETag `"<mtime>-<length>"`;
* `Cache-Control: max-age=600` everywhere, and query strings are ignored.

`--validators` changes what names the file's version: `strong` (the above, the default), `weak`
(a weak ETag and Last-Modified), `lastmod` (Last-Modified only, one-second resolution) or `none`,
to test servers that do not name a version reliably.

Every request is logged to the file given by --log as one JSON object per line (method, path,
query, range, status, body bytes), so a test can count transfers.

    python3 -I pages_server.py --root DIR --port 8766 --log requests.jsonl
"""
import argparse
import email.utils
import gzip
import http.server
import json
import os
import urllib.parse


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--port", type=int, default=8766)
    ap.add_argument("--log", required=True)
    ap.add_argument("--validators", choices=["strong", "weak", "lastmod", "none"], default="strong")
    args = ap.parse_args()
    root = os.path.realpath(args.root)

    # Enumerate trusted paths independently of request text. Refresh on a miss
    # so tests can create additional database fixtures while the server runs.
    files = {}
    def refresh_files():
        nonlocal files
        refreshed = {}
        for directory, _, names in os.walk(root):
            for name in names:
                candidate = os.path.join(directory, name)
                resolved = os.path.realpath(candidate)
                if resolved.startswith(root + os.sep) and os.path.isfile(resolved):
                    refreshed["/" + os.path.relpath(candidate, root).replace(os.sep, "/")] = resolved
        files = refreshed
    refresh_files()
    # Static Pages serves an already encoded representation. Reuse it for HEAD
    # and GET until the file changes; ctime also detects writes that restore mtime.
    gzip_bodies = {}

    class H(http.server.BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def record(self, status, n):
            with open(args.log, "a") as f:
                u = urllib.parse.urlsplit(self.path)
                f.write(json.dumps({"method": self.command, "path": u.path, "query": u.query,
                                    "range": self.headers.get("Range"), "status": status,
                                    "bytes": n}) + "\n")

        def serve(self, head):
            u = urllib.parse.urlsplit(self.path)
            key = urllib.parse.unquote(u.path)
            if key.endswith("/"):
                key += "index.html"
            p = files.get(key)
            if p is None:
                refresh_files()
                p = files.get(key)
            if p is None:
                self.send_response(404); self.end_headers(); self.record(404, 0); return
            st = os.stat(p)
            length = st.st_size
            tag = '"%x-%x"' % (int(st.st_mtime), length)
            lastmod = email.utils.formatdate(int(st.st_mtime), usegmt=True)

            def validators(etag):
                if args.validators == "strong":
                    self.send_header("ETag", etag)
                elif args.validators == "weak":
                    self.send_header("ETag", etag if etag.startswith("W/") else "W/" + etag)
                if args.validators in ("weak", "lastmod"):
                    self.send_header("Last-Modified", lastmod)
            ctype = ("text/html; charset=utf-8" if p.endswith(".html") else
                     "text/javascript" if p.endswith(".js") else
                     "text/css" if p.endswith(".css") else
                     "application/json" if p.endswith(".json") else
                     "text/markdown; charset=utf-8" if p.endswith(".md") else
                     "image/svg+xml" if p.endswith(".svg") else
                     "image/png" if p.endswith(".png") else
                     "application/octet-stream")
            rng = self.headers.get("Range")
            gz = "gzip" in (self.headers.get("Accept-Encoding") or "")
            if rng and rng.startswith("bytes="):
                a, _, b = rng[6:].partition("-")
                a = int(a); b = min(int(b) if b else length - 1, length - 1)
                with open(p, "rb") as stream:
                    stream.seek(a)
                    body = stream.read(max(0, b - a + 1))
                self.send_response(206)
                self.send_header("Content-Range", "bytes %d-%d/%d" % (a, b, length))
                validators(tag)
            elif gz:
                version = (st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
                cached = gzip_bodies.get(p)
                if cached is None or cached[0] != version:
                    with open(p, "rb") as stream:
                        cached = (version, gzip.compress(stream.read()))
                    gzip_bodies[p] = cached
                body = cached[1]
                self.send_response(200)
                self.send_header("Content-Encoding", "gzip")
                validators("W/" + tag)
            else:
                with open(p, "rb") as stream:
                    body = stream.read()
                self.send_response(200)
                validators(tag)
            self.send_header("Content-Type", ctype)
            self.send_header("Accept-Ranges", "bytes")
            self.send_header("Cache-Control", "max-age=600")
            self.send_header("Vary", "Accept-Encoding")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            if not head:
                self.wfile.write(body)
            self.record(206 if rng else 200, 0 if head else len(body))

        def do_GET(self):
            self.serve(False)

        def do_HEAD(self):
            self.serve(True)

    http.server.ThreadingHTTPServer(("127.0.0.1", args.port), H).serve_forever()


if __name__ == "__main__":
    main()

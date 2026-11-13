"""A static server that behaves like GitHub Pages for the explorer's database (checked against
https://hiloopai.github.io/silmaril-lean/ on 2026-11-13):

* a request that accepts gzip and has no Range gets a gzip body (and a HEAD the gzip length),
  with a weak ETag; this is what hid the file length from sql.js-httpvfs;
* a Range request gets the identity bytes, `206` and `Content-Range: bytes a-b/<length>`, with a
  strong ETag `"<mtime>-<length>"`;
* `Cache-Control: max-age=600` everywhere, and query strings are ignored.

Every request is logged to the file given by --log as one JSON object per line (method, path,
query, range, status, body bytes), so a test can count transfers.

    python3 -I pages_server.py --root DIR --port 8766 --log requests.jsonl
"""
import argparse
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
    args = ap.parse_args()
    root = os.path.abspath(args.root)

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
            p = os.path.normpath(os.path.join(root, urllib.parse.unquote(u.path).lstrip("/") or "index.html"))
            if not p.startswith(root) or not os.path.isfile(p):
                self.send_response(404); self.end_headers(); self.record(404, 0); return
            data = open(p, "rb").read()
            st = os.stat(p)
            tag = '"%x-%x"' % (int(st.st_mtime), len(data))
            ctype = ("text/html; charset=utf-8" if p.endswith(".html") else
                     "text/javascript" if p.endswith(".js") else "application/octet-stream")
            rng = self.headers.get("Range")
            gz = "gzip" in (self.headers.get("Accept-Encoding") or "")
            if rng and rng.startswith("bytes="):
                a, _, b = rng[6:].partition("-")
                a = int(a); b = min(int(b) if b else len(data) - 1, len(data) - 1)
                body = data[a:b + 1]
                self.send_response(206)
                self.send_header("Content-Range", "bytes %d-%d/%d" % (a, b, len(data)))
                self.send_header("ETag", tag)
            elif gz:
                body = gzip.compress(data)
                self.send_response(200)
                self.send_header("Content-Encoding", "gzip")
                self.send_header("ETag", "W/" + tag)
            else:
                body = data
                self.send_response(200)
                self.send_header("ETag", tag)
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

#!/usr/bin/env python3
"""Helpers for the demangler corpus test (no third-party modules; run with python3 -I).

  symbols.py wat SYMS OUT.wat      a module with one function per symbol, named by it
  symbols.py names IN.wasm         print the function names of IN.wasm's name section, one per line
"""
import sys

def leb(b, i):
    r = s = 0
    while True:
        x = b[i]; i += 1; r |= (x & 127) << s; s += 7
        if x < 128:
            return r, i

def wat(syms, out):
    def esc(s):
        return "".join(c if 32 <= ord(c) < 127 and c not in '"\\' else "".join("\\%02x" % b for b in c.encode()) for c in s)
    with open(out, "w") as f:
        f.write("(module\n")
        for s in syms:
            f.write('  (func $"%s")\n' % esc(s))
        f.write(")\n")

def names(path):
    b = open(path, "rb").read()
    i = 8
    while i < len(b):
        sid = b[i]; i += 1
        n, i = leb(b, i)
        body = b[i:i + n]; i += n
        if sid != 0:
            continue
        nl, j = leb(body, 0)
        if body[j:j + nl] != b"name":
            continue
        j += nl
        while j < len(body):
            ss = body[j]; j += 1
            sz, j = leb(body, j)
            data = body[j:j + sz]; j += sz
            if ss == 1:
                k, p = leb(data, 0)
                for _ in range(k):
                    _, p = leb(data, p)
                    l, p = leb(data, p)
                    print(data[p:p + l].decode("utf-8", "replace"))
                    p += l

if __name__ == "__main__":
    if sys.argv[1] == "wat":
        wat([l.rstrip("\n") for l in open(sys.argv[2], encoding="utf-8") if l.strip()], sys.argv[3])
    elif sys.argv[1] == "names":
        names(sys.argv[2])

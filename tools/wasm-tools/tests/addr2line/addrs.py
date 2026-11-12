#!/usr/bin/env python3
"""Addresses for the addr2line differential test (python3 -I, standard library only).

  addrs.py FILE STEP [--relative]

Prints addresses inside the code section of every core module of FILE (the outer module or
the modules nested in a component), one per line: every STEP-th byte from the start of the
code section's contents to its end, plus both ends; hexadecimal (`0x…`, and every third one
as `@…`), or decimal offsets from the code section with --relative (single-module files).
"""
import sys

def leb(b, i):
    r = s = 0
    while True:
        x = b[i]; i += 1; r |= (x & 127) << s; s += 7
        if x < 128:
            return r, i

def modules(b, start, end, out):
    comp = b[start + 4:start + 8] == b"\x0d\x00\x01\x00"
    i = start + 8
    while i < end:
        sid = b[i]; n, j = leb(b, i + 1)
        if comp and sid in (1, 4):
            modules(b, j, j + n, out)
        elif not comp and sid == 10:
            out.append((j, j + n))
        i = j + n

b = open(sys.argv[1], "rb").read()
step = int(sys.argv[2])
rel = "--relative" in sys.argv
mods = []
modules(b, 0, len(b), mods)
k = 0
for (a, e) in mods:
    for x in list(range(a, e, step)) + [e - 1, e]:
        k += 1
        if rel:
            print(x - a)
        elif k % 3 == 0:
            print("@%x" % x)
        else:
            print("0x%x" % x)

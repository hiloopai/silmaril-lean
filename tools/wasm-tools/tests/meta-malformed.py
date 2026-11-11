#!/usr/bin/env python3
"""Malformed-binary differential test of `metadata show`, `metadata add` and `demangle` (run with python3 -I).

  meta-malformed.py UPSTREAM OURS N SEED FILE...

Derives N inputs from the seed binaries FILE... by deterministic mutations (truncation, byte
flips, inserted and deleted bytes, LEB128 size fields grown or shrunk, nested-section headers
damaged), runs `metadata show`, `metadata add --name x --language a=1` and `demangle` on each with both binaries, and compares the exit
code, stdout and stderr byte for byte (error messages include wasmparser's offsets). Prints a
summary and the first differences; exit 1 when any case differs (a case where upstream
panics and ours exits 1 with an error message is counted apart, not as a difference).
"""
import os, random, subprocess, sys, tempfile

def mutate(rng, b):
    b = bytearray(b)
    k = rng.randrange(7)
    if k == 0 and len(b) > 8:
        return bytes(b[:rng.randrange(8, len(b))])
    if k == 1 and len(b) > 8:
        for _ in range(rng.randrange(1, 4)):
            i = rng.randrange(8, len(b)); b[i] = rng.randrange(256)
        return bytes(b)
    if k == 2 and len(b) > 8:
        i = rng.randrange(8, len(b)); b[i:i] = bytes([rng.randrange(256)])
        return bytes(b)
    if k == 3 and len(b) > 9:
        i = rng.randrange(8, len(b)); del b[i]
        return bytes(b)
    if k == 4 and len(b) > 9:
        # a section size field: walk to a random section and change its size
        secs = []
        i = 8
        while i < len(b):
            sid = b[i]; j = i + 1; n = 0; s = 0
            while j < len(b):
                x = b[j]; j += 1; n |= (x & 127) << s; s += 7
                if x < 128 or s > 35: break
            secs.append((i, j, n))
            i = j + n
        if secs:
            i, j, n = rng.choice(secs)
            n2 = max(0, n + rng.choice([-3, -2, -1, 1, 2, 3, 100]))
            enc = bytearray()
            while True:
                x = n2 & 127; n2 >>= 7
                if n2: enc.append(x | 128)
                else: enc.append(x); break
            b[i + 1:j] = enc
        return bytes(b)
    if k == 5 and len(b) > 9:
        i = rng.randrange(8, len(b)); b[i] = rng.choice([0x80, 0xff, 0x00, 0x0a, 0x0b, 0x0c, 0x01, 0x04])
        return bytes(b)
    if len(b) > 16:
        i = rng.randrange(8, len(b) - 4); b[i:i + 4] = b"\0asm"
    return bytes(b)

def run(binary, args, path):
    p = subprocess.run([binary] + args + [path], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       stdin=subprocess.DEVNULL, env={k: v for k, v in os.environ.items() if k != "COLUMNS"})
    return p.returncode, p.stdout, p.stderr

def main():
    up, ours, n, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    seeds = [open(f, "rb").read() for f in sys.argv[5:]]
    seeds = [s for s in seeds if len(s) < 200000]
    rng = random.Random(seed)
    same = diff = 0; firsts = []
    errs_same = 0; crashes = 0
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "in.wasm")
        for t in range(n):
            data = mutate(rng, rng.choice(seeds))
            if rng.random() < 0.3:
                data = mutate(rng, data)
            open(path, "wb").write(data)
            for args in (["metadata", "show"], ["demangle", "-o", os.path.join(d, "out.wasm")],
                         ["metadata", "add", "--name", "x", "--language", "a=1", "-o", os.path.join(d, "out.wasm")]):
                a = run(up, args, path)
                if "-o" in args:
                    ua = open(os.path.join(d, "out.wasm"), "rb").read() if a[0] == 0 else b""
                b = run(ours, args, path)
                if "-o" in args:
                    ub = open(os.path.join(d, "out.wasm"), "rb").read() if b[0] == 0 else b""
                    a = a + (ua,); b = b + (ub,)
                if a == b:
                    same += 1
                    if a[0] != 0: errs_same += 1
                elif (a[0] < 0 or b"panicked at" in a[2]) and b[0] == 1 and b[2].startswith(b"error: "):
                    # upstream crashes (e.g. `metadata add` slicing a code section that runs
                    # past the end of the input, rewrite.rs:172); ours reports the error
                    crashes += 1
                else:
                    diff += 1
                    if len(firsts) < 15:
                        firsts.append((t, " ".join(args[:2]), a[0], b[0], a[2][:200], b[2][:200]))
                        open(os.path.join(os.environ.get("MALFORMED_KEEP", d), "diff-%d.wasm" % t), "wb").write(data) if os.environ.get("MALFORMED_KEEP") else None
    print("meta-malformed: %d cases identical (%d of them errors), %d where upstream crashes and ours reports an error, %d different"
          % (same, errs_same, crashes, diff))
    for f in firsts:
        print("  case %d %s: exit %d vs %d\n    up:   %r\n    ours: %r" % f)
    sys.exit(1 if diff else 0)

main()

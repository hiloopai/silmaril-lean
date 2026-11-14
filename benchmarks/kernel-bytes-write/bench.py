#!/usr/bin/env python3
"""Kernel-check time of reads after n writes on 1 MiB of kernel bytes (README.md).

Run from the repository root after `lake build Silmaril.Prelude.Bytes.Write.Thms`:
    python3 -I benchmarks/kernel-bytes-write/bench.py [n ...]
Each case is one `decide +kernel` of four `readLE` facts after `n` 8-byte writes at
pseudo-random offsets; the expected values come from a Python model of the same writes.
"""
import os, subprocess, sys, tempfile, time

N = 1 << 20
BASES = ["zerosCanon 4096 1048576", "zeros 1048576"]
OPS = ["write", "ropeWrite"]


def model(n):
    m = bytearray(N)
    for k in range(n - 1, -1, -1):  # `go` applies the write of index k = n-1, …, 0
        p = (k * 40503) % 1048000
        m[p:p + 8] = k.to_bytes(8, "little")
    return m


def source(base, op, n):
    m = model(n)
    pos = [(k * 40503) % 1048000 for k in (0, n // 3, n // 2, n - 1)]
    facts = " ∧ ".join(
        f"t.readLE {p} 8 = some {int.from_bytes(m[p:p + 8], 'little')}" for p in pos)
    return f"""import Silmaril.Prelude.Bytes.Write.Thms
open Silmaril Silmaril.KBytes
def go : Nat → KBytes → KBytes
  | 0, t => t
  | k + 1, t => go k (t.{op} ((k * 40503) % 1048000) 8 k)
set_option maxRecDepth 100000 in
example : (let t := go {n} ({base}); {facts}) := by decide +kernel
"""


def main():
    ns = [int(a) for a in sys.argv[1:]] or [64, 256, 1024]
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, "Bench.lean")
        print("base\top\tn\tseconds\tresult")
        for base in BASES:
            for op in OPS:
                for n in ns:
                    with open(f, "w") as h:
                        h.write(source(base, op, n))
                    s = time.time()
                    r = subprocess.run(["timeout", "300", "lake", "env", "lean", f],
                                       capture_output=True, text=True)
                    e = time.time() - s
                    ok = "ok" if r.returncode == 0 else (r.stdout + r.stderr).strip()[:80]
                    print(f"{base}\t{op}\t{n}\t{e:.2f}\t{ok}", flush=True)


if __name__ == "__main__":
    main()

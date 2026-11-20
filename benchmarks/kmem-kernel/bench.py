#!/usr/bin/env python3
"""Wall time and peak RSS of `lake env lean` on the KMem end-to-end acceptance module and on a
ByteArray comparison file.

Usage (from the repository root, after
`lake build Silmaril.Wasi.Component.Accept.Ref.KMem.Examples`):
    python3 -I benchmarks/kmem-kernel/bench.py [timeout-seconds]

Cases:
* `kmem`: `Silmaril/Wasi/Component/Accept/Ref/KMem/Examples.lean` (`runHiK_true` by
  `decide +kernel` over `core3K neverFail`, then `acceptedK_hi`, `hi_mem_of_progRel`, `hi_mem`).
* `bytearray`: a generated file checking `runHi = true` (the same run over the `ByteArray`
  engine `core3 neverFail`) by `decide +kernel`. It is expected to fail: the kernel gives up on
  the 64 KiB `ByteArray` memory. It is a measurement, not a test; CI does not run it.

Prints one TSV row per case: case, exit code, wall seconds, peak RSS (GB, the largest
resident set of the `lake`/`lean` process tree, from `getrusage(RUSAGE_CHILDREN)`), status.
Each case runs in a fresh Python child so the RSS figures do not mix.
"""
import os, subprocess, sys, tempfile, time

KMEM = "Silmaril/Wasi/Component/Accept/Ref/KMem/Examples.lean"
BYTEARRAY = r'''import Silmaril.Wasi.Component.Accept.Ref.Examples
open Silmaril.Wasi.Accept.Ref.Examples
/-- `runHi` (the `ByteArray` engine `core3 neverFail`) in the kernel. -/
example : runHi = true := by decide +kernel
'''

def measure(path, limit):
    """Run `lake env lean path`; return exit code, wall seconds, peak RSS (KiB), output."""
    import resource
    t0 = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                           timeout=limit)
        code, out = r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        code, out = "timeout", f"script timeout ({limit} s)"
    wall = time.time() - t0
    return code, wall, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss, out

def status(code, out):
    if code == 0:
        return "ok"
    for line in out.splitlines():
        if "error" in line or "timeout" in line:
            return line.split("error:", 1)[-1].strip()[:160]
    return (out.strip().splitlines() or ["failed"])[0][:160]

def child(path, limit):
    code, wall, rss, out = measure(path, limit)
    print(f"{code}\t{wall:.1f}\t{rss / 1048576:.2f}\t{status(code, out)}", flush=True)

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--child":
        child(sys.argv[2], int(sys.argv[3]))
        return
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 900
    print("case\texit\twall_s\tpeak_rss_gb\tstatus", flush=True)
    with tempfile.TemporaryDirectory() as d:
        bytes_path = os.path.join(d, "ByteArrayHi.lean")
        with open(bytes_path, "w") as fh:
            fh.write(BYTEARRAY)
        for name, path in [("kmem", KMEM), ("bytearray", bytes_path)]:
            r = subprocess.run([sys.executable, "-I", os.path.abspath(__file__), "--child", path,
                                str(limit)], capture_output=True, text=True)
            row = (r.stdout.strip() or r.stderr.strip()).replace(d, "<tmp>")
            print(f"{name}\t{row}", flush=True)

if __name__ == "__main__":
    main()

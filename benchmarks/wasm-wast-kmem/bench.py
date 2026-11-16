#!/usr/bin/env python3
"""Wall time and peak RSS of the kernel check of each `address.wast` module, on `KMem` stores
(`scriptKM`, as the generated rows use it) and on `ByteArray` stores (`scriptK`).

Usage (from the repository root, after `lake build Silmaril.Project.WasmWast.Address.Defs
Silmaril.Project.Shapes.WasmWast.Thms`):
    python3 -I benchmarks/wasm-wast-kmem/bench.py [timeout-seconds] [case ...]

Cases (all by default):
* `imports`: a file with only the imports below (the fixed cost of every other case).
* `kmemJ` (J = 0..3): `ScriptHolds neverFail mJ cmdsJ` by `ScriptHolds.of_kernelKM` and
  `decide +kernel`: decode, validate, instantiate (with the data segments) and run every
  command of `cmdsJ` on `KMem` stores. This is the check of `scriptJ` in
  `Silmaril/Project/WasmWast/Address/Thms.lean`.
* `bytesJ`: the same with `ScriptHolds.of_kernel` (`scriptK`, `ByteArray` stores). Expected to
  fail; a measurement, not a test. CI does not run this script.

Prints one TSV row per case: case, exit code, wall seconds, peak RSS (GB, the largest resident
set of the `lake`/`lean` process tree, from `getrusage(RUSAGE_CHILDREN)`), status. Each case runs
in a fresh Python child so the RSS figures do not mix.
"""
import os, subprocess, sys, tempfile, time

HEAD = """import Silmaril.Project.WasmWast.Address.Defs
import Silmaril.Project.Shapes.WasmWast.Thms
open Silmaril.Project.WasmWast.Address Silmaril.Project.Shapes.WasmWast
"""

def case_text(name):
    if name == "imports":
        return HEAD
    kind, j = name[:-1], name[-1]
    thm = "of_kernelKM" if kind == "kmem" else "of_kernel"
    return HEAD + (f"theorem t : ScriptHolds Silmaril.Wasm.SingleThreaded.neverFail m{j} cmds{j} :=\n"
                   f"  .{thm} (fuel := 100000) (by decide +kernel)\n")

CASES = ["imports"] + [f"kmem{j}" for j in range(4)] + [f"bytes{j}" for j in range(4)]

def measure(path, limit):
    import resource
    t0 = time.time()
    import signal
    p = subprocess.Popen(["lake", "env", "lean", path], stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        out, _ = p.communicate(timeout=limit)
        code = p.returncode
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)  # lake and its lean child
        p.communicate()
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
    cases = sys.argv[2:] or CASES
    print("case\texit\twall_s\tpeak_rss_gb\tstatus", flush=True)
    with tempfile.TemporaryDirectory() as d:
        for name in cases:
            path = os.path.join(d, f"{name}.lean")
            with open(path, "w") as fh:
                fh.write(case_text(name))
            r = subprocess.run([sys.executable, "-I", os.path.abspath(__file__), "--child", path,
                                str(limit)], capture_output=True, text=True)
            row = (r.stdout.strip() or r.stderr.strip()).replace(d, "<tmp>")
            print(f"{name}\t{row}", flush=True)

if __name__ == "__main__":
    main()

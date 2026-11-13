#!/usr/bin/env python3
"""Kernel benchmarks of the memory representations (docs/projects/wasm-kernel-eval.md).

One Lean file per case, one `decide +kernel` each, elaborated with `lake env lean` and the
profiler. Records the kernel ("type checking") time, wall time and the peak resident memory of
the Lean process. Usage: python3 -I benchmarks/wasm-kernel-eval/mem_bench.py [-o out.json]
[--timeout S] [--only SUBSTRING]
"""
import argparse, json, os, re, subprocess, tempfile, time

HEAD = """import Silmaril.Wasm.KernelEval.Examples
import Silmaril.Wasm.KernelEval.Memories
import Silmaril.Wasm.KernelEval.CoreMem
open Silmaril.Wasm.KernelEval Examples
set_option profiler true
set_option profiler.threshold 0
set_option maxRecDepth 100000
"""

def reps(size):
    pb = 12 if size >= 4096 else 8
    d = (size >> pb).bit_length() - 1
    r = {
        "ListMem": f"(⟨List.replicate {size} 0⟩ : ListMem)",
        "KMem (Verify.Kernel fload/fstore)": f"(KMem.zeros {size})",
        "NatMem": f"(NatMem.zeros {size})",
        "Overlay(NatMem)": f"(Overlay.ofBase (NatMem.zeros {size}))",
        f"PageMem {2 ** pb // 1024 or 2 ** pb}{'KiB' if pb >= 10 else 'B'} pages": f"(PageMem.zeros {pb} {d})",
    }
    if size <= 256:
        r["CoreMem (Memory.load/store)"] = f"(CoreMem.mk ⟨Array.replicate {size} 0⟩)"
    return r

def workloads():
    w = []
    w.append(("fillSort 8", 256, lambda m: f"returns 10000000 fillSort (fillSortLocals 8) {m} 9 = true"))
    w.append(("fillSort 16", 65536, lambda m: f"returns 10000000 fillSort (fillSortLocals 16) {m} 17 = true"))
    for size in (65536, 1048576):
        s = size // 128 - 4
        w.append((f"scatter 128", size, lambda m, s=s: f"returns 10000000 scatter (scatterLocals 128 {s}) {m} 8128 = true"))
    for size in (65536, 1048576):
        s = size // 200 - 4
        w.append(("updates 200", size, lambda m, s=s: f"(updates {m} 200 {s} == some 0) = true"))
    for size in (65536, 1048576):
        s = size // 64 - 4
        w.append(("sharing 64", size, lambda m, s=s: f"sharingCheck (fillWords {m} 64) ((List.range 64).map (· * {s})) 8 = true"))
    return w

ENV = dict(os.environ, LEAN_PATH=subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
    capture_output=True, text=True, check=True).stdout.strip())

TIME = re.compile(r"^\s*type checking\s+([\d.]+)(ms|s)\s*$")

def run_case(src, timeout):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(src); path = f.name
    t0 = time.time()
    # `lean` directly (not under `lake env`), so that `wait4` reports its own peak memory.
    with tempfile.TemporaryFile("w+") as log:
        p = subprocess.Popen(["lean", path], stdout=log, stderr=subprocess.STDOUT, env=ENV)
        timed_out = False
        while True:
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid:
                break
            if time.time() - t0 > timeout:
                p.kill(); _, status, ru = os.wait4(p.pid, 0); timed_out = True; break
            time.sleep(0.05)
        rss = ru.ru_maxrss
        log.seek(0); out = log.read()
    ok = not timed_out and os.waitstatus_to_exitcode(status) == 0
    if timed_out: out = "timeout"
    wall = time.time() - t0
    os.unlink(path)
    kernel = None
    for line in out.splitlines():
        m = TIME.match(line)
        if m: kernel = float(m.group(1)) * (1000 if m.group(2) == "s" else 1)
    errs = [l for l in out.splitlines() if "error" in l]
    err = None if ok else ("timeout" if out == "timeout" else (errs or out.strip().splitlines())[-1][:200])
    return {"ok": ok, "kernel_ms": kernel, "wall_s": round(wall, 2),
            "max_rss_mb": round(rss / 1024), "error": err}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-o"); ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--only", default=None)
    a = ap.parse_args()
    res = []
    base = run_case(HEAD + "example : True := trivial\n", a.timeout)
    base.update(workload="baseline (imports only)", size=0, rep="-")
    res.append(base); print(json.dumps(base), flush=True)
    for name, size, goal in workloads():
        for rep, m in reps(size).items():
            if a.only and a.only not in f"{name} {rep}": continue
            r = run_case(HEAD + f"example : {goal(m)} := by decide +kernel\n", a.timeout)
            r.update(workload=name, size=size, rep=rep)
            res.append(r); print(json.dumps(r), flush=True)
    if a.o: json.dump(res, open(a.o, "w"), indent=1)

if __name__ == "__main__":
    main()

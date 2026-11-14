#!/usr/bin/env python3
"""Kernel-evaluation benchmarks for Silmaril.Wasm.KernelEval (docs/projects/wasm-kernel-eval.md).

Each case is one Lean file with one `example`, elaborated with `lake env lean` and the profiler;
the reported time is Lean's "type checking" (kernel) plus "elaboration"/"tactic execution"
for the goal. `--native` also runs `native_decide` cases: those files are generated in a
scratch directory only (native_decide is not allowed in this repository).

Usage: python3 -I benchmarks/wasm-kernel-eval/bench.py [--native] [--quick] [-o out.json]
"""
import argparse, json, os, re, subprocess, sys, tempfile, time

HEAD = """import Silmaril.Wasm.KernelEval.Examples
open Silmaril.Wasm.KernelEval Examples
set_option profiler true
set_option profiler.threshold 0
set_option maxRecDepth 100000
def chk {M} (r : Result M) (v : BitVec 32) : Bool := match r.top? with | some w => w == v | none => false
"""

def expected_sum(n): return (n * (n - 1) // 2) % 2**32
def expected_sort(n): return 1 + n

def prog(kind, n, mem, page):
    size = 65536 if page else 4 * n
    if kind == "sumTo":
        return f"sumTo (sumToLocals {n})", expected_sum(n), "(NatMem.zeros 0)" if mem == "nat" else "(listZeros 0)"
    m = f"(NatMem.zeros {size})" if mem == "nat" else f"(listZeros {size})"
    return f"fillSort (fillSortLocals {n})", expected_sort(n), m

def case_src(kind, n, mem, driver, tactic, page):
    body, v, m = prog(kind, n, mem, page)
    code, locs = body.split(" ", 1)
    fuel = 50_000_000
    goal = f"chk ({driver} {fuel} (Config.init {code} {locs} {m})) {v} = true"
    tac = {"kernel": "by decide +kernel", "decide": "by decide", "native": "by native_decide",
           "rfl": "rfl"}[tactic]
    return HEAD + f"example : {goal} := {tac}\n"

TIME = re.compile(r"^\s*(type checking|elaboration|tactic execution|compilation|interpretation)\s+([\d.]+)(ms|s)\s*$")
INTERP = re.compile(r"^interpretation of .* took ([\d.]+)(ms|s)\s*$")

def run_case(src, timeout):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=tempfile.gettempdir()) as f:
        f.write(src); path = f.name
    t0 = time.time()
    try:
        p = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True, timeout=timeout)
        out, ok = p.stdout + p.stderr, p.returncode == 0
    except subprocess.TimeoutExpired:
        out, ok = "timeout", False
    wall = time.time() - t0
    os.unlink(path)
    times = {}
    for line in out.splitlines():
        mt = TIME.match(line)
        if mt:
            times[mt.group(1)] = float(mt.group(2)) * (1000 if mt.group(3) == "s" else 1)
        mi = INTERP.match(line)
        if mi:
            times["native evaluation"] = float(mi.group(1)) * (1000 if mi.group(2) == "s" else 1)
    err = None if ok else ("timeout" if out == "timeout" else out.strip().splitlines()[-1][:200])
    return {"ok": ok, "wall_s": round(wall, 2), "times_ms": times, "error": err}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--native", action="store_true")
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--tactic", default=None, help="run only cases with this tactic")
    ap.add_argument("-o", default=None)
    a = ap.parse_args()
    cases = []
    sizes_sum = [100, 1000] if a.quick else [100, 1000, 10000]
    sizes_sort = [8, 16] if a.quick else [8, 16, 32, 64]
    for n in sizes_sum:
        for drv in ["runRec", "run"]:
            cases.append(("sumTo", n, "nat", drv, "kernel", False))
        cases.append(("sumTo", n, "nat", "runRec", "decide", False))
    for n in sizes_sort:
        for mem in ["nat", "list"]:
            for page in [False, True]:
                cases.append(("fillSort", n, mem, "runRec", "kernel", page))
    if a.native:
        for n in sizes_sum: cases.append(("sumTo", n, "nat", "runRec", "native", False))
        for n in sizes_sort: cases.append(("fillSort", n, "nat", "runRec", "native", True))
    if a.tactic:
        cases = [c for c in cases if c[4] == a.tactic]
    results = []
    for c in cases:
        r = run_case(case_src(*c), a.timeout)
        r.update(dict(zip(["prog", "n", "mem", "driver", "tactic", "page"], c)))
        results.append(r)
        print(json.dumps(r), flush=True)
    if a.o:
        json.dump(results, open(a.o, "w"), indent=1)

if __name__ == "__main__":
    main()

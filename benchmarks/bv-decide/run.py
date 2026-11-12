#!/usr/bin/env python3
"""Time `bv_decide` against its kernel-checked alternatives on fixed goals.

Each case is one standalone Lean file importing only `Std.Tactic.BVDecide`; the
wall time of `lean FILE` (startup included, about 0.23 s) is recorded with the
axioms of the resulting theorem. Run with the repository toolchain:

    python3 -I benchmarks/bv-decide/run.py --out results.json [--lean "lean"] [--reps 3]

`--lean "lean +leanprover/lean4-pr-releases:pr-release-12509"` with
`--tactics native,cbv` measures the upstream `bv_decide -native` experiment.
"""
import argparse, json, re, shlex, subprocess, sys, tempfile, time, pathlib

GOALS = {
    # Silmaril.X86.Float.State: lane and byte-image identities.
    "setLane32": "(v : BitVec 128) (x : BitVec 32) : (v.extractLsb' 32 96 ++ x : BitVec 128).extractLsb' 0 32 = x",
    "zeroLane64": "(x : BitVec 64) : (x.setWidth 128).extractLsb' 0 64 = x",
    "le32": "(v : BitVec 32) : v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v",
    "le64": "(v : BitVec 64) : v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++ v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v",
    # Rewriting closes these.
    "addsub64": "(x y : BitVec 64) : x + y - y = x",
    # These need the SAT stage.
    "xorswap32": "(x y : BitVec 32) : (x ^^^ y) ^^^ y = x",
    "lowbit8": "(x : BitVec 8) : (x &&& (x - 1)) = 0 → (x &&& -x) = x",
    "lowbit32": "(x : BitVec 32) : (x &&& (x - 1)) = 0 → (x &&& -x) = x",
    "avg32": "(x y : BitVec 32) : (x &&& y) + ((x ^^^ y) >>> 1) = ((x.setWidth 33 + y.setWidth 33) >>> 1).setWidth 32",
    "mulcomm8": "(x y : BitVec 8) : x * y = y * x",
    "mulcomm16": "(x y : BitVec 16) : x * y = y * x",
    "muldist8": "(x y z : BitVec 8) : x * (y + z) = x * y + x * z",
}
# Kernel enumeration of the whole domain, for small widths only.
DECIDE = {
    "lowbit8": "∀ x : BitVec 8, (x &&& (x - 1)) = 0 → (x &&& -x) = x",
    "mulcomm8": "∀ x y : BitVec 8, x * y = y * x",
    "muldist4": "∀ x y z : BitVec 4, x * (y + z) = x * y + x * z",
}
TACTICS = {
    "bv_decide": "bv_decide",
    "bv_normalize": "bv_normalize",
    "native": "bv_decide",
    "cbv": "bv_decide -native",
}
HEADER = "import Std.Tactic.BVDecide\nset_option maxHeartbeats 20000000\nset_option maxRecDepth 1000000\n"


def cases(tactics):
    for g, stmt in GOALS.items():
        for t in tactics:
            if t == "decide_kernel":
                if g in DECIDE:
                    yield g, t, f"theorem T : {DECIDE[g]} := by decide +kernel\n"
            else:
                yield g, t, f"theorem T {stmt} := by {TACTICS[t]}\n"
    if "decide_kernel" in tactics:
        yield "muldist4", "decide_kernel", f"theorem T : {DECIDE['muldist4']} := by decide +kernel\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--tactics", default="bv_decide,bv_normalize,decide_kernel")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    lean = shlex.split(a.lean)
    version = subprocess.run(lean + ["--version"], capture_output=True, text=True).stdout.strip()
    rows = []
    with tempfile.TemporaryDirectory() as d:
        for goal, tactic, body in cases(a.tactics.split(",")):
            f = pathlib.Path(d) / f"{goal}__{tactic}.lean"
            f.write_text(HEADER + body + "#print axioms T\n")
            times, out, rc = [], "", None
            for _ in range(a.reps):
                start = time.monotonic()
                try:
                    p = subprocess.run(lean + [str(f)], capture_output=True, text=True, timeout=a.timeout)
                    out, rc = p.stdout + p.stderr, p.returncode
                except subprocess.TimeoutExpired:
                    out, rc = "timeout", -1
                times.append(round(time.monotonic() - start, 3))
            m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
            axioms = [x.strip() for x in m.group(1).split(",")] if m else []
            err = re.search(r"error: (.*)", out)
            row = {
                "goal": goal, "tactic": tactic, "ok": rc == 0, "seconds_min": min(times),
                "seconds": times,
                "native_axiom": any("_native" in x for x in axioms),
                "axioms": [re.sub(r"^T\._native\.bv_decide\.ax_.*", "T._native.bv_decide.ax_…", x) for x in axioms],
                "error": err.group(1)[:160] if err and rc != 0 else None,
            }
            rows.append(row)
            print(f"{goal:11s} {tactic:13s} ok={row['ok']!s:5s} {row['seconds_min']:7.2f}s"
                  f" native_axiom={row['native_axiom']!s:5s} {row['error'] or ''}", file=sys.stderr)
    json.dump({"lean": version, "lean_command": a.lean, "reps": a.reps, "rows": rows},
              open(a.out, "w"), indent=1, ensure_ascii=False)


if __name__ == "__main__":
    main()

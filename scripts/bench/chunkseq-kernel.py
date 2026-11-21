#!/usr/bin/env python3
"""Kernel/displayed-term workload for canonical ChunkSeq; run from the repo root."""
from pathlib import Path
import argparse
import re
import subprocess
import sys
import tempfile

HEADER = """import Lean.Elab.Tactic
import Silmaril.Prelude.ChunkSeq.Balanced.Thms
open Silmaril.ChunkSeq.Balanced Lean Elab Term Meta
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
elab "#kernel_time " claim:term : command => Command.liftTermElabM do
  let proposition ← elabType claim
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let inst ← instantiateMVars (← synthInstance (mkApp (Lean.mkConst ``Decidable) proposition))
  let proof := mkApp3 (Lean.mkConst ``of_decide_eq_true) proposition inst
    (mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true))
  let name ← mkFreshUserName `bench
  let start ← IO.monoNanosNow
  addDecl (.thmDecl { name, levelParams := [], type := proposition, value := proof })
  let elapsed := (← IO.monoNanosNow) - start
  logInfo m!"KERNEL_MS {elapsed.toFloat / 1e6}"
"""


def tree(values, start, count):
    if not count:
        return ".empty"
    left = (1 << ((count + 1).bit_length() - 1)) - 1
    if left == count:
        left //= 2
    mid = start + left
    return (f"(.node {count} {tree(values, start, left)} {values(mid)} "
            f"{tree(values, mid + 1, count - left - 1)})")


def literals(values):
    return "#[" + ",".join(map(str, values)) + "]"


def main():
    args = argparse.ArgumentParser()
    args.add_argument("--sizes", default="100,1000,10000")
    args.add_argument("--seconds", type=int, default=20)
    args.add_argument("--runs", type=int, default=1)
    args.add_argument("--widths", default="0,1,32")
    options = args.parse_args()
    print("variant,n,phase,run,exit,kernel_ms,wall_s,max_rss_kib,olean_bytes", flush=True)
    with tempfile.TemporaryDirectory() as scratch:
        target = Path(scratch, "SequenceProbe.lean")
        artifact = Path(scratch, "SequenceProbe.olean")
        timing = Path(scratch, "time")
        for count in map(int, options.sizes.split(",")):
            for width in map(int, options.widths.split(",")):
                variant = "node" if width == 0 else f"chunk{width}"
                if width == 0:
                    raw, material = "Tree Nat", tree(str, 0, count)
                    init = f"Tree.ofList (List.range {count})"
                    index = lambda expr, pos: f"({expr}).get? {pos}"
                    push = lambda expr: f"({expr}).push {count}"
                else:
                    raw = "Chunks Nat"
                    head = tree(lambda i: literals(range(i * width, (i + 1) * width)), 0, count // width)
                    tail = literals(range(count - count % width, count))
                    material = f"⟨{head}, {tail}⟩"
                    init = f"Chunks.ofList {width - 1} (List.range {count})"
                    index = lambda expr, pos: f"({expr}).get? {width - 1} {pos}"
                    push = lambda expr: f"({expr}).push {width - 1} {count}"
                cases = [
                    ("literal-declare", f"def data : {raw} := {material}\n", ""),
                    ("literal-late", f"def data : {raw} := {material}\n", f"{index('data', count-1)} = some {count-1}"),
                    ("literal-insert", f"def data : {raw} := {material}\n", f"{index(push('data'), count)} = some {count}"),
                    ("build-and-late", "", f"{index(init, count-1)} = some {count-1}"),
                ]
                for phase, declaration, claim in cases:
                    checks = f"#kernel_time 1 = 1\n#kernel_time {claim}\n" if claim else ""
                    target.write_text(HEADER + declaration + checks, encoding="utf-8")
                    for run in range(options.runs):
                        artifact.unlink(missing_ok=True)
                        flags = ["-o", str(artifact)] if not claim else []
                        result = subprocess.run(["/usr/bin/time", "-f", "%e,%M", "-o", str(timing),
                                                 "timeout", str(options.seconds), "lake", "env", "lean", "-j1",
                                                 "-s32768", "-M4096", f"--root={scratch}", *flags, str(target)],
                                                capture_output=True, text=True, check=False)
                        matches = re.findall(r"KERNEL_MS ([\d.]+)", result.stdout)
                        kernel = matches[-1] if len(matches) == 2 else ""
                        size = artifact.stat().st_size if artifact.exists() else ""
                        print(f"{variant},{count},{phase},{run+1},{result.returncode},{kernel},"
                              f"{timing.read_text().strip().splitlines()[-1]},{size}", flush=True)
                        if result.returncode not in (0, 124):
                            print(f"{variant},{count},{phase}: {result.stdout}{result.stderr}", file=sys.stderr)


if __name__ == "__main__":
    main()

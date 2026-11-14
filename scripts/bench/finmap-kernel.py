#!/usr/bin/env python3
"""Kernel benchmarks for `Silmaril.Data.BytesTrie` (docs/projects/finmaps.md).

Writes one Lean file per scenario to a scratch directory, checks it with
`lake env lean`, and reads the kernel time of the measured theorem from
`#kernel_time`, which builds the `decide +kernel` proof term
(`of_decide_eq_true _ _ (Eq.refl true)`; no `native_decide`, no extra axioms) and
times `addDecl` (after a warm-up declaration, with `Elab.async` off so earlier
definitions are already checked), so the number is the time the kernel spends evaluating the
`Decidable` instance. Materialized scenarios first evaluate the map with the
compiler at elaboration time and splice the normal form in as a literal term.

Usage: scripts/bench/finmap-kernel.py [--sizes 100,1000] [--out results.json]
Run from the repository root after `lake build Silmaril.Data.BytesTrie.Thms`.
"""
import argparse, json, os, re, subprocess, sys, tempfile, time

PRELUDE = r'''
import Lean
import Silmaril.Data.BytesTrie.Thms
import Silmaril.Data.NatBitSet.Thms
open Lean Elab Term Meta Silmaril.Data Silmaril.Data.BytesTrie

/-- Dense keys: `i` as three big-endian bytes (up to 256 siblings per level). -/
def denseKey (i : Nat) : List UInt8 := [UInt8.ofNat (i / 65536), UInt8.ofNat (i / 256), UInt8.ofNat i]
/-- Spread keys: a multiplicative hash of `i`, three bytes. -/
def spreadKey (i : Nat) : List UInt8 := denseKey (i * 2654435761 % 16777216)

def build (key : Nat → List UInt8) (n : Nat) : BytesTrie Nat :=
  (List.range n).foldl (fun t i => t.insert (key i) i) BytesTrie.empty
def buildRev (key : Nat → List UInt8) (n : Nat) : BytesTrie Nat :=
  (List.range n).reverse.foldl (fun t i => t.insert (key i) i) BytesTrie.empty
def assoc (key : Nat → List UInt8) (n : Nat) : List (List UInt8 × Nat) :=
  (List.range n).foldl (fun l i => (key i, i) :: l) []

partial def trieExpr : Trie Nat → Expr
  | .nil => mkApp (Lean.mkConst ``Trie.nil [Level.zero]) (Lean.mkConst ``Nat)
  | .node b v c n => mkApp5 (Lean.mkConst ``Trie.node [Level.zero]) (Lean.mkConst ``Nat) (toExpr b) (toExpr v)
      (trieExpr c) (trieExpr n)

/-- Evaluate a raw trie at elaboration time and splice its normal form in as a literal term. -/
elab "materialize% " t:term : term => do
  let e ← elabTerm t (some (Lean.mkConst ``BytesTrie [Level.zero] |>.app (Lean.mkConst ``Nat)))
  let v ← unsafe evalExpr (BytesTrie Nat) (mkApp (Lean.mkConst ``BytesTrie [Level.zero]) (Lean.mkConst ``Nat)) e
  return mkApp3 (Lean.mkConst ``BytesTrie.mk [Level.zero]) (Lean.mkConst ``Nat) (toExpr v.root) (trieExpr v.kids)

elab "materializeAssoc% " t:term : term => do
  let ty ← elabType (← `(List (List UInt8 × Nat)))
  let e ← elabTerm t (some ty)
  let v ← unsafe evalExpr (List (List UInt8 × Nat)) ty e
  return toExpr v

/-- Check `p` by kernel evaluation of its `Decidable` instance, as `decide +kernel`
does, and print the time `addDecl` (the kernel check) takes. -/
elab "#kernel_time " p:term : command => Command.liftTermElabM do
  let p ← elabType p
  Term.synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars p
  let inst ← instantiateMVars (← synthInstance (mkApp (Lean.mkConst ``Decidable) p))
  let pf := mkApp3 (Lean.mkConst ``of_decide_eq_true) p inst
    (mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true))
  let name ← mkFreshUserName `bench
  let t0 ← IO.monoNanosNow
  addDecl (.thmDecl { name, levelParams := [], type := p, value := pf })
  let t1 ← IO.monoNanosNow
  logInfo m!"KERNEL_MS {(t1 - t0).toFloat / 1e6}"
'''

def scenarios(n, dist):
    k = f"{dist}Key"
    last, first = n - 1, 0
    setup = {
        "mat": f"def M : BytesTrie Nat := materialize% build {k} {n}\n"
               f"def M2 : BytesTrie Nat := materialize% buildRev {k} {n}\n",
        "matA": f"def A : List (List UInt8 × Nat) := materializeAssoc% assoc {k} {n}\n",
    }
    return [
        ("build+lookup", "", f"(build {k} {n}).find? ({k} {last}) = some {last}"),
        ("build+lookup(assoc)", "", f"(assoc {k} {n}).lookup ({k} {first}) = some {first}"),
        ("lookup first(materialized)", setup["mat"], f"M.find? ({k} {first}) = some {first}"),
        ("lookup last(materialized)", setup["mat"], f"M.find? ({k} {last}) = some {last}"),
        ("lookup first(materialized assoc)", setup["matA"], f"A.lookup ({k} {first}) = some {first}"),
        ("lookup last(materialized assoc)", setup["matA"], f"A.lookup ({k} {last}) = some {last}"),
        ("insert+lookup(materialized)", setup["mat"], f"(M.insert ({k} {n}) 7).find? ({k} {n}) = some 7"),
        ("erase+lookup other(materialized)", setup["mat"],
         f"(M.erase ({k} {last})).find? ({k} {first}) = some {first}"),
        ("validate canonB(materialized)", setup["mat"], "M.canonB = true"),
        ("equality(materialized)", setup["mat"], "M = M2"),
        ("equality(build vs buildRev)", "", f"build {k} {n} = buildRev {k} {n}"),
    ]

def bitset_scenarios(n):
    b = (f"def S : NatBitSet := (List.range {n}).foldl (fun s i => s.insert (3 * i)) NatBitSet.empty\n"
         f"def S2 : NatBitSet := (List.range {n}).reverse.foldl (fun s i => s.insert (3 * i)) NatBitSet.empty\n")
    return [
        ("build+mem", b, f"S.mem {3 * (n - 1)} = true"),
        ("build+equality", b, "S = S2"),
    ]

def run(lean_src, workdir, timeout):
    path = os.path.join(workdir, "Bench.lean")
    with open(path, "w") as f:
        f.write(lean_src)
    t0 = time.time()
    try:
        out = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                             timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        return None, "timeout"
    m = re.findall(r"KERNEL_MS ([\d.]+)", out)
    if len(m) < 2 or "error:" in out:
        return None, out.strip()[-300:]
    return float(m[1]), f"{time.time() - t0:.1f}s wall"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", default="100,1000,4000")
    ap.add_argument("--dists", default="dense,spread,bitset")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    results = []
    with tempfile.TemporaryDirectory() as d:
        for dist in a.dists.split(","):
            for n in map(int, a.sizes.split(",")):
                for name, setup, prop in (bitset_scenarios(n) if dist == "bitset"
                                          else scenarios(n, dist)):
                    src = (PRELUDE + "set_option Elab.async false\nset_option maxRecDepth 1000000\n" + setup
                           + f"#kernel_time 1 = 1\n#kernel_time {prop}\n")
                    ms, note = run(src, d, a.timeout)
                    row = {"dist": dist, "n": n, "scenario": name, "kernel_ms": ms, "note": note}
                    results.append(row)
                    print(json.dumps(row), flush=True)
    if a.out:
        with open(a.out, "w") as f:
            json.dump(results, f, indent=1)

if __name__ == "__main__":
    sys.exit(main())

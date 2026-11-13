module

public import Silmaril.Compiler.Core.Verified.CfgBound.Defs
/-! # Potentials for the labels of a printing control-flow graph

A guess, checked by `Cfg.check` (nothing here needs a proof). Let `S` be the room of every print
node of the plan. A label whose tree tests a slot `x` against a literal `k` (`x < k`, `x ≤ k`, …)
heads a loop counting `x` up to `b = k + 1`: its potential is `S` bytes per step below `b`. The
labels its tree jumps to (a `switch`'s cases, a `break` label) count with it one step closer, then
with the shift of `x` on the way; other labels that jump to a counting label count one step
further. The constant parts are the least that pays every path, by rounds of relaxation. Labels
that reach no counter get a constant potential.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgPotential

open Silmaril.Cerberus Silmaril.Cerberus.Core
open StateExpr (Key Term)
open Cfg

/-- The room of every print node of a tree. -/
def prints : Code → Nat
  | .atom _ c => prints c
  | .print pre suf _ c => CfgPrintStmt.room pre suf + prints c
  | .test _ _ y n => prints y + prints n
  | _ => 0

/-- The slot and bound of the first test of a slot against a literal, in the tree's order. -/
def counter : Code → Option (Key × Int)
  | .atom _ c => counter c
  | .print _ _ _ c => counter c
  | .test _ t y n =>
    let rest := (counter y).orElse fun _ => counter n
    match testFact t with
    | some (.lt, .var x, k, _) | some (.le, .var x, k, _) | some (.gt, .var x, k, _)
    | some (.ge, .var x, k, _) => some (x, k + 1)
    | _ => rest
  | _ => none

/-- The end of a path: the prints passed, the label jumped to (`none` for a return), the
symbolic store and the counter's bound there. -/
structure End where
  P : Nat
  l : Option Key
  st : Key → SVal
  hi : Option Int

/-- The ends of the paths of a tree, walked as `Cfg.check` walks them. -/
def ends (π : Pot) : (Key → SVal) → Option Int → Nat → Code → List End
  | st, hi, P, .atom (.set q t) c => ends π (Function.update st q (sval st t)) hi P c
  | st, hi, P, .atom (.clear q) c => ends π (Function.update st q (.const 0)) hi P c
  | st, hi, P, .print pre suf _ c => ends π st hi (P + CfgPrintStmt.room pre suf) c
  | st, hi, P, .test direct t y n =>
    ends π st (refine π st hi direct true t) P n ++ ends π st (refine π st hi direct false t) P y
  | st, hi, P, .goto l => [⟨P, some l, st, hi⟩]
  | st, hi, P, _ => [⟨P, none, st, hi⟩]

/-- The shift of `x` at an end, when it is `x`'s root value shifted. -/
def shiftAt (x : Key) (e : End) : Option Int :=
  match e.st x with
  | .rel q δ => if q = x then some δ else none
  | _ => none

/-- The counters and bounds of the labels: loop heads first, then what they jump to, then what
jumps to a counting label. -/
def bounds (codes : List (Key × Code)) : List (Key × (Key × Int)) :=
  let heads := codes.filterMap fun z => (counter z.2).map fun xb => (z.1, xb)
  let rounds := codes.length + 1
  let step := fun (acc : List (Key × (Key × Int))) =>
    codes.foldl (fun acc z =>
      match acc.lookup z.1 with
      | none => acc
      | some (x, b) =>
        let isHead := (heads.lookup z.1).isSome
        let es := ends ⟨some x, 0, b, 0⟩ rootStore none 0 z.2
        es.foldl (fun acc e =>
          match e.l, shiftAt x e with
          | some l', some δ =>
            if (acc.lookup l').isSome then acc
            else acc ++ [(l', (x, if isHead then b - 1 + δ else b + δ))]
          | _, _ => acc) acc) acc
  let forward := (List.range rounds).foldl (fun acc _ => step acc) heads
  let back := codes.filterMap fun z =>
    if (forward.lookup z.1).isSome then none
    else
      (ends ⟨none, 0, 0, 0⟩ rootStore none 0 z.2).findSome? fun e =>
        match e.l with
        | some l' => (forward.lookup l').bind fun (x, b) =>
            (shiftAt x e).map fun δ => (z.1, (x, b - δ + 1))
        | none => none
  forward ++ back

/-- The constant part a path end asks of its root's potential, the target's being `pot`. -/
def ask (a : Nat) (π : Pot) (pot : Key → Pot) (e : End) : Nat :=
  match e.l with
  | none => e.P
  | some l' =>
    let π' := pot l'
    match π'.x, π.x with
    | none, _ => e.P + π'.e
    | some x', some x =>
      match shiftAt x' e with
      | some δ =>
        let below : Bool := match e.hi with | some h => decide (h ≤ π.b - 1) | none => false
        if x' = x ∧ 1 ≤ π.b - π'.b + δ ∧ below = true
        then e.P + π'.e - a
        else e.P + π'.e
      | none => e.P + π'.e
    | some _, none => e.P + π'.e

/-- The potentials of the labels of a plan. -/
def infer (P : Plan) : List (Key × Pot) :=
  let S := prints P.entry + (P.codes.map fun z => prints z.2).sum
  let bs := bounds P.codes
  let shape : Key → Nat → Pot := fun l e =>
    match bs.lookup l with
    | some (x, b) => ⟨some x, S, b, e⟩
    | none => ⟨none, 0, 0, e⟩
  let relax := fun (es : List (Key × Nat)) =>
    let pot := fun l => shape l ((es.lookup l).getD 0)
    P.codes.map fun z =>
      let π := pot z.1
      let need := ((ends π rootStore none 0 z.2).map (ask S π pot)).foldl max 0
      (z.1, max ((es.lookup z.1).getD 0) need)
  let es := (List.range (P.codes.length + 2)).foldl (fun es _ => relax es) (P.codes.map fun z => (z.1, 0))
  P.codes.map fun z => (z.1, shape z.1 ((es.lookup z.1).getD 0))

end Silmaril.Compile.Core.Verified.CfgPotential

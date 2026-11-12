module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs

/-!
# Round 7, memory SIMD: where `$vbytes_` is called (definitions)

`Round7.Task.wholeStepValidRM` is stated at `BM = withVBytes (Prims.builtins …)`, round 6 at
`BI`. The two builtins differ only at `$vbytes_`. A transfer between them needs to know which
parts of the script can call `$vbytes_`. The computations below say it, for the kernel:

* `ruleUsers y rules`: the indices of the rules in `rules` whose events refer to the
  definition `y`;
* `relRulesUsers y x`: `ruleUsers y` on the rules that `envFixed` finds for the relation `x`
  (`none` when there is no such relation);
* `itemUsers y s`: the items of `s` whose events refer to the definition `y`;
* `vbytesOnlyStep s`: every item of `s` that refers to `$vbytes_` is one of the relations
  `Step_read` and `Step`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VBytes

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script

/-- The indices of the rules in `rules` whose events refer to the definition `y`. -/
def ruleUsers (y : String) (rules : List Rule) : List Nat :=
  (List.range rules.length).filter fun i =>
    match rules[i]? with
    | some r => (evRefs (evRule r)).contains (1, y)
    | none => false

/-- `ruleUsers y` on the rules of the relation `x` in the fixed wasm-3.0 script's environment. -/
noncomputable def relRulesUsers (y x : String) : Option (List Nat) :=
  (Scripts.Wasm30.envFixed.findRel? x).map fun v => ruleUsers y v.2.2.2

/-- The items of `s` whose events refer to the definition `y`. -/
def itemUsers (y : String) (s : Script) : List (Nat × String) :=
  (items s).filterMap fun it =>
    if (evRefs it.2.2).contains (1, y) then some (it.1, it.2.1) else none

/-- An item that does not refer to `$vbytes_`, unless it is the relation `Step_read` or `Step`. -/
def vbytesItemOk (it : Item) : Bool :=
  (it.1 == 0 && (it.2.1 == "Step_read" || it.2.1 == "Step")) ||
    !(evRefs it.2.2).contains (1, "vbytes_")

/-- **Only `Step_read` and `Step` refer to `$vbytes_`** in `s`. -/
def vbytesOnlyStep (s : Script) : Bool := (items s).all vbytesItemOk

end Silmaril.Wasm.SpecTec.Sim.Round7.VBytes

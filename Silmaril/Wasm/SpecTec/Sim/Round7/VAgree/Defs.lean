module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Thms

/-!
# Round 7, memory SIMD: `simEnv B₁` and `simEnv B₂` away from `$vbytes_` (definitions)

`OpenRMRest` is stated at `BM = withVBytes …`, round 6 at `BI`. The two builtins differ only at
`$vbytes_`. `Round7.VBytes` proves that only `Step_read` rule 43 and `Step` rule 23 refer to
`$vbytes_`. The evaluator half of the transfer compares `simEnv B₁` with `simEnv B₂` for any two
builtins that agree off `$vbytes_` (`AgreeOff`). The definitions below are its invariants:

* `GoodName y`: a definition reachable from `Step` other than `$vbytes_`;
* `GoodRel x`: a relation reachable from `Step` other than `Step` and `Step_read`, the two
  relations that hold rules calling `$vbytes_`;
* `GoodEvs l`: every definition and relation that `l` refers to is good; `DefsOk ρ`, `ArgOk w`:
  definition variables and definition arguments name good definitions.

Two kernel computations say which items and rules refer to `Step` or `Step_read`:

* `stepRelOnly s`: an item of `s` reachable from `Step` refers to the relation `Step` or
  `Step_read` only if it is one of them;
* `relRulesUsersK k y x`: the indices of the rules of the relation `x` that refer to the item
  `(k, y)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (Ev Item items evRefs evRule stepReach)

/-- A reference to the relation `Step` or `Step_read`. -/
def stepRelRef (r : Nat × String) : Bool := r == (0, "Step") || r == (0, "Step_read")

/-- An item that does not refer to `Step` or `Step_read`, unless it is one of them or is not
reachable from `Step`. -/
def stepRelItemOk (it : Item) : Bool :=
  !(evRefs it.2.2).any stepRelRef || stepRelRef (it.1, it.2.1) || !stepReach.contains (it.1, it.2.1)

/-- **Only `Step` and `Step_read` refer to `Step` or `Step_read`**, among the reachable items. -/
def stepRelOnly (s : IL.Script) : Bool := (items s).all stepRelItemOk

/-- The indices of the rules in `rules` that refer to the item `(k, y)`. -/
def ruleUsersK (k : Nat) (y : String) (rules : List Rule) : List Nat :=
  (List.range rules.length).filter fun i =>
    match rules[i]? with
    | some r => (evRefs (evRule r)).contains (k, y)
    | none => false

/-- `ruleUsersK k y` on the rules of the relation `x` in the fixed wasm-3.0 script. -/
noncomputable def relRulesUsersK (k : Nat) (y x : String) : Option (List Nat) :=
  (Scripts.Wasm30.envFixed.findRel? x).map fun v => ruleUsersK k y v.2.2.2

/-! ## The invariants -/

/-- A definition reachable from `Step` other than `$vbytes_`. -/
def GoodName (y : String) : Prop := (1, y) ∈ stepReach ∧ y ≠ "vbytes_"

/-- A relation reachable from `Step` other than `Step` and `Step_read`. -/
def GoodRel (x : String) : Prop := (0, x) ∈ stepReach ∧ x ≠ "Step" ∧ x ≠ "Step_read"

/-- A harmless event: a definition reference is `GoodName`, a relation reference `GoodRel`. -/
def GoodEv : Ev → Prop
  | .ref 1 x => GoodName x
  | .ref 0 x => GoodRel x
  | _ => True

/-- Every event of `l` is `GoodEv`. -/
def GoodEvs (l : List Ev) : Prop := ∀ e ∈ l, GoodEv e

/-- Every definition variable of `ρ` names a `GoodName` definition. -/
def DefsOk (ρ : VarEnv) : Prop := ∀ p ∈ ρ.defs, GoodName p.2

/-- A definition argument names a `GoodName` definition. -/
def ArgOk : ArgV → Prop
  | .defName y => GoodName y
  | _ => True

/-- **Two builtins agree off `$vbytes_`.** `withVBytes B` and `B` do (`agreeOff_withVBytes`). -/
def AgreeOff (B₁ B₂ : Builtins) : Prop := ∀ x ws, x ≠ "vbytes_" → B₁.call x ws = B₂.call x ws

/-- **Rule `i` of the relation `x` is harmless**: whenever `simEnv` finds `x` with a rule `i`,
that rule is `GoodEvs`. -/
def GoodRule (x : IL.Id) (i : Nat) : Prop :=
  ∀ (B : Builtins) (d : RelDef) (r : Rule), (simEnv B).findRel? x = some d → d.2.2.2[i]? = some r →
    GoodEvs (evRule r)

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

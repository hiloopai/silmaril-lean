module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.VBytes.Thms

/-!
# Round 7, `BD`: `simEnv B₁` and `simEnv B₂` away from `$vbytes_` and `$hostcall` (definitions)

Round 7's reduction of `Round7.Task.wholeStepValidRM` (`MemSimd.OpenRMRest`) is stated at
`BM = withVBytes (Prims.builtins P hn host)`. Round 5 showed that `BM` answers no `$hostcall` made
from a store with memory SIMD code (`MSPres.bm_hostcall_none`), and defined `HostD.BD`, which keys
`$hostcall` on `storeVD` images. `BD` agrees with `BM` everywhere but at `$hostcall`, and with
round 6's `BI = Prims.builtins P hn host` everywhere but at `$hostcall` and `$vbytes_`.

`Round7.VAgree` and `Round7.VDecl` compare `simEnv B₁` and `simEnv B₂` for builtins that agree off
`$vbytes_`. This topic is the same comparison for builtins that agree off **both** `$vbytes_` and
`$hostcall`, so that it covers the three pairs `BD`/`BM`, `BD`/`BI` and `BM`/`BI` at once. The
definitions below are VAgree's and VDecl's with `$hostcall` also excluded; the definitions that do
not mention `$vbytes_` (`VAgree.GoodRel`, `VAgree.stepRelOnly`, `VAgree.relRulesUsersK`,
`VDecl.elseFree`, `VDecl.elseFreeIdx`, `VDecl.lhsAtom`, …) are reused.

* `GoodName y`: a definition reachable from `Step` other than `$vbytes_` and `$hostcall`;
  `GoodEv`, `GoodEvs`, `DefsOk`, `ArgOk`, `GoodRule` as in VAgree with this `GoodName`;
* `AgreeOff B₁ B₂`: the two builtins answer alike at every name other than `$vbytes_` and
  `$hostcall`;
* `RefOk`, `RG`, `TypsG`, `ArgTyG` and the kernel checks `refOkB`, `rgB`, `quantsRgB`,
  `ruleFactsB`, `relFactsB`: as in VDecl, with `$hostcall` also excluded;
* `hostcallItemOk`, `hostcallOnlyStep s`: every item of `s` that refers to `$hostcall` is the
  relation `Step`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (Ev Item items evRefs evTyp evExp evRule stepReach)
open Round7.VAgree (GoodRel)

/-! ## The evaluator invariants -/

/-- A definition reachable from `Step` other than `$vbytes_` and `$hostcall`. -/
def GoodName (y : String) : Prop := (1, y) ∈ stepReach ∧ y ≠ "vbytes_" ∧ y ≠ "hostcall"

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

/-- **Two builtins agree off `$vbytes_` and `$hostcall`.** -/
def AgreeOff (B₁ B₂ : Builtins) : Prop :=
  ∀ x ws, x ≠ "vbytes_" → x ≠ "hostcall" → B₁.call x ws = B₂.call x ws

/-- **Rule `i` of the relation `x` is harmless**: whenever `simEnv` finds `x` with a rule `i`,
that rule is `GoodEvs`. -/
def GoodRule (x : IL.Id) (i : Nat) : Prop :=
  ∀ (B : Builtins) (d : RelDef) (r : Rule), (simEnv B).findRel? x = some d → d.2.2.2[i]? = some r →
    GoodEvs (evRule r)

/-! ## The declarative invariants -/

/-- A reference reachable from `Step`, other than `$vbytes_`, `$hostcall`, `Step` and
`Step_read`. -/
def RefOk (r : Nat × String) : Prop :=
  r ∈ stepReach ∧ r ≠ (1, "vbytes_") ∧ r ≠ (1, "hostcall") ∧ r ≠ (0, "Step") ∧
    r ≠ (0, "Step_read")

/-- Every reference of `l` is `RefOk`. -/
def RG (l : List Ev) : Prop := ∀ r ∈ evRefs l, RefOk r

/-- Every type variable of `ρ` is bound to an `RG` type. -/
def TypsG (ρ : VarEnv) : Prop := ∀ p ∈ ρ.typs, RG (evTyp p.2)

/-- A type argument is an `RG` type. -/
def ArgTyG : ArgV → Prop
  | .typ t => RG (evTyp t)
  | _ => True

/-- `RefOk`, as a check. -/
def refOkB (r : Nat × String) : Bool :=
  stepReach.contains r && r != (1, "vbytes_") && r != (1, "hostcall") && r != (0, "Step") &&
    r != (0, "Step_read")

/-- `RG`, as a check. -/
def rgB (l : List Ev) : Bool := (evRefs l).all refOkB

/-- Every expression quantifier has an `RG` type. -/
def quantsRgB (qs : List Param) : Bool :=
  qs.all fun q => match q with
    | .expP _ t => rgB (evTyp t)
    | _ => true

/-- A rule's quantifier types and conclusion alternatives are `RG`. -/
def ruleFactsB : Rule → Bool
  | .ruleD _ qs _ e _ => quantsRgB qs && (Round6.Reading.conclAlts e).all fun e' => rgB (evExp e')

/-- **The relations of `m` that `Step` reaches have no parameters, and their rules pass
`ruleFactsB`.** -/
def relFactsB (m : Map RelDef) : Bool :=
  m.all fun p => !stepReach.contains (0, p.1) || (p.2.1.isEmpty && p.2.2.2.2.all ruleFactsB)

/-! ## Where `$hostcall` is called -/

/-- An item that does not refer to `$hostcall`, unless it is the relation `Step`. -/
def hostcallItemOk (it : Item) : Bool :=
  (it.1 == 0 && it.2.1 == "Step") || !(evRefs it.2.2).contains (1, "hostcall")

/-- **Only `Step` refers to `$hostcall`** in `s`. -/
def hostcallOnlyStep (s : Script) : Bool := (items s).all hostcallItemOk

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

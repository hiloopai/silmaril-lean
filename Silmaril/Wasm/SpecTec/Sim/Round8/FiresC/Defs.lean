module

public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.Defs

/-!
# Round 8, function code erasure under the declarative reading (definitions)

`Round8.CodeErase` shows that the IL evaluator commutes with `eraseC` (every `CODE` field `u`
becomes `hostC u`, the code of a host function named injectively by `u`), with every value in the
swap set. `Round8.RMCode.FiresEraseD` asks for the same of the declarative reading `Sim.Fires`.
`Fires` reads a rule through `Sim.RuleBody`: its quantifiers must be typed (`Sim.QuantsOk`, read by
`Sem.hasTyp`, its own fuel-indexed block), its conclusion evaluates, and its premises hold.

This topic moves the typing block and the `if`/`let` premises across `eraseC`. It is round 7's
`Round7.EraseDer` (`TypBase`, `TypFwd`) for `CODE` fields instead of `EXPORTS`, at round 8's
evaluator-level erasure and with every value in the swap set. That makes the erased scope just
`eraseScope ρ`: the related-scope bookkeeping of round 7 (`TRel`, `aiPart`) is not needed.

* `xTy S t`, … `xTypMap S m`, `xRelQuants S m`: round 7's check on types, with round 8's check
  `CodeErase.EraseAll.xExp grC gdC` on the expressions inside types. The `CODE` field of a record
  type has type `funccode` and no premises (`xTFields`), and an instance whose body declares a
  `CODE` field has no argument patterns (`xInsts`), so that the field is typed in a scope without
  type variables. The kernel checks both on the fixed wasm-3.0 script at `tyC` (round 7's `tyB`
  with `exportinst` and `name`; `Round8.FiresC.xTypMap_fixed`, `xRelQuants_fixed`).
* `relG`: `Ref_ok`, `Expand` and the 25 validation relations they reach. None has parameters
  or an `otherwise` premise, and each rule passes round 8's check (`relGOk`, kernel-checked), so
  their derivations move across erasure (`Round8.FiresC.dderives_erase`). `relRule`: a rule with
  no `otherwise` premise whose relation premises are in `relG`. `relRead` (75 rules of
  `Step_read`) and `relStep` (every rule of `Step` from 6 on but 7–9) are such rules.
* `RestMSHCF`, `OpenRMRestDPF`: round 8 pass 2's `RMCode.RestMSHCQ` and `OpenRMRestDPQ` with
  `FiresEraseD` asked only for the 28 `Step_read` rules with an `otherwise` premise (`elseRead`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (grC gdC xExp xPrems xRule)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)

/-! ## The check on types -/

/-- **The types checked**: round 7's `tyB` (every type `Step` reaches but `name` and
`exportinst`) and those two. Round 7 left them out because of the export erasure; here they are
ordinary types. -/
def tyC : List String := Round7.TypAgree.tyB ++ ["exportinst", "name"]

mutual
/-- **A type over the names `S` whose expressions pass round 8's evaluator-level check**; type
arguments are closed. -/
def xTy (S : List String) : Typ → Bool
  | .varT x args => S.contains x && xTyArgs S args
  | .tupT bs => xTyBinds S bs
  | .iterT t it => xTy S t && CodeErase.EraseAll.xIter grC gdC it
  | _ => true

/-- `xTy` on the arguments of a type reference. -/
def xTyArgs (S : List String) : List Arg → Bool
  | [] => true
  | .typA t :: r => xTy S t && varsIn [] (freeTyp t) && xTyArgs S r
  | .expA e :: r => xExp grC gdC e && xTyArgs S r
  | _ :: _ => false

/-- `xTy` on tuple binders. -/
def xTyBinds (S : List String) : List TypBind → Bool
  | [] => true
  | .mk _ t :: bs => xTy S t && xTyBinds S bs
end

/-- The type of `funcinst`'s `CODE` field, `funccode`. -/
def isCodeT : Typ → Bool
  | .varT "funccode" [] => true
  | _ => false

/-- Record fields: a `CODE` field has type `funccode` and no premises; every other field is
checked. -/
def xTFields (S : List String) : List TypField → Bool
  | [] => true
  | .mk a t _ prems :: fs =>
      (if a == "CODE" then isCodeT t && prems.isEmpty
        else xTy S t && xPrems grC gdC prems) && xTFields S fs

/-- Variant cases: carried type, quantifier types and premises. -/
def xTCases (S : List String) : List TypCase → Bool
  | [] => true
  | .mk _ t qs prems :: cs =>
      xTy S t && qs.all (fun q => match q with | .expP _ t => xTy S t | _ => true) &&
        xPrems grC gdC prems && xTCases S cs

/-- A type definition's body. -/
def xDefTyp (S : List String) : DefTyp → Bool
  | .aliasT t => xTy S t
  | .structT fs => xTFields S fs
  | .variantT cs => xTCases S cs

/-- The record fields include one named `CODE`. -/
def fieldsCode (fs : List TypField) : Bool :=
  fs.any fun f => match f with | .mk a _ _ _ => a == "CODE"

/-- A type definition's body declares a record field named `CODE`. -/
def defTypCode : DefTyp → Bool
  | .structT fs => fieldsCode fs
  | _ => false

/-- The instances of a type family: argument patterns and bodies; an instance whose body declares
a `CODE` field has no argument patterns. -/
def xInsts (S : List String) (insts : List Inst) : Bool :=
  insts.all fun i => match i with
    | .instD _ pats dt => CodeErase.EraseAll.xArgs grC gdC pats && xDefTyp S dt &&
        (!defTypCode dt || pats.isEmpty)

/-- **Every type of `m` named in `S` is checked.** -/
def xTypMap (S : List String) (m : Map TypDef) : Bool :=
  m.all fun p => !S.contains p.1 || xInsts S p.2.2

/-- **The quantifier types of every rule `Step` reaches are checked.** -/
def xRelQuants (S : List String) (m : Map RelDef) : Bool :=
  m.all fun p => !Round7.Script.stepReach.contains (0, p.1) || p.2.2.2.2.all fun r => match r with
    | .ruleD _ qs _ _ _ => qs.all fun q => match q with
      | .expP _ t => xTy S t
      | _ => true

/-- **The shape of `funccode`**: one instance without argument patterns, a variant whose first
case `FUNC` carries a non-empty tuple and whose second case is `_HOSTFUNC text`, with no
quantifiers or premises. A `_HOSTFUNC` code needs less fuel to type than a `FUNC` code. -/
def funccodeOk : TypDef → Bool
  | (_, [.instD _ [] (.variantT [.mk "FUNC" (.tupT (_ :: _)) _ _, .mk "_HOSTFUNC" .textT [] []])]) =>
      true
  | _ => false

/-- Every type named `funccode` in `m` has the shape `funccodeOk`. -/
def funccodeMap (m : Map TypDef) : Bool :=
  m.all fun p => p.1 != "funccode" || funccodeOk p.2

/-! ## Rules -/

/-- The relations a premise consults. -/
def premRelsC : Prem → List IL.Id
  | .rulePr x _ _ _ => [x]
  | .iterPr pr _ => premRelsC pr
  | _ => []

/-- A premise is or iterates `otherwise`. -/
def premElse : Prem → Bool
  | .elsePr => true
  | .iterPr pr _ => premElse pr
  | _ => false

/-- The indices `i < k` of the rules of `rules` that pass `f`. -/
def idxWhere (f : Rule → Bool) (rules : List Rule) : List Nat :=
  (List.range rules.length).filter fun i => match rules[i]? with
    | some r => f r
    | none => false

/-- The rules of the relation `x` of the fixed script. -/
noncomputable def rulesOf (x : IL.Id) : List Rule :=
  match (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).find? x with
  | some d => d.2.2.2
  | none => []

/-! ## Relation premises -/

/-- **The relations the relation premises of `Step_read` and `Step` reach**: `Ref_ok`, `Expand`
and the 25 validation relations they consult. -/
def relG : List String :=
  ["Comptype_ok", "Comptype_sub", "Deftype_ok", "Deftype_sub", "Expand", "Fieldtype_ok",
    "Fieldtype_sub", "Heaptype_ok", "Heaptype_sub", "Numtype_ok", "Numtype_sub", "Packtype_ok",
    "Packtype_sub", "Rectype_ok2", "Ref_ok", "Reftype_ok", "Reftype_sub", "Resulttype_ok",
    "Resulttype_sub", "Storagetype_ok", "Storagetype_sub", "Subtype_ok2", "Typeuse_ok",
    "Valtype_ok", "Valtype_sub", "Vectype_ok", "Vectype_sub"]

/-- A premise that is not (and does not iterate) `otherwise`, and consults only `relG`. -/
def relPrem (pr : Prem) : Bool := !premElse pr && (premRelsC pr).all relG.contains

/-- **A rule whose premises move with `relG`**: it passes round 8's check, has no `otherwise`
premise, and consults only `relG`. -/
def relRule (r : Rule) : Bool :=
  xRule grC gdC r && match r with
    | .ruleD _ _ _ _ prems => prems.all relPrem

/-- **`relG` is closed**: every relation of `m` in `relG` has no parameters and rules that are
`relRule`; and every relation of `relG` is one `Step` reaches, other than `Step`. -/
def relGOk (m : Map RelDef) : Bool :=
  relG.all (fun x => grC x && Round7.Script.stepReach.contains (0, x)) &&
    m.all fun p => !relG.contains p.1 || (p.2.1.isEmpty && p.2.2.2.2.all relRule)

/-- **The rules of `Step_read` with no `otherwise` premise** (75 of 103), all `relRule`. -/
def relRead : List Nat :=
  [0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28,
    31, 35, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 60, 63, 64, 65, 67,
    69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 86, 87, 88, 89, 93, 94, 95, 98, 99,
    100]

/-- **The rules of `Step_read` with an `otherwise` premise** (28). -/
def elseRead : List Nat :=
  [3, 5, 21, 29, 30, 32, 33, 34, 36, 37, 54, 55, 57, 58, 59, 61, 62, 66, 68, 84, 85, 90, 91, 92,
    96, 97, 101, 102]

/-- **The rules of `Step` from 6 on, other than 7–9** (the three that read `CODE`), all
`relRule`. -/
def relStep : List Nat := 6 :: (List.range 26).map (· + 10)

/-- Every index of `l` names a `relRule` rule of `x`. -/
noncomputable def relAt (x : IL.Id) (l : List Nat) : Bool :=
  l.all fun i => match (rulesOf x)[i]? with
    | some r => relRule r
    | none => false

/-! ## The obligations left -/

section
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS)
open Round7.MemSimd (configVD adminsToVD TypedD BwdUpToD msReadRules stepMSRules BoundedSelM)

variable {H : Type}

/-- **`RMCode.RestMSHCQ` with `FiresEraseD` asked only for the 28 `Step_read` rules with an
`otherwise` premise** (`elseRead`); none is left for `Step`. -/
structure RestMSHCF (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMCode.RestMSHCQ.pure`. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    ¬ AdminsMS is → Round7.MSRest.VMS ⟨s, f, is⟩ →
    TypedD (simEnv (Prims.builtins P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- As `RMCode.RestMSHCQ.read`. -/
  read : ∀ (i : Nat), i ∉ msReadRules → ∀ (c : Config H) (w : Value), ¬ AdminsMS c.code →
    Round7.MSRest.VMS c → TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- As `RMCode.RestMSHCQ.step`. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ stepMSRules → i ≠ 8 → i ≠ 9 → ∀ (c : Config H) (w : Value),
    (¬ AdminsMS c.code ∨ i = 7) → Round7.MSRest.VMS c →
    TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step" i (.tuple [configVD hn c, w]) →
    BwdUpToD hn P host c w
  /-- The `Step_read` rules with an `otherwise` premise keep firing when the function code is
  erased. -/
  firesRead : ∀ i ∈ elseRead,
    RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i

/-- **`RMCode.OpenRMRestDPQ` with `RestMSHCF` for `RestMSHCQ`.** -/
structure OpenRMRestDPF (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMCode.OpenRMRestDPQ.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.HostD.BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule obligations left. -/
  restMSHC : RestMSHCF hn P host
  /-- As `RMCode.OpenRMRestDPQ.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `RMCode.OpenRMRestDPQ.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → Round6.Target.CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

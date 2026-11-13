module

public import Silmaril.Wasm.SpecTec.Institution.Typing30.Defs
public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms

/-!
# Typing judgements of the wasm-3.0 script against Core 3.0 validation

The model is `stepModel BI`, the backend canonical model of the fixed wasm-3.0 script at the
concrete primitives `Round4Int.BI` (the model of `Cover.toModelDom`). The judgements are
`Typing30.TySen`.

* `preserves`: on the domain, a judgement Core validates is a fact of `stepModel BI`
  (`AgreeTy.okIntro`, `AgreeTy.subIntro`, and `Agree.refOk` with `RefOkV.refOkS_iff`).
* `reflects`, `sat_iff`: for `sub` and `refOk` the converse holds as well. For `sub` it goes
  through `AgreeTy.subElim` (the right-hand side is the image of `SubE`), `tyV_inj`, and
  `RefOkV.sub_of_subE_ref` at heap types made coherent by `AgreeTy.okElim`.
* `ok_coh`: for `ok` only coherence of the heap type comes back.
* `ok_not_reflects`, `refOk_nested`: and no more. `REF NULL D_out` is
  bounded, `stepModel BI` validates it and types `null` at it on every typed store, while Core
  rejects both.
* `refOk_dom_of_config`: a `refOk` judgement at the store of a valid `BoundedSel` configuration is
  in the domain as soon as its type is bounded and Core-valid.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Typing30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj)
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type}

/-- A fact sentence holds in a model exactly when the model's interpretation derives it. -/
theorem sat_toSen_iff {S : Sig} (alts : Reading) (M : Model S) (hn : H → String) (φ : TySen H) :
    (φ.toSen hn).Sat alts M.env M.D ↔
      match φ.toSen hn with
      | .fact x op args v => M.D x op args v
      | .rule _ _ => False := by
  cases φ <;> exact Iff.rfl

variable (P : Profile) (hn : H → String) (host : HostSemantics H)

/-- The model of the typing comorphism: `stepModel` at the concrete primitives `BI`. -/
local notation "MB" => Wasm30.stepModel (Round4Int.BI P hn host)

/-- Its evaluator. -/
local notation "EB" => simEnv (Round4Int.BI P hn host)

/-- `Reftype_ok {}` of `stepModel BI` makes the heap type coherent. -/
theorem okFact_coh {rt : CRefType}
    (h : (MB).D "Reftype_ok" "%|-%:OK" [] (.tuple [Round6.RefOkV.ctxEmptyV, tyV rt])) :
    Round6.RefOkV.CohH (Round6.RefOkV.refHeap rt) :=
  (Round6.Int.agreeTy_BI P hn host).okElim _ rt h

include P hn host in
/-- A bounded, Core-valid reference type has a coherent heap type. -/
theorem coh_of_tyOk {rt : CRefType} (hb : Round4.tyBnd rt = true) (h : TyOk {} rt) :
    Round6.RefOkV.CohH (Round6.RefOkV.refHeap rt) :=
  okFact_coh P hn host ((Round6.Int.agreeTy_BI P hn host).okIntro _ rt hb h)

/-- **Core validation is preserved**: on the domain, a judgement that Core validates is a fact
of `stepModel BI`. -/
theorem preserves {φ : TySen H} (hd : φ.Dom (EB) hn) (h : φ.Holds) :
    (φ.toSen hn).Sat backend (MB).env (MB).D := by
  have A := Round6.Int.agreeTy_BI P hn host
  cases φ with
  | ok rt => exact A.okIntro _ rt hd h
  | sub p rt => exact A.subIntro _ p rt hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 h
  | refOk s r rt =>
    obtain ⟨hs, hS, hb, hok⟩ := hd
    exact ((Round6.RefOkV.agree_of_agreeTy A).refOk hn s rt hs hS hb hok _ r).2
      ((Round6.RefOkV.refOkS_iff hS hok).2 h)

/-- `Reftype_sub {}` of `stepModel BI` between bounded, Core-valid types is Core's `Sub {}`. -/
theorem sub_reflects {p rt : CRefType} (hbp : Round4.tyBnd p = true)
    (hbr : Round4.tyBnd rt = true) (hp : TyOk {} p) (hr : TyOk {} rt)
    (h : (MB).D "Reftype_sub" "%|-%<:%" [] (.tuple [Round6.RefOkV.ctxEmptyV, tyV p, tyV rt])) :
    Sub {} p rt := by
  obtain ⟨rt', he, hs⟩ := (Round6.Int.agreeTy_BI P hn host).subElim _ p (tyV rt) h
  have hrt : rt = rt' := tyV_inj rt rt' he
  subst hrt
  have cp := coh_of_tyOk P hn host hbp hp
  have cr := coh_of_tyOk P hn host hbr hr
  cases p
  cases rt
  exact Round6.RefOkV.sub_of_subE_ref hs cp cr

/-- **Core validation is reflected** on the exact judgements (`sub`, `refOk`). -/
theorem reflects {φ : TySen H} (he : φ.Exact) (hd : φ.Dom (EB) hn)
    (h : (φ.toSen hn).Sat backend (MB).env (MB).D) : φ.Holds := by
  cases φ with
  | ok rt => exact he.elim
  | sub p rt => exact sub_reflects P hn host hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 h
  | refOk s r rt =>
    obtain ⟨hs, hS, hb, hok⟩ := hd
    have A := Round6.RefOkV.agree_of_agreeTy (Round6.Int.agreeTy_BI P hn host)
    exact (Round6.RefOkV.refOkS_iff hS hok).1 ((A.refOk hn s rt hs hS hb hok _ r).1 h)

/-- **The satisfaction condition** on the exact judgements: a `Reftype_sub {}` or `Ref_ok` fact
holds in `stepModel BI` iff Core validates the judgement. -/
theorem sat_iff {φ : TySen H} (he : φ.Exact) (hd : φ.Dom (EB) hn) :
    (φ.toSen hn).Sat backend (MB).env (MB).D ↔ φ.Holds :=
  ⟨reflects P hn host he hd, preserves P hn host hd⟩

/-- For `ok`, a fact of `stepModel BI` gives back coherence of the heap type only. -/
theorem ok_coh {rt : CRefType} (h : ((TySen.ok rt : TySen H).toSen hn).Sat backend (MB).env (MB).D) :
    Round6.RefOkV.CohH (Round6.RefOkV.refHeap rt) :=
  okFact_coh P hn host h

/-- **`ok` is not reflected**: `REF NULL D_out` is bounded and valid in `stepModel BI`, and Core
rejects it. -/
theorem ok_not_reflects :
    (TySen.ok Round5.RefOk.nestedRT : TySen H).Dom (EB) hn ∧
      ((TySen.ok Round5.RefOk.nestedRT : TySen H).toSen hn).Sat backend (MB).env (MB).D ∧
      ¬ (TySen.ok Round5.RefOk.nestedRT : TySen H).Holds :=
  ⟨Round6.RefOkB.tyBnd_nested, Round6.RefOkB.dderivesB_reftypeOk_nested _,
    Round5.RefOk.not_tyOk_nested⟩

/-- **Off the domain, `refOk` is not reflected either**: on every store with a typed image,
`stepModel BI` types `null` at `REF NULL D_out`, Core does not, and the judgement is outside the
domain because Core rejects the type. -/
theorem refOk_nested (s : Store H) (hs : TypedV (EB) storeT (storeV hn s)) :
    ((TySen.refOk s .null Round5.RefOk.nestedRT).toSen hn).Sat backend (MB).env (MB).D ∧
      ¬ (TySen.refOk s .null Round5.RefOk.nestedRT).Holds ∧
      ¬ (TySen.refOk s .null Round5.RefOk.nestedRT).Dom (EB) hn :=
  ⟨Round6.RefOkB.dderivesB_refOk_nested _ hs, Round5.RefOk.not_refOk_null_nested s,
    fun hd => Round5.RefOk.not_tyOk_nested hd.2.2.2⟩

/-- The empty store is in the domain of `refOk` (so `refOk_nested` applies to it). -/
theorem typedV_storeEmpty : TypedV (EB) storeT (storeV hn ({} : Store H)) :=
  Round5.RefOk.typedV_storeEmpty _ hn

/-- **Configurations**: a `refOk` judgement at the store of a valid `BoundedSel` configuration,
at a bounded Core-valid type, is in the domain. -/
theorem refOk_dom_of_config {c : Config H} {ts : List CValType} (hok : ConfigOk c ts)
    (hb : Round5.Target.BoundedSel c) (r : Ref) {rt : CRefType} (hbr : Round4.tyBnd rt = true)
    (hr : TyOk {} rt) : (TySen.refOk c.store r rt).Dom (EB) hn := by
  have ht := Round5.Target.typed_of_configOk_sel (Round4Int.BI P hn host) hn hok hb
  have T := Typing.typingFacts_simEnv (Round4Int.BI P hn host) hn
  have hz := ((T.config c).1 ht).1
  obtain ⟨C, ⟨hS, -⟩, -⟩ := hok
  exact ⟨((T.state _ _).1 hz).1, hS, hbr, hr⟩

end Silmaril.Wasm.SpecTec.Institution.Typing30

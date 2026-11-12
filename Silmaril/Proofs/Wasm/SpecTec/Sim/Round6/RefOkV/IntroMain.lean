module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Intro

/-!
# Round 6: Core's `RefOk` gives SpecTec's `Ref_ok` (assembly)

* `dderivesB_refOk_base`: every base rule (`BaseOk`) fires under `DDerivesB`;
* `dderivesB_refOk_sub`: `Ref_ok/sub` fires from its three premises;
* `dderivesB_refOk_of_refOk`: from `AgreeTy`'s introduction fields, Core's `RefOk` at a bounded,
  Core-valid reference type, on a valid store with a typed image, is SpecTec's `Ref_ok`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round6.Reading

variable {H : Type} {B : Builtins}

/-- `ctxEmptyV` is `{}`. -/
theorem ctxEmptyV_eq : ctxEmptyV = ctx0V := rfl

/-- The `u31` payload of an `i31` reference is typed. -/
theorem typedV_u31 (b : BitVec 31) :
    TypedV (simEnv B) (.varT "u31" []) (percentV (.num (.natN b.toNat))) := fun ρ hρ =>
  hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) Typing.findTyp_u31
    Equiv.evalArgs_nil (hasTypInsts_head matchArgs_nil
      (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN evalExp_num b.isLt)))

/-- `Ref_ok/i31`. -/
theorem dderivesB_refOk_i31 (O : ElseI) {sv : Value} (hs : TypedV (simEnv B) storeT sv)
    (b : BitVec 31) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [sv, refToValue (.i31 b), tyV (Ty.ref false (Ty.abs .i31))]) :=
  dderivesB_of_ruleAt ruleAt_refOkI31 (self_mem_conclAlts _)
    [("s", sv), ("i", percentV (.num (.natN b.toNat)))]
    (QuantsOk.cons rfl (hs _ (valsOnly_bind _))
      (QuantsOk.cons rfl (typedV_u31 b _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_baseAbs rfl rfl .i31 "I31" rfl) premsB_nil

/-- `Ref_ok/host`. -/
theorem dderivesB_refOk_host (O : ElseI) {sv : Value} (hs : TypedV (simEnv B) storeT sv)
    (a : Nat) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [sv, refToValue (.host a), tyV (Ty.ref false (Ty.abs .any))]) :=
  dderivesB_of_ruleAt ruleAt_refOkHost (self_mem_conclAlts _) [("s", sv), ("a", .num (.natN a))]
    (QuantsOk.cons rfl (hs _ (valsOnly_bind _))
      (QuantsOk.cons rfl (typedV_addr a _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_baseAbs rfl rfl .any "ANY" rfl) premsB_nil

/-- `Ref_ok/exn`. -/
theorem dderivesB_refOk_exn (O : ElseI) {hn : H → String} {s : Store H}
    (hs : TypedV (simEnv B) storeT (storeV hn s)) {a : Nat} {e : ExnInst}
    (h : s.exns[a]? = some e) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [storeV hn s, refToValue (.exn a), tyV (Ty.ref false (Ty.abs .exn))]) := by
  have he : TypedV (simEnv B) (.varT "exninst" []) (exnInstV e) :=
    Typing.typedV_exninst e (typedV_list_iff.2 fun u hu => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
      exact Typing.typedV_val v)
  have hl : (s.exns.map exnInstV)[a]? = some (exnInstV e) := by simp [h]
  refine dderivesB_of_ruleAt ruleAt_refOkExn (self_mem_conclAlts _)
    [("s", storeV hn s), ("a", .num (.natN a)), ("exn", exnInstV e)]
    (QuantsOk.cons rfl (hs _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_addr a _ (valsOnly_bind _)) (QuantsOk.cons rfl (he _ (valsOnly_bind _))
        QuantsOk.nil)))
    (evalExp_baseAbs rfl rfl .exn "EXN" rfl) (premsB_one (.ifPr ?_))
  exact evalExp_cmpE_iff.2 ⟨exnInstV e, exnInstV e, evalExp_idxE_iff.2 ⟨_, a,
    evalExp_storeField rfl rfl, evalExp_var rfl, hl⟩, evalExp_var rfl, by simp [cmpValues]⟩

/-- Two premises, under the new reading. -/
theorem premsB_pair {env : Env} {O : ElseI} {els : Prop} {ρ : VarEnv} {p₁ p₂ : Prem}
    (h₁ : DPremB env O els ρ p₁) (h₂ : DPremB env O els ρ p₂) :
    ∀ p ∈ [p₁, p₂], DPremB env O els ρ p := by
  intro p hp
  rcases List.mem_pair.1 hp with rfl | rfl
  · exact h₁
  · exact h₂

/-- The premises of `Ref_ok/extern`. -/
theorem dpremsB_extern (O : ElseI) {els : Prop} {sv : Value} {r : Ref} (hn : r ≠ .null)
    (h : DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [sv, refToValue r, tyV (Ty.ref false (Ty.abs .any))])) :
    ∀ pr ∈ externPrems, DPremB (simEnv B) O els
      (VarEnv.empty.bindVals [("s", sv), ("ref", refToValue r)]) pr := by
  have hne : refToValue r ≠ .case "REF.NULL_ADDR" (.tuple []) := fun e =>
    hn (Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue_inj e)
  refine premsB_pair (.rulePr (evalArgs_nil _ _) (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl)
    (evalExp_case (evalExp_tup2 (evalExp_optE_none_iff.2 rfl)
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))))) h) (.ifPr ?_)
  exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl,
    evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩), by simp [cmpValues, hne]⟩

/-- `Ref_ok/extern`. -/
theorem dderivesB_refOk_extern (O : ElseI) {sv : Value} (hs : TypedV (simEnv B) storeT sv)
    {r : Ref} (hn : r ≠ .null)
    (h : DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [sv, refToValue r, tyV (Ty.ref false (Ty.abs .any))])) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [sv, refToValue (.extern r), tyV (Ty.ref false (Ty.abs .extern))]) :=
  dderivesB_of_ruleAt ruleAt_refOkExtern (self_mem_conclAlts _) [("s", sv), ("ref", refToValue r)]
    (QuantsOk.cons rfl (hs _ (valsOnly_bind _))
      (QuantsOk.cons rfl (Typing.typedV_ref r _ (valsOnly_bind _)) QuantsOk.nil))
    (evalExp_baseAbs rfl rfl .extern "EXTERN" rfl) (dpremsB_extern O hn h)

/-- **Every base rule fires** under `DDerivesB`, at the image of a typed store (`extern` from a
derivation of its premise). -/
theorem dderivesB_refOk_base (O : ElseI) {hn : H → String} {s : Store H}
    (hs : TypedV (simEnv B) storeT (storeV hn s)) {r : Ref} {p : CRefType} (hb : BaseOk s r p)
    (hext : ∀ r', r = .extern r' → DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [storeV hn s, refToValue r', tyV (Ty.ref false (Ty.abs .any))])) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [storeV hn s, refToValue r, tyV p]) := by
  cases hb with
  | null => exact dderivesB_refOk_null O hs
  | i31 b => exact dderivesB_refOk_i31 O hs b
  | @struct a si h =>
    exact dderivesB_refOk_dt O ruleAt_refOkStruct hs rfl (iv := structInstV si) (by simp [h]) rfl
      (tyBnd_structType hs h)
  | @array a ai h =>
    exact dderivesB_refOk_dt O ruleAt_refOkArray hs rfl (iv := arrayInstV ai) (by simp [h]) rfl
      (tyBnd_arrayType hs h)
  | @func a fi h =>
    exact dderivesB_refOk_dt O ruleAt_refOkFunc hs rfl (iv := funcInstV hn fi) (by simp [h]) rfl
      (tyBnd_funcType hs h)
  | exn h => exact dderivesB_refOk_exn O hs h
  | host a => exact dderivesB_refOk_host O hs a
  | extern _ hn => exact dderivesB_refOk_extern O hs hn (hext _ rfl)

/-- **`Ref_ok/sub`**, from its three premises. -/
theorem dderivesB_refOk_sub (O : ElseI) {sv : Value} (hs : TypedV (simEnv B) storeT sv) {r : Ref}
    {p rt : CRefType} (hp : Round4.tyBnd p = true) (hrt : Round4.tyBnd rt = true)
    (h₁ : DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [sv, refToValue r, tyV p]))
    (h₂ : DDerivesB (simEnv B) O "Reftype_ok" "%|-%:OK" [] (.tuple [ctx0V, tyV rt]))
    (h₃ : DDerivesB (simEnv B) O "Reftype_sub" "%|-%<:%" [] (.tuple [ctx0V, tyV p, tyV rt])) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [sv, refToValue r, tyV rt]) :=
  dderivesB_of_ruleAt ruleAt_refOkSub (self_mem_conclAlts _)
    [("s", sv), ("ref", refToValue r), ("rt", tyV rt), ("rt'", tyV p)]
    (QuantsOk.cons rfl (hs _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_ref r _ (valsOnly_bind _)) (QuantsOk.cons rfl
        (typedV_reftype hrt _ (valsOnly_bind _)) (QuantsOk.cons rfl
          (typedV_reftype hp _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
    (fun pr hpr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      rcases hpr with rfl | rfl | rfl
      · exact .rulePr (evalArgs_nil _ _)
          (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) h₁
      · exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 evalExp_ctx0 (evalExp_var rfl)) h₂
      · exact .rulePr (evalArgs_nil _ _)
          (evalExp_tup3 evalExp_ctx0 (evalExp_var rfl) (evalExp_var rfl)) h₃)

/-- **Core's `RefOk` is SpecTec's `Ref_ok`**, from `AgreeTy`'s introduction fields: at a bounded,
Core-valid reference type, on a valid store with a typed image. -/
theorem dderivesB_refOk_of_refOk (A : AgreeTy (simEnv B)) (O : ElseI) {hn : H → String}
    {s : Store H} (hs : TypedV (simEnv B) storeT (storeV hn s)) (hS : StoreOk s) :
    ∀ (r : Ref) {rt : CRefType}, RefOk s r rt → TyOk {} rt → Round4.tyBnd rt = true →
      DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [storeV hn s, refToValue r, tyV rt]) := by
  intro r
  induction r with
  | extern r' ih =>
    intro rt h hrt hb
    obtain ⟨p, hbase, hc⟩ := base_of_refOk h
    have hext : ∀ r'', Ref.extern r' = .extern r'' → DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
        (.tuple [storeV hn s, refToValue r'', tyV (Ty.ref false (Ty.abs .any))]) := by
      intro r'' e
      cases e
      cases hbase with
      | extern h' _ => exact ih h' (.ref (.abs _)) rfl
    exact lift_base A O hs hS hbase hext hc hrt hb
  | _ =>
    intro rt h hrt hb
    obtain ⟨p, hbase, hc⟩ := base_of_refOk h
    exact lift_base A O hs hS hbase (fun _ e => nomatch e) hc hrt hb
where
  /-- From a base rule to the target type, by `Ref_ok/sub` when they differ. -/
  lift_base (A : AgreeTy (simEnv B)) (O : ElseI) {hn : H → String} {s : Store H}
      (hs : TypedV (simEnv B) storeT (storeV hn s)) (hS : StoreOk s) {r : Ref} {p rt : CRefType}
      (hbase : BaseOk s r p)
      (hext : ∀ r', r = .extern r' → DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
        (.tuple [storeV hn s, refToValue r', tyV (Ty.ref false (Ty.abs .any))]))
      (hc : p = rt ∨ (TyOk {} rt ∧ Sub {} p rt)) (hrt : TyOk {} rt)
      (hb : Round4.tyBnd rt = true) :
      DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" [] (.tuple [storeV hn s, refToValue r, tyV rt]) :=
    have h₀ := dderivesB_refOk_base O hs hbase hext
    have hpb := base_ok_bnd hs hS hbase
    match hc with
    | .inl e => e ▸ h₀
    | .inr ⟨_, hsub⟩ => dderivesB_refOk_sub O hs hpb.2 hb h₀ (A.okIntro O rt hb hrt)
        (A.subIntro O p rt hpb.2 hb hpb.1 hrt hsub)

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

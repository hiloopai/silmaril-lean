module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.RefOk
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi4.WitnessBnd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Store
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Exn

/-!
# Round 6: Core's `RefOk` gives SpecTec's `Ref_ok`, from `AgreeTy`

* `base_of_refOk` (Core): every `RefOk` derivation starts at a base rule (`BaseOk`), and its type
  is the base type or Core-`Sub {}`-above it (composing `sub` steps by `Sub.trans`).
* `dderivesB_refOk_base`: each base rule fires under `DDerivesB`, at the image of a typed store.
* `dderivesB_refOk_sub`: `Ref_ok/sub` fires from its three premises.
* `dderivesB_refOk_of_refOk`: so, given `AgreeTy`'s introduction fields, Core's `RefOk` at a
  bounded, Core-valid type on a valid store with a typed image gives `Ref_ok` under `DDerivesB`.
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

/-! ## Base rules (Core) -/

/-- `RefOk`'s rules other than `sub`. -/
inductive BaseOk (s : Store H) : Ref → CRefType → Prop where
  | null : BaseOk s .null (.ref true .bot)
  | i31 (b : BitVec 31) : BaseOk s (.i31 b) (.ref false (.abs .i31))
  | struct {a : Nat} {si : StructInst} (h : s.structs[a]? = some si) :
      BaseOk s (.struct a) (.ref false (.defHeap si.type))
  | array {a : Nat} {ai : ArrayInst} (h : s.arrays[a]? = some ai) :
      BaseOk s (.array a) (.ref false (.defHeap ai.type))
  | func {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
      BaseOk s (.func a) (.ref false (.defHeap fi.type))
  | exn {a : Nat} {e : ExnInst} (h : s.exns[a]? = some e) :
      BaseOk s (.exn a) (.ref false (.abs .exn))
  | host (a : Nat) : BaseOk s (.host a) (.ref false (.abs .any))
  | extern {r : Ref} (h : RefOk s r (.ref false (.abs .any))) (hn : r ≠ .null) :
      BaseOk s (.extern r) (.ref false (.abs .extern))

/-- Core subtyping composes at the reference sort through a Core-valid middle type. -/
theorem sub_ref_trans {p rt' rt : CRefType} (h₁ : Sub {} p rt') (hm : TyOk {} rt')
    (h₂ : Sub {} rt' rt) : Sub {} p rt :=
  Sub.trans TypeCtx.ok_empty hm h₁ h₂

/-- **Every `RefOk` derivation starts at a base rule**, and its type is the base type or
`Sub {}`-above it. -/
theorem base_of_refOk {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∃ p, BaseOk s r p ∧ (p = rt ∨ (TyOk {} rt ∧ Sub {} p rt)) := by
  induction h with
  | null => exact ⟨_, .null, .inl rfl⟩
  | i31 b => exact ⟨_, .i31 b, .inl rfl⟩
  | struct h => exact ⟨_, .struct h, .inl rfl⟩
  | array h => exact ⟨_, .array h, .inl rfl⟩
  | func h => exact ⟨_, .func h, .inl rfl⟩
  | exn h => exact ⟨_, .exn h, .inl rfl⟩
  | host a => exact ⟨_, .host a, .inl rfl⟩
  | extern h hn _ => exact ⟨_, .extern h hn, .inl rfl⟩
  | sub _ hok hs ih =>
    obtain ⟨p, hb, hc⟩ := ih
    refine ⟨p, hb, .inr ⟨hok, ?_⟩⟩
    rcases hc with rfl | ⟨hm, hp⟩
    · exact hs
    · exact sub_ref_trans hp hm hs

/-! ## Store facts -/

/-- The type of a struct instance of a typed store is bounded. -/
theorem tyBnd_structType {hn : H → String} {s : Store H}
    (hs : TypedV (simEnv B) storeT (storeV hn s)) {a : Nat} {si : StructInst}
    (h : s.structs[a]? = some si) : Round4.tyBnd si.type = true := by
  have ht := ConfigOk.structOfStore_simEnv hn s si hs (List.mem_of_getElem? h)
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    Round5.Pos.findTyp_structinst (ht _ ConfigOk.valsOnly_empty)
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  exact Round5.Multi.tyBnd_of_tyI si.type (.inl hF.1)

/-- The type of an array instance of a typed store is bounded. -/
theorem tyBnd_arrayType {hn : H → String} {s : Store H}
    (hs : TypedV (simEnv B) storeT (storeV hn s)) {a : Nat} {ai : ArrayInst}
    (h : s.arrays[a]? = some ai) : Round4.tyBnd ai.type = true := by
  have ht := ConfigOk.arrayOfStore_simEnv hn s ai hs (List.mem_of_getElem? h)
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    Round5.Pos.findTyp_arrayinst (ht _ ConfigOk.valsOnly_empty)
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  exact Round5.Multi.tyBnd_of_tyI ai.type (.inl hF.1)

/-- The type of a function instance of a typed store is bounded. -/
theorem tyBnd_funcType {hn : H → String} {s : Store H}
    (hs : TypedV (simEnv B) storeT (storeV hn s)) {a : Nat} {fi : FuncInst H}
    (h : s.funcs[a]? = some fi) : Round4.tyBnd fi.type = true := by
  have ht := ConfigOk.funcinst_of_store hn s a fi hs h
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    ConfigOk.findTyp_funcinst (ht _ ConfigOk.valsOnly_empty)
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  exact Round5.Multi.tyBnd_of_tyI fi.type (.inl hF.1)

/-- A base type on a valid store with a typed image is Core-valid and bounded. -/
theorem base_ok_bnd {hn : H → String} {s : Store H}
    (hs : TypedV (simEnv B) storeT (storeV hn s)) (hS : StoreOk s) {r : Ref} {p : CRefType}
    (hb : BaseOk s r p) : TyOk {} p ∧ Round4.tyBnd p = true := by
  cases hb with
  | null => exact ⟨.ref .bot, rfl⟩
  | i31 => exact ⟨.ref (.abs _), rfl⟩
  | struct h =>
    exact ⟨tyOk_defRef (hS.structsClosed _ (List.mem_of_getElem? h)), tyBnd_structType hs h⟩
  | array h =>
    exact ⟨tyOk_defRef (hS.arraysClosed _ (List.mem_of_getElem? h)), tyBnd_arrayType hs h⟩
  | func h => exact ⟨tyOk_defRef (tyOk_func_type hS h), tyBnd_funcType hs h⟩
  | exn => exact ⟨.ref (.abs _), rfl⟩
  | host => exact ⟨.ref (.abs _), rfl⟩
  | extern => exact ⟨.ref (.abs _), rfl⟩

/-! ## The base rules, under `DDerivesB` -/

/-- A natural number is an `addr`. -/
theorem typedV_addr (a : Nat) : TypedV (simEnv B) (.varT "addr" []) (.num (.natN a)) :=
  Typing.typedV_natAlias Typing.findTyp_addr a

/-- `s.F` of the image of a store, for a field `F` holding the list `l`. -/
theorem evalExp_storeField {ρ : VarEnv} {sv : Value} {F : AtomS} {l : List Value}
    (hS : ρ.findVal? "s" = some sv) (hF : sv.field? F = some (.list l)) :
    EvalExp (simEnv B) ρ (.dotE (.varE "s") F) (.list l) :=
  evalExp_dotE_iff.2 ⟨sv, evalExp_var hS, hF⟩

/-- The premise `s.F[a].TYPE = dt` holds at an instance of type `d` at address `a`. -/
theorem dpremB_typePrem {O : ElseI} {els : Prop} {ρ : VarEnv} {sv : Value} {F : AtomS}
    {l : List Value} {a : Nat} {iv : Value} {d : DefType}
    (hS : ρ.findVal? "s" = some sv) (hA : ρ.findVal? "a" = some (.num (.natN a)))
    (hD : ρ.findVal? "dt" = some (tyV d)) (hF : sv.field? F = some (.list l))
    (hl : l[a]? = some iv) (hT : iv.field? "TYPE" = some (tyV d)) :
    DPremB (simEnv B) O els ρ (typePrem F) :=
  .ifPr (evalExp_cmpE_iff.2 ⟨tyV d, tyV d,
    evalExp_dotE_iff.2 ⟨iv, evalExp_idxE_iff.2 ⟨.list l, a, evalExp_storeField hS hF,
      evalExp_var hA, hl⟩, hT⟩, evalExp_var hD, by simp [cmpValues]⟩)

/-- The conclusion of a base rule, at a defined type. -/
theorem evalExp_baseDt {ρ : VarEnv} {op : MixopS} {sv x : Value} {d : DefType}
    (hS : ρ.findVal? "s" = some sv) (hA : ρ.findVal? "a" = some x)
    (hD : ρ.findVal? "dt" = some (tyV d)) :
    EvalExp (simEnv B) ρ (baseConcl op "a" dtHeapE)
      (.tuple [sv, .case op x, tyV (Ty.ref false (Ty.defHeap d))]) :=
  evalExp_tup3 (evalExp_var hS) (evalExp_case (evalExp_var hA))
    (evalExp_case (evalExp_tup2 (evalExp_optE_none_iff.2 rfl)
      (RefsGC.evalExp_sub_of (evalExp_var hD))))

/-- The conclusion of a base rule, at an abstract heap type. -/
theorem evalExp_baseAbs {ρ : VarEnv} {op : MixopS} {x : IL.Id} {sv w : Value}
    (hS : ρ.findVal? "s" = some sv) (hX : ρ.findVal? x = some w) (a : AbsHeapType)
    (op' : MixopS) (hop : Silmaril.SpecTec.Equiv.Validation.absV a = .case op' (.tuple [])) :
    EvalExp (simEnv B) ρ (baseConcl op x (absE op'))
      (.tuple [sv, .case op w, tyV (Ty.ref false (Ty.abs a))]) := by
  have e : tyV (Ty.ref false (Ty.abs a)) = .case "REF" (.tuple [.opt none, .case op' (.tuple [])]) :=
    by simp only [tyV, hop]; rfl
  rw [e]
  exact evalExp_tup3 (evalExp_var hS) (evalExp_case (evalExp_var hX))
    (evalExp_case (evalExp_tup2 (evalExp_optE_none_iff.2 rfl)
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))))

/-- The quantifiers `s`, `a`, `dt` of a base rule at a defined type. -/
theorem quantsOk_addrDt {sv : Value} (hs : TypedV (simEnv B) storeT sv) (a : Nat) {d : DefType}
    (hd : Round4.tyBnd d = true) :
    QuantsOk (simEnv B) (VarEnv.empty.bindVals [("s", sv), ("a", .num (.natN a)), ("dt", tyV d)])
      addrDtQs :=
  QuantsOk.cons rfl (hs _ (valsOnly_bind _)) (QuantsOk.cons rfl (typedV_addr a _ (valsOnly_bind _))
    (QuantsOk.cons rfl (Round5.Pos.typedV_deftype d hd _ (valsOnly_bind _)) QuantsOk.nil))

/-- A base rule at a defined type, from the instance list of its store field. -/
theorem dderivesB_refOk_dt (O : ElseI) {k : Nat} {nm : IL.Id} {op : MixopS} {F : AtomS}
    {sv : Value} {l : List Value}
    (hr : Equiv.Validation.HasRuleAt (simEnv B) "Ref_ok" "%|-%:%" k
      (.ruleD nm addrDtQs "%|-%:%" (baseConcl op "a" dtHeapE) [typePrem F]))
    (hs : TypedV (simEnv B) storeT sv) (hF : sv.field? F = some (.list l)) {a : Nat} {iv : Value}
    {d : DefType} (hl : l[a]? = some iv) (hT : iv.field? "TYPE" = some (tyV d))
    (hd : Round4.tyBnd d = true) :
    DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
      (.tuple [sv, .case op (.num (.natN a)), tyV (Ty.ref false (Ty.defHeap d))]) :=
  dderivesB_of_ruleAt hr (self_mem_conclAlts _) [("s", sv), ("a", .num (.natN a)), ("dt", tyV d)]
    (quantsOk_addrDt hs a hd) (evalExp_baseDt rfl rfl rfl)
    (premsB_one (dpremB_typePrem rfl rfl rfl hF hl hT))

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

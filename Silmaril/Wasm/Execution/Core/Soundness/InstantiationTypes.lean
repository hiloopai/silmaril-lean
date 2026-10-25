module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping
public import Silmaril.Wasm.Validation.Subtyping.Check
public import Silmaril.Wasm.Validation.RollClosed

@[expose] public section

/-! # Closed types of a valid module (helpers for `Instantiate.alloc_ok`)

* `TypesOk.tyOk_empty`: the defined types of a valid module are valid in the
  empty context (what `Moduleinst_ok` requires of `TYPES`);
* closing a *source* value/reference/heap type against those types gives a
  type valid in the empty context (`TyOk.closeVal_empty` & co.);
* `Sub.empty_of_closed`: context subtyping between types valid in `{}` holds
  in `{}`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- The closed defined types of a valid module are valid in the empty context.
(Metatheory of rolling: `Rectype_ok` of a group in the extended context gives
`Rectype_ok2` of the rolled group.) -/
theorem TypesOk.tyOk_empty {rts : List RecType} {dts : List DefType}
    (h : TypesOk {} rts dts) : ∀ d ∈ dts, TyOk {} d := by
  exact h.tyOk_empty'

/-! ## The subtyping checker does not depend on the context on closed types -/

section CheckClosed

theorem Ty.closed_of_tyOk_empty {k : TKind} {t : Ty k} (h : TyOk {} t) : t.Closed := by
  unfold Ty.Closed
  apply List.eq_nil_iff_forall_not_mem.2
  intro y hy
  have := TyOk.freeIdx_lt h y hy
  simp at this

/-- Substituting closed type uses for `REC` variables adds no free indices. -/
theorem Ty.freeIdx_subst_recv {k : TKind} (t : Ty k) :
    ∀ σ : Subst, (∀ x, σ (.idx x) = none) →
      (∀ j u, σ (.recv j) = some u → u.freeIdx = []) → ∀ y ∈ (t.subst σ).freeIdx, y ∈ t.freeIdx := by
  induction t with
  | idx x =>
    intro σ hσ _ y hy
    simp only [Ty.subst, hσ, Option.getD_none] at hy; exact hy
  | recv i =>
    intro σ _ hr y hy
    simp only [Ty.subst] at hy
    cases h : σ (.recv i) with
    | none => simp [h, Ty.freeIdx] at hy
    | some u => simp [h, hr i u h] at hy
  | group subs ih =>
    intro σ hσ hr y hy
    exact ih σ.minusRecs (fun x => hσ x) (fun j u h => by simp [Subst.minusRecs] at h) y hy
  | cons a l iha ihl =>
    intro σ hσ hr y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    exact hy.imp (iha σ hσ hr y) (ihl σ hσ hr y)
  | func ps rs ihp ihr =>
    intro σ hσ hr y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    exact hy.imp (ihp σ hσ hr y) (ihr σ hσ hr y)
  | sub fin sups b ihs ihb =>
    intro σ hσ hr y hy
    simp only [Ty.subst, Ty.freeIdx, List.mem_append] at hy ⊢
    exact hy.imp (ihs σ hσ hr y) (ihb σ hσ hr y)
  | dt d ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | defn g i ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | use u ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | ref n h ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | refv r ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | val t ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | field m s ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | struct fs ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | array f ih => intro σ hσ hr y hy; exact ih σ hσ hr y hy
  | _ => intro σ _ _ y hy; simp [Ty.subst, Ty.freeIdx] at hy

theorem Ty.closed_of_mem_toList {k : TKind} {l : Ty (.list k)} (hl : l.Closed) {a : Ty k}
    (ha : a ∈ l.toList) : a.Closed := by
  unfold Ty.Closed at *
  apply List.eq_nil_iff_forall_not_mem.2
  intro y hy
  have : y ∈ (Ty.ofList l.toList).freeIdx := (Ty.mem_freeIdx_ofList _).2 ⟨a, ha, hy⟩
  rw [Ty.ofList_toList, hl] at this
  cases this

/-- The declared supertypes of a closed defined type are closed. -/
theorem supersOf_closed {d : DefType} (hd : d.Closed) : ∀ u ∈ supersOf d, u.Closed := by
  intro u hu
  unfold supersOf at hu
  cases hun : unrolldt d with
  | none => rw [hun] at hu; cases hu
  | some st =>
    rw [hun] at hu
    cases d with
    | defn g i =>
    cases g with
    | group subs =>
    simp only [unrolldt, unrollrt, Ty.subs] at hun
    have hst : st.Closed := by
      have hmem := List.mem_of_getElem? hun
      apply Ty.closed_of_mem_toList (l := subs.subst _) _ hmem
      unfold Ty.Closed at hd ⊢
      apply List.eq_nil_iff_forall_not_mem.2
      intro y hy
      have := Ty.freeIdx_subst_recv subs _ (fun _ => rfl) (fun j u h => by
        simp only at h
        split at h
        · cases h; exact hd
        · cases h) y hy
      have hd' : subs.freeIdx = [] := hd
      rw [hd'] at this
      cases this
    cases st with
    | sub fin sups b =>
    simp only [Ty.supers] at hu
    have hs : sups.Closed := by
      unfold Ty.Closed at hst ⊢; simp only [Ty.freeIdx, List.append_eq_nil_iff] at hst; exact hst.1
    exact Ty.closed_of_mem_toList hs hu

theorem resolve_closed (Δ Δ' : TypeCtx) {u : CTypeUse} (hu : u.Closed) :
    Δ.resolve u = Δ'.resolve u := by
  cases u with
  | dt d => rfl
  | recv i => rfl
  | idx x => simp [Ty.Closed, Ty.freeIdx] at hu

theorem resolve_some_closed {Δ : TypeCtx} {u : CTypeUse} (hu : u.Closed) {d : DefType}
    (h : Δ.resolve u = some d) : d.Closed := by
  cases u with
  | dt d' => simp [TypeCtx.resolve] at h; subst h; exact hu
  | recv i => simp [TypeCtx.resolve] at h
  | idx x => simp [Ty.Closed, Ty.freeIdx] at hu

theorem any_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih fun b hb => h b (by simp [hb])]

theorem reach_closed (Δ Δ' : TypeCtx) {P P' : DefType → Bool}
    (hP : ∀ e : DefType, e.Closed → P e = P' e) :
    ∀ (n : Nat) (d : DefType), d.Closed → Δ.reach P n d = Δ'.reach P' n d := by
  intro n
  induction n with
  | zero => intro d hd; simp only [TypeCtx.reach]; exact hP d hd
  | succ n ih =>
    intro d hd
    simp only [TypeCtx.reach]
    rw [hP d hd]
    congr 1
    apply any_congr'
    intro u hu
    have huc := supersOf_closed hd u hu
    rw [resolve_closed Δ Δ' huc]
    cases h : Δ'.resolve u with
    | none => rfl
    | some d' => exact ih d' (resolve_some_closed huc h)

theorem fuel_closed (Δ : TypeCtx) {d : DefType} (hd : d.Closed) : Δ.fuel d = mu0 d := by
  simp [TypeCtx.fuel, show d.freeIdx = [] from hd]

theorem checkDef_closed (Δ Δ' : TypeCtx) {d₁ d₂ : DefType} (h₁ : d₁.Closed) (h₂ : d₂.Closed) :
    Δ.checkDef d₁ d₂ = Δ'.checkDef d₁ d₂ := by
  unfold TypeCtx.checkDef
  rw [fuel_closed Δ h₁, fuel_closed Δ' h₁]
  apply reach_closed Δ Δ' _ _ _ h₁
  intro e he
  simp [Ty.clos, Ty.substAll_closed he, Ty.substAll_closed h₂]

theorem checkUseAbs_closed (Δ Δ' : TypeCtx) {u : CTypeUse} (hu : u.Closed) (b : AbsHeapType) :
    Δ.checkUseAbs u b = Δ'.checkUseAbs u b := by
  unfold TypeCtx.checkUseAbs
  rw [resolve_closed Δ Δ' hu]

theorem checkHeap_closed (Δ Δ' : TypeCtx) {a b : CHeapType} (ha : a.Closed) (hb : b.Closed) :
    Δ.checkHeap a b = Δ'.checkHeap a b := by
  cases a with
  | bot => rfl
  | abs x =>
    cases b with
    | abs y => rfl
    | bot => rfl
    | use u =>
      simp only [TypeCtx.checkHeap]
      cases botTop x with
      | none => rfl
      | some t => exact checkUseAbs_closed Δ Δ' hb t
  | use u₁ =>
    have hu₁ : u₁.Closed := ha
    cases b with
    | abs y => exact checkUseAbs_closed Δ Δ' hu₁ y
    | bot => rfl
    | use u₂ =>
      have hu₂ : u₂.Closed := hb
      simp only [TypeCtx.checkHeap]
      rw [resolve_closed Δ Δ' hu₁, resolve_closed Δ Δ' hu₂]
      cases h₁ : Δ'.resolve u₁ with
      | none => cases Δ'.resolve u₂ <;> rfl
      | some d₁ =>
        cases h₂ : Δ'.resolve u₂ with
        | none => rfl
        | some d₂ =>
          exact checkDef_closed Δ Δ' (resolve_some_closed hu₁ h₁) (resolve_some_closed hu₂ h₂)

theorem checkRef_closed (Δ Δ' : TypeCtx) {a b : CRefType} (ha : a.Closed) (hb : b.Closed) :
    Δ.checkRef a b = Δ'.checkRef a b := by
  cases a with
  | ref n₁ h₁ =>
    cases b with
    | ref n₂ h₂ =>
      simp only [TypeCtx.checkRef]
      rw [checkHeap_closed Δ Δ' (a := h₁) ha hb]

theorem checkVal_closed (Δ Δ' : TypeCtx) {a b : CValType} (ha : a.Closed) (hb : b.Closed) :
    Δ.checkVal a b = Δ'.checkVal a b := by
  cases a <;> cases b <;> try rfl
  simp only [TypeCtx.checkVal]
  exact checkRef_closed Δ Δ' ha hb

theorem checkStorage_closed (Δ Δ' : TypeCtx) {a b : CStorageType} (ha : a.Closed) (hb : b.Closed) :
    Δ.checkStorage a b = Δ'.checkStorage a b := by
  cases a <;> cases b <;> try rfl
  simp only [TypeCtx.checkStorage]
  exact checkVal_closed Δ Δ' ha hb

theorem checkField_closed (Δ Δ' : TypeCtx) {a b : CFieldType} (ha : a.Closed) (hb : b.Closed) :
    Δ.checkField a b = Δ'.checkField a b := by
  cases a with
  | field m₁ z₁ =>
    cases b with
    | field m₂ z₂ =>
      have hz₁ : z₁.Closed := ha
      have hz₂ : z₂.Closed := hb
      cases m₁ <;> cases m₂ <;> simp only [TypeCtx.checkField] <;>
        (rw [checkStorage_closed Δ Δ' hz₁ hz₂]; try rw [checkStorage_closed Δ Δ' hz₂ hz₁])

theorem forall2B_congr {α : Type} {f g : α → α → Bool} :
    ∀ {l₁ l₂ : List α}, (∀ a ∈ l₁, ∀ b ∈ l₂, f a b = g a b) → forall2B f l₁ l₂ = forall2B g l₁ l₂
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [forall2B]
    rw [h a (by simp) b (by simp), forall2B_congr fun x hx y hy => h x (by simp [hx]) y (by simp [hy])]

theorem checkComp_closed (Δ Δ' : TypeCtx) {a b : CCompType} (ha : a.Closed) (hb : b.Closed) :
    Δ.checkComp a b = Δ'.checkComp a b := by
  cases a <;> cases b <;> try rfl
  · rename_i fs₁ fs₂
    have h₁ : fs₁.Closed := ha
    have h₂ : fs₂.Closed := hb
    simp only [TypeCtx.checkComp]
    congr 1
    apply forall2B_congr
    intro x hx y hy
    exact checkField_closed Δ Δ' (Ty.closed_of_mem_toList h₁ (List.mem_of_mem_take hx))
      (Ty.closed_of_mem_toList h₂ hy)
  · exact checkField_closed Δ Δ' ha hb
  · rename_i ps₁ rs₁ ps₂ rs₂
    have hp₁ : ps₁.Closed := by
      unfold Ty.Closed at ha ⊢; simp only [Ty.freeIdx, List.append_eq_nil_iff] at ha; exact ha.1
    have hr₁ : rs₁.Closed := by
      unfold Ty.Closed at ha ⊢; simp only [Ty.freeIdx, List.append_eq_nil_iff] at ha; exact ha.2
    have hp₂ : ps₂.Closed := by
      unfold Ty.Closed at hb ⊢; simp only [Ty.freeIdx, List.append_eq_nil_iff] at hb; exact hb.1
    have hr₂ : rs₂.Closed := by
      unfold Ty.Closed at hb ⊢; simp only [Ty.freeIdx, List.append_eq_nil_iff] at hb; exact hb.2
    simp only [TypeCtx.checkComp]
    rw [forall2B_congr (g := Δ'.checkVal) fun x hx y hy =>
        checkVal_closed Δ Δ' (Ty.closed_of_mem_toList hp₂ hx) (Ty.closed_of_mem_toList hp₁ hy),
      forall2B_congr (g := Δ'.checkVal) fun x hx y hy =>
        checkVal_closed Δ Δ' (Ty.closed_of_mem_toList hr₁ hx) (Ty.closed_of_mem_toList hr₂ hy)]

theorem checkK_closed (Δ Δ' : TypeCtx) :
    ∀ (k : TKind) {a b : Ty k}, a.Closed → b.Closed → Sub.checkK Δ k a b = Sub.checkK Δ' k a b
  | .heap, _, _, ha, hb => checkHeap_closed Δ Δ' ha hb
  | .ref, _, _, ha, hb => checkRef_closed Δ Δ' ha hb
  | .val, _, _, ha, hb => checkVal_closed Δ Δ' ha hb
  | .storage, _, _, ha, hb => checkStorage_closed Δ Δ' ha hb
  | .field, _, _, ha, hb => checkField_closed Δ Δ' ha hb
  | .comp, _, _, ha, hb => checkComp_closed Δ Δ' ha hb
  | .def, _, _, ha, hb => checkDef_closed Δ Δ' ha hb
  | .list k, a, b, ha, hb => by
    simp only [Sub.checkK]
    exact forall2B_congr fun x hx y hy =>
      checkK_closed Δ Δ' k (Ty.closed_of_mem_toList ha hx) (Ty.closed_of_mem_toList hb hy)
  | .use, _, _, _, _ => rfl
  | .sub, _, _, _, _ => rfl
  | .group, _, _, _, _ => rfl

end CheckClosed


/-- Context subtyping between two types that are valid in the empty context
holds in the empty context (the context is closed and has no `RECS`). -/
theorem Sub.empty_of_closed {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {k : TKind}
    {a b : Ty k} (ha : TyOk {} a) (hb : TyOk {} b) (h : Sub Δ a b) : Sub {} a b := by
  have hc := Sub.check_complete hΔ hr h (TyOk.of_empty _ ha) (TyOk.of_empty _ hb)
  unfold Sub.check at hc
  rw [checkK_closed Δ {} k (Ty.closed_of_tyOk_empty ha) (Ty.closed_of_tyOk_empty hb)] at hc
  exact Sub.check_sound hc

/-! ## Closing source types -/

theorem TyOk.closeHeap_empty {dts : List DefType} (hd : ∀ d ∈ dts, TyOk {} d) {Δ : TypeCtx}
    (hΔ : Δ.types = dts) {h : HeapType}
    (hok : TyOk Δ ((liftHeap h).substAll (dts.map .dt))) :
    TyOk {} ((liftHeap h).substAll (dts.map .dt)) := by
  cases h with
  | abstract a => exact .abs a
  | typeIdx x =>
    simp only [liftHeap, liftTypeIdx, Ty.substAll, Ty.subst, Subst.all, List.getElem?_map] at hok ⊢
    cases hx : dts[x.toNat]? with
    | none =>
      rw [hx] at hok
      simp only [Option.map_none, Option.getD_none] at hok
      cases hok with
      | use h => cases h with
        | idx h => rw [hΔ, hx] at h; cases h
    | some d =>
      simp only [Option.map_some, Option.getD_some]
      exact .use (.dt (hd d (List.mem_of_getElem? hx)))

theorem TyOk.closeRef_empty {dts : List DefType} (hd : ∀ d ∈ dts, TyOk {} d) {Δ : TypeCtx}
    (hΔ : Δ.types = dts) {r : RefType}
    (hok : TyOk Δ ((liftRef r).substAll (dts.map .dt))) :
    TyOk {} ((liftRef r).substAll (dts.map .dt)) := by
  simp only [liftRef, Ty.substAll, Ty.subst] at hok ⊢
  cases hok with
  | ref h => exact .ref (TyOk.closeHeap_empty hd hΔ h)

theorem TyOk.closeVal_empty {dts : List DefType} (hd : ∀ d ∈ dts, TyOk {} d) {Δ : TypeCtx}
    (hΔ : Δ.types = dts) {t : ValType}
    (hok : TyOk Δ ((liftVal t).substAll (dts.map .dt))) :
    TyOk {} ((liftVal t).substAll (dts.map .dt)) := by
  cases t with
  | num t => exact .num t
  | vec t => exact .vec t
  | ref r =>
    simp only [liftVal, Ty.substAll, Ty.subst] at hok ⊢
    cases hok with
    | refv h => exact .refv (TyOk.closeRef_empty hd hΔ h)

end Silmaril.Wasm.Execution.Core

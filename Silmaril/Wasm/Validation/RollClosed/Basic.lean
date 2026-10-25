module

public import Silmaril.Wasm.Validation.Subtyping.DefInv

@[expose] public section

/-! # Rolling metatheory: basic helpers

* weakening of `TYPES` (from `[]`) and of `RECS` (from `[]`), copied from the runtime
  development (`Execution/Core/Soundness/RefTyping.lean`) with an `RC` suffix;
* `RollClosed.Lv n O t`: the *leaves* of a heap-shaped type are `REC i` with `i < n`,
  abstract heap types, or `_DEF d` with `O d` (no `_IDX`, no bare deftypes).
-/

namespace Silmaril.Wasm.Validation

namespace RollClosed

/-! ## Weakening -/

theorem subst_all_nil : Subst.all [] = fun _ => none := by
  funext v; cases v <;> rfl

theorem clos_nil {k : TKind} (t : Ty k) : t.clos [] = t := by
  simp only [Ty.clos, closDefTypes, List.foldl_nil, List.map_nil, Ty.substAll, subst_all_nil]
  exact Ty.subst_none t

theorem unrollUse_wkRC {Δ : TypeCtx} {u : CTypeUse} (hu : TyOk Δ u) (hΔ : Δ.types = [])
    (T : List DefType) : ({ Δ with types := T } : TypeCtx).unrollUse u = Δ.unrollUse u := by
  cases u with
  | idx x => cases hu with | idx h => simp [hΔ] at h
  | recv i => rfl
  | dt d => rfl

mutual

theorem TyOk.wkTypesRC (T : List DefType) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k},
    TyOk Δ t → Δ.types = [] → TyOk { Δ with types := T } t
  | _, _, _, .idx h, hΔ => by simp [hΔ] at h
  | _, _, _, .recv h, _ => .recv h
  | _, _, _, .dt h, hΔ => .dt (TyOk.wkTypesRC T h hΔ)
  | _, _, _, .defn h hi, hΔ => .defn (GroupOk2.wkTypesRC T h hΔ) hi
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, hΔ => .use (TyOk.wkTypesRC T h hΔ)
  | _, _, _, .ref h, hΔ => .ref (TyOk.wkTypesRC T h hΔ)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, hΔ => .refv (TyOk.wkTypesRC T h hΔ)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, hΔ => .val (TyOk.wkTypesRC T h hΔ)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, hΔ => .field (TyOk.wkTypesRC T h hΔ)
  | _, _, _, .struct h, hΔ => .struct (TyOk.wkTypesRC T h hΔ)
  | _, _, _, .array h, hΔ => .array (TyOk.wkTypesRC T h hΔ)
  | _, _, _, .func hp hr, hΔ => .func (TyOk.wkTypesRC T hp hΔ) (TyOk.wkTypesRC T hr hΔ)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, hΔ => .cons (TyOk.wkTypesRC T ha hΔ) (TyOk.wkTypesRC T hl hΔ)

theorem SubOk2.wkTypesRC (T : List DefType) : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat},
    SubOk2 Δ st i → Δ.types = [] → SubOk2 { Δ with types := T } st i
  | _, _, _, .noSuper hct, hΔ => .noSuper (TyOk.wkTypesRC T hct hΔ)
  | _, _, _, .oneSuper hu hb hunroll hct hsub, hΔ =>
    .oneSuper (TyOk.wkTypesRC T hu hΔ) hb (by rw [unrollUse_wkRC hu hΔ]; exact hunroll)
      (TyOk.wkTypesRC T hct hΔ) (Sub.wkTypesRC T hsub hΔ)

theorem GroupOk2.wkTypesRC (T : List DefType) : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat},
    GroupOk2 Δ g i → Δ.types = [] → GroupOk2 { Δ with types := T } g i
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons h hs, hΔ => .cons (SubOk2.wkTypesRC T h hΔ) (GroupOk2.wkTypesRC T hs hΔ)

theorem Sub.wkTypesRC (T : List DefType) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k},
    Sub Δ a b → Δ.types = [] → Sub { Δ with types := T } a b
  | _, _, _, _, .heapRefl, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ =>
    .heapTrans (TyOk.wkTypesRC T hok hΔ) (Sub.wkTypesRC T h₁ hΔ) (Sub.wkTypesRC T h₂ hΔ)
  | _, _, _, _, .eqAny, _ => .eqAny
  | _, _, _, _, .i31Eq, _ => .i31Eq
  | _, _, _, _, .structEq, _ => .structEq
  | _, _, _, _, .arrayEq, _ => .arrayEq
  | _, _, _, _, .defStruct h, _ => .defStruct h
  | _, _, _, _, .defArray h, _ => .defArray h
  | _, _, _, _, .defFunc h, _ => .defFunc h
  | _, _, _, _, .defDef h, hΔ => .defDef (Sub.wkTypesRC T h hΔ)
  | _, _, _, _, .idxL hx _, hΔ => by simp [hΔ] at hx
  | _, _, _, _, .idxR hx _, hΔ => by simp [hΔ] at hx
  | _, _, _, _, .recStruct h, _ => .recStruct h
  | _, _, _, _, .recArray h, _ => .recArray h
  | _, _, _, _, .recFunc h, _ => .recFunc h
  | _, _, _, _, .recSub h hj, _ => .recSub h hj
  | _, _, _, _, .none hs hb, hΔ => .none (Sub.wkTypesRC T hs hΔ) hb
  | _, _, _, _, .nofunc hs hb, hΔ => .nofunc (Sub.wkTypesRC T hs hΔ) hb
  | _, _, _, _, .noexn hs hb, hΔ => .noexn (Sub.wkTypesRC T hs hΔ) hb
  | _, _, _, _, .noextern hs hb, hΔ => .noextern (Sub.wkTypesRC T hs hΔ) hb
  | _, _, _, _, .bot, _ => .bot
  | _, _, _, _, .refNonNull h, hΔ => .refNonNull (Sub.wkTypesRC T h hΔ)
  | _, _, _, _, .refNull h, hΔ => .refNull (Sub.wkTypesRC T h hΔ)
  | _, _, _, _, .num, _ => .num
  | _, _, _, _, .vec, _ => .vec
  | _, _, _, _, .refv h, hΔ => .refv (Sub.wkTypesRC T h hΔ)
  | _, _, _, _, .botv, _ => .botv
  | _, _, _, _, .val h, hΔ => .val (Sub.wkTypesRC T h hΔ)
  | _, _, _, _, .pack, _ => .pack
  | _, _, _, _, .fieldConst h, hΔ => .fieldConst (Sub.wkTypesRC T h hΔ)
  | _, _, _, _, .fieldVar h₁ h₂, hΔ => .fieldVar (Sub.wkTypesRC T h₁ hΔ) (Sub.wkTypesRC T h₂ hΔ)
  | _, _, _, _, .struct h, hΔ => .struct (Sub.wkTypesRC T h hΔ)
  | _, _, _, _, .array h, hΔ => .array (Sub.wkTypesRC T h hΔ)
  | _, _, _, _, .func hp hr, hΔ => .func (Sub.wkTypesRC T hp hΔ) (Sub.wkTypesRC T hr hΔ)
  | _, _, _, _, .defRefl h, hΔ => .defRefl (by rw [hΔ, clos_nil, clos_nil] at h; rw [h])
  | _, _, _, _, .defSuper h hj hs, hΔ => .defSuper h hj (Sub.wkTypesRC T hs hΔ)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons h hl, hΔ => .cons (Sub.wkTypesRC T h hΔ) (Sub.wkTypesRC T hl hΔ)

end

theorem TyOk.wkRecsRC (R : List CSubType) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k},
    TyOk Δ t → Δ.recs = [] → TyOk { Δ with recs := R } t
  | _, _, _, .idx h, _ => .idx h
  | _, _, _, .recv h, hΔ => by simp [hΔ] at h
  | _, _, _, .dt h, hΔ => .dt (TyOk.wkRecsRC R h hΔ)
  | _, _, _, .defn h hi, _ => .defn h hi
  | _, _, _, .abs a, _ => .abs a
  | _, _, _, .bot, _ => .bot
  | _, _, _, .use h, hΔ => .use (TyOk.wkRecsRC R h hΔ)
  | _, _, _, .ref h, hΔ => .ref (TyOk.wkRecsRC R h hΔ)
  | _, _, _, .num t, _ => .num t
  | _, _, _, .vec t, _ => .vec t
  | _, _, _, .refv h, hΔ => .refv (TyOk.wkRecsRC R h hΔ)
  | _, _, _, .botv, _ => .botv
  | _, _, _, .val h, hΔ => .val (TyOk.wkRecsRC R h hΔ)
  | _, _, _, .pack p, _ => .pack p
  | _, _, _, .field h, hΔ => .field (TyOk.wkRecsRC R h hΔ)
  | _, _, _, .struct h, hΔ => .struct (TyOk.wkRecsRC R h hΔ)
  | _, _, _, .array h, hΔ => .array (TyOk.wkRecsRC R h hΔ)
  | _, _, _, .func hp hr, hΔ => .func (TyOk.wkRecsRC R hp hΔ) (TyOk.wkRecsRC R hr hΔ)
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons ha hl, hΔ => .cons (TyOk.wkRecsRC R ha hΔ) (TyOk.wkRecsRC R hl hΔ)

theorem Sub.wkRecsRC (R : List CSubType) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k},
    Sub Δ a b → Δ.recs = [] → Sub { Δ with recs := R } a b
  | _, _, _, _, .heapRefl, _ => .heapRefl
  | _, _, _, _, .heapTrans hok h₁ h₂, hΔ =>
    .heapTrans (TyOk.wkRecsRC R hok hΔ) (Sub.wkRecsRC R h₁ hΔ) (Sub.wkRecsRC R h₂ hΔ)
  | _, _, _, _, .eqAny, _ => .eqAny
  | _, _, _, _, .i31Eq, _ => .i31Eq
  | _, _, _, _, .structEq, _ => .structEq
  | _, _, _, _, .arrayEq, _ => .arrayEq
  | _, _, _, _, .defStruct h, _ => .defStruct h
  | _, _, _, _, .defArray h, _ => .defArray h
  | _, _, _, _, .defFunc h, _ => .defFunc h
  | _, _, _, _, .defDef h, hΔ => .defDef (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .idxL hx h, hΔ => .idxL hx (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .idxR hx h, hΔ => .idxR hx (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .recStruct h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recArray h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recFunc h, hΔ => by simp [hΔ] at h
  | _, _, _, _, .recSub h _, hΔ => by simp [hΔ] at h
  | _, _, _, _, .none hs hb, hΔ => .none (Sub.wkRecsRC R hs hΔ) hb
  | _, _, _, _, .nofunc hs hb, hΔ => .nofunc (Sub.wkRecsRC R hs hΔ) hb
  | _, _, _, _, .noexn hs hb, hΔ => .noexn (Sub.wkRecsRC R hs hΔ) hb
  | _, _, _, _, .noextern hs hb, hΔ => .noextern (Sub.wkRecsRC R hs hΔ) hb
  | _, _, _, _, .bot, _ => .bot
  | _, _, _, _, .refNonNull h, hΔ => .refNonNull (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .refNull h, hΔ => .refNull (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .num, _ => .num
  | _, _, _, _, .vec, _ => .vec
  | _, _, _, _, .refv h, hΔ => .refv (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .botv, _ => .botv
  | _, _, _, _, .val h, hΔ => .val (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .pack, _ => .pack
  | _, _, _, _, .fieldConst h, hΔ => .fieldConst (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .fieldVar h₁ h₂, hΔ => .fieldVar (Sub.wkRecsRC R h₁ hΔ) (Sub.wkRecsRC R h₂ hΔ)
  | _, _, _, _, .struct h, hΔ => .struct (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .array h, hΔ => .array (Sub.wkRecsRC R h hΔ)
  | _, _, _, _, .func hp hr, hΔ => .func (Sub.wkRecsRC R hp hΔ) (Sub.wkRecsRC R hr hΔ)
  | _, _, _, _, .defRefl h, _ => .defRefl h
  | _, _, _, _, .defSuper h hj hs, hΔ => .defSuper h hj (Sub.wkRecsRC R hs hΔ)
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons h hl, hΔ => .cons (Sub.wkRecsRC R h hΔ) (Sub.wkRecsRC R hl hΔ)

/-! ## Leaves -/

/-- The leaves of a heap-shaped type: `REC i` with `i < n`, or `_DEF d` with `O d`. -/
def Lv (n : Nat) (O : DefType → Prop) : {k : TKind} → Ty k → Prop
  | _, .nil => True
  | _, .cons a l => Lv n O a ∧ Lv n O l
  | _, .idx _ => False
  | _, .recv i => i < n
  | _, .dt d => O d
  | _, .defn _ _ => False
  | _, .abs _ => True
  | _, .bot => True
  | _, .use u => Lv n O u
  | _, .ref _ h => Lv n O h
  | _, .num _ => True
  | _, .vec _ => True
  | _, .refv r => Lv n O r
  | _, .botv => True
  | _, .val t => Lv n O t
  | _, .pack _ => True
  | _, .field _ s => Lv n O s
  | _, .struct fs => Lv n O fs
  | _, .array f => Lv n O f
  | _, .func ps rs => Lv n O ps ∧ Lv n O rs
  | _, .sub _ _ _ => False
  | _, .group _ => False

theorem Lv.mono {n n' : Nat} {O O' : DefType → Prop} (hn : n ≤ n') (hO : ∀ e, O e → O' e)
    {k : TKind} (t : Ty k) : Lv n O t → Lv n' O' t := by
  induction t with
  | recv i => intro h; simp only [Lv] at h ⊢; omega
  | dt d _ => intro h; exact hO d h
  | cons a l iha ihl => intro h; exact ⟨iha h.1, ihl h.2⟩
  | func ps rs ihp ihr => intro h; exact ⟨ihp h.1, ihr h.2⟩
  | use u ih => exact ih
  | ref _ h ih => exact ih
  | refv r ih => exact ih
  | val t ih => exact ih
  | field _ s ih => exact ih
  | struct fs ih => exact ih
  | array f ih => exact ih
  | _ => intro h; exact h

theorem Lv.and {n : Nat} {O O' : DefType → Prop} {k : TKind} (t : Ty k) :
    Lv n O t → Lv n O' t → Lv n (fun e => O e ∧ O' e) t := by
  induction t with
  | dt d _ => intro h h'; exact ⟨h, h'⟩
  | cons a l iha ihl => intro h h'; exact ⟨iha h.1 h'.1, ihl h.2 h'.2⟩
  | func ps rs ihp ihr => intro h h'; exact ⟨ihp h.1 h'.1, ihr h.2 h'.2⟩
  | use u ih => exact ih
  | ref _ h ih => exact ih
  | refv r ih => exact ih
  | val t ih => exact ih
  | field _ s ih => exact ih
  | struct fs ih => exact ih
  | array f ih => exact ih
  | _ => intro h _; exact h

theorem Lv.size {n : Nat} {O : DefType → Prop} {S : Nat} {k : TKind} (t : Ty k) :
    Lv n O t → t.size ≤ S → Lv n (fun e => O e ∧ e.size < S) t := by
  induction t with
  | dt d _ => intro h hs; simp only [Ty.size] at hs; exact ⟨h, by omega⟩
  | cons a l iha ihl =>
    intro h hs; simp only [Ty.size] at hs; exact ⟨iha h.1 (by omega), ihl h.2 (by omega)⟩
  | func ps rs ihp ihr =>
    intro h hs; simp only [Ty.size] at hs; exact ⟨ihp h.1 (by omega), ihr h.2 (by omega)⟩
  | use u ih => intro h hs; simp only [Ty.size] at hs; exact ih h (by omega)
  | ref _ h ih => intro hh hs; simp only [Ty.size] at hs; exact ih hh (by omega)
  | refv r ih => intro h hs; simp only [Ty.size] at hs; exact ih h (by omega)
  | val t ih => intro h hs; simp only [Ty.size] at hs; exact ih h (by omega)
  | field _ s ih => intro h hs; simp only [Ty.size] at hs; exact ih h (by omega)
  | struct fs ih => intro h hs; simp only [Ty.size] at hs; exact ih h (by omega)
  | array f ih => intro h hs; simp only [Ty.size] at hs; exact ih h (by omega)
  | _ => intro h _; exact h

theorem Lv.of_mem {n : Nat} {O : DefType → Prop} {k : TKind} :
    ∀ {l : Ty (.list k)}, Lv n O l → ∀ a ∈ l.toList, Lv n O a
  | .nil, _, a, h => by simp at h
  | .cons b l, hl, a, h => by
    simp only [Ty.toList_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact hl.1
    · exact Lv.of_mem hl.2 a h

theorem Lv.closed {n : Nat} {O : DefType → Prop} (hO : ∀ e, O e → e.Closed) {k : TKind}
    (t : Ty k) : Lv n O t → t.freeIdx = [] := by
  induction t with
  | idx _ => intro h; exact h.elim
  | dt d _ => intro h; exact hO d h
  | cons a l iha ihl => intro h; simp [Ty.freeIdx, iha h.1, ihl h.2]
  | func ps rs ihp ihr => intro h; simp [Ty.freeIdx, ihp h.1, ihr h.2]
  | use u ih => exact ih
  | ref _ h ih => exact ih
  | refv r ih => exact ih
  | val t ih => exact ih
  | field _ s ih => exact ih
  | struct fs ih => exact ih
  | array f ih => exact ih
  | defn _ _ _ => intro h; exact h.elim
  | sub _ _ _ _ _ => intro h; exact h.elim
  | group _ _ => intro h; exact h.elim
  | _ => intro _; rfl

/-- Leaves in the empty group context yield validity there. -/
theorem Lv.tyOk {n : Nat} {O : DefType → Prop} (hO : ∀ e, O e → TyOk {} e) {Δ : TypeCtx}
    (hΔ : Δ.types = []) (hn : n ≤ Δ.recs.length) {k : TKind} (t : Ty k) :
    Lv n O t → TyOk Δ t := by
  induction t with
  | idx _ => intro h; exact h.elim
  | recv i =>
    intro h
    simp only [Lv] at h
    exact .recv (List.getElem?_eq_getElem (by omega))
  | dt d _ => intro h; exact .dt (TyOk.def_congr (by simp [hΔ]) (hO d h))
  | cons a l iha ihl => intro h; exact .cons (iha h.1) (ihl h.2)
  | func ps rs ihp ihr => intro h; exact .func (ihp h.1) (ihr h.2)
  | use u ih => intro h; exact .use (ih h)
  | ref _ h ih => intro hh; exact .ref (ih hh)
  | refv r ih => intro h; exact .refv (ih h)
  | val t ih => intro h; exact .val (ih h)
  | field _ s ih => intro h; exact .field (ih h)
  | struct fs ih => intro h; exact .struct (ih h)
  | array f ih => intro h; exact .array (ih h)
  | abs a => intro _; exact .abs a
  | bot => intro _; exact .bot
  | num t => intro _; exact .num t
  | vec t => intro _; exact .vec t
  | botv => intro _; exact .botv
  | pack p => intro _; exact .pack p
  | nil => intro _; exact .nil
  | defn _ _ _ => intro h; exact h.elim
  | sub _ _ _ _ _ => intro h; exact h.elim
  | group _ _ => intro h; exact h.elim

/-- Sorts without deftypes at the top. -/
def NoDef : TKind → Prop
  | .def => False
  | .list k => NoDef k
  | _ => True

/-- Leaves of a valid (non-deftype) type in a context without `TYPES`. -/
theorem Lv.of_tyOk {Δ : TypeCtx} (hΔ : Δ.types = []) {k : TKind} (t : Ty k) (hk : NoDef k) :
    TyOk Δ t → Lv Δ.recs.length (fun e => TyOk {} e) t := by
  induction t with
  | idx x => intro h; cases h with | idx h => simp [hΔ] at h
  | recv i =>
    intro h; cases h with
    | recv h => simp only [Lv]; exact (List.getElem?_eq_some_iff.1 h).1
  | dt d _ => intro h; exact TyOk.def_congr (by simp [hΔ]) h.dt_inv
  | defn _ _ _ => exact hk.elim
  | cons a l iha ihl =>
    intro h
    exact ⟨iha hk h.cons_inv.1, ihl hk h.cons_inv.2⟩
  | func ps rs ihp ihr =>
    intro h; exact ⟨ihp trivial h.func_inv.1, ihr trivial h.func_inv.2⟩
  | use u ih => intro h; exact ih trivial h.use_inv
  | ref _ h ih => intro hh; exact ih trivial hh.ref_inv
  | refv r ih => intro h; exact ih trivial h.refv_inv
  | val t ih => intro h; exact ih trivial h.val_inv
  | field _ s ih => intro h; exact ih trivial h.field_inv
  | struct fs ih => intro h; exact ih trivial h.struct_inv
  | array f ih => intro h; exact ih trivial h.array_inv
  | sub _ _ _ _ _ => intro h; cases h
  | group _ _ => intro h; cases h
  | _ => intro _; trivial

/-- `REC`-free leaves: unrolling is the identity. -/
theorem Lv.subst_id {O : DefType → Prop} (σ : Subst) (hσ : ∀ x, σ (.idx x) = none)
    {k : TKind} (t : Ty k) : Lv 0 O t → t.subst σ = t := by
  induction t with
  | idx _ => intro h; exact h.elim
  | recv i => intro h; simp only [Lv] at h; omega
  | dt d _ => intro _; exact Ty.recFree_dt d σ hσ
  | cons a l iha ihl => intro h; simp only [Ty.subst, iha h.1, ihl h.2]
  | func ps rs ihp ihr => intro h; simp only [Ty.subst, ihp h.1, ihr h.2]
  | use u ih => intro h; simp only [Ty.subst, ih h]
  | ref _ h ih => intro hh; simp only [Ty.subst, ih hh]
  | refv r ih => intro h; simp only [Ty.subst, ih h]
  | val t ih => intro h; simp only [Ty.subst, ih h]
  | field _ s ih => intro h; simp only [Ty.subst, ih h]
  | struct fs ih => intro h; simp only [Ty.subst, ih h]
  | array f ih => intro h; simp only [Ty.subst, ih h]
  | defn _ _ _ => intro h; exact h.elim
  | sub _ _ _ _ _ => intro h; exact h.elim
  | group _ _ => intro h; exact h.elim
  | _ => intro _; rfl

/-- Unrolling a group maps `REC` leaves to the group's defined types. -/
theorem Lv.subst_unroll {m : Nat} {P : DefType → Prop} (s : Ty (.list .sub)) (hm : m ≤ s.length)
    (hP : ∀ j < m, P (.defn (.group s) j)) {k : TKind} (t : Ty k) :
    Lv m P t → Lv 0 P (t.subst (unrollSubst s)) := by
  induction t with
  | idx _ => intro h; exact h.elim
  | recv i =>
    intro h
    simp only [Lv] at h
    rw [DefInv.subst_recv (by omega)]
    exact hP i h
  | dt d _ => intro h; simp only [Ty.subst, DefInv.subst_def_u]; exact h
  | cons a l iha ihl => intro h; exact ⟨iha h.1, ihl h.2⟩
  | func ps rs ihp ihr => intro h; exact ⟨ihp h.1, ihr h.2⟩
  | use u ih => exact ih
  | ref _ h ih => exact ih
  | refv r ih => exact ih
  | val t ih => exact ih
  | field _ s ih => exact ih
  | struct fs ih => exact ih
  | array f ih => exact ih
  | defn _ _ _ => intro h; exact h.elim
  | sub _ _ _ _ _ => intro h; exact h.elim
  | group _ _ => intro h; exact h.elim
  | _ => intro h; exact h

end RollClosed

end Silmaril.Wasm.Validation

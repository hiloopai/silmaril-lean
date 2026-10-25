module

public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Type metatheory for the call preservation lemmas

* `sub_toEmpty`: a subtyping in a context whose `TYPES` are valid in `{}` transfers to
  `{}` (after closing `_IDX`), provided the left-hand side is in the up-set of a
  value's principal type (`HeapI`): the context's (unconstrained) `RECS` can then
  not be used.
* `sub_substRecs`: subtyping inside a valid recursive group transfers to `{}` under
  the unrolling substitution.
* `ds_func`: subtyping of defined function types gives contravariant parameter and
  covariant result subtyping.
-/

namespace Silmaril.Wasm.Execution.Core.PC

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core

/-! ## Closed types -/

theorem freeIdx_of_empty {k : TKind} {t : Ty k} (h : TyOk {} t) : t.freeIdx = [] := by
  have := TyOk.freeIdx_lt h
  cases hf : t.freeIdx with
  | nil => rfl
  | cons y l => exact absurd (this y (by simp [hf])) (by simp)

theorem subst_of_empty {k : TKind} {t : Ty k} (h : TyOk {} t) (σ : Subst)
    (hσ : ∀ i, σ (.recv i) = none) : t.subst σ = t :=
  Ty.subst_closed t σ hσ (freeIdx_of_empty h)

/-- The defined types of a context are valid in the empty context. -/
def TypesOk (Δ : TypeCtx) : Prop := ∀ d ∈ Δ.types, TyOk {} d

theorem TypesOk.ok {Δ : TypeCtx} (h : TypesOk Δ) : Δ.Ok := fun d hd =>
  ⟨freeIdx_of_empty (h d hd), TyOk.of_empty Δ (h d hd)⟩

theorem TypesOk.get {Δ : TypeCtx} (h : TypesOk Δ) {x : Nat} {d : DefType}
    (hx : Δ.types[x]? = some d) : TyOk {} d := h d (List.mem_of_getElem? hx)

/-! ## Heap types above principal types -/

/-- Heap types in the up-set of a non-null value's principal type. -/
def HeapI : CHeapType → Prop
  | .abs a => a ≠ .none ∧ a ≠ .nofunc ∧ a ≠ .noexn ∧ a ≠ .noextern
  | .use (.dt d) => TyOk {} d
  | _ => False

def RefI : CRefType → Prop
  | .ref _ h => HeapI h

def ValI : CValType → Prop
  | .num _ | .vec _ => True
  | .refv r => RefI r
  | .botv => False

theorem HeapI.tyOk {h : CHeapType} (hI : HeapI h) : TyOk {} h := by
  match h, hI with
  | .abs a, _ => exact .abs a
  | .use (.dt d), hI => exact .use (.dt hI)

theorem RefI.tyOk {r : CRefType} (hI : RefI r) : TyOk {} r := by
  match r, hI with
  | .ref _ h, hI => exact .ref (HeapI.tyOk hI)

theorem ValI.tyOk {t : CValType} (hI : ValI t) : TyOk {} t := by
  match t, hI with
  | .num n, _ => exact .num n
  | .vec v, _ => exact .vec v
  | .refv r, hI => exact .refv (RefI.tyOk hI)

/-- The motive of `sub_toEmpty`. -/
def SMot (Δ : TypeCtx) : (k : TKind) → Ty k → Ty k → Prop
  | .heap, a, b => HeapI (a.subst Δ.closSubst) →
      Sub {} (a.subst Δ.closSubst) (b.subst Δ.closSubst) ∧ HeapI (b.subst Δ.closSubst)
  | .def, a, b => TyOk {} (a.subst Δ.closSubst) →
      Sub {} (a.subst Δ.closSubst) (b.subst Δ.closSubst) ∧ TyOk {} (b.subst Δ.closSubst)
  | .ref, a, b => RefI (a.subst Δ.closSubst) →
      Sub {} (a.subst Δ.closSubst) (b.subst Δ.closSubst) ∧ RefI (b.subst Δ.closSubst)
  | .val, a, b => ValI (a.subst Δ.closSubst) →
      Sub {} (a.subst Δ.closSubst) (b.subst Δ.closSubst) ∧ ValI (b.subst Δ.closSubst)
  | _, _, _ => True

theorem expand_subst {d : DefType} {ct : CCompType} (h : Expand d ct) (σ : Subst)
    (hσ : ∀ i, σ (.recv i) = none) (hσu : ∀ x u, σ (.idx x) = some u → u.RecFree) :
    Expand (d.subst σ) (ct.subst σ) := by
  obtain ⟨hu⟩ := h
  rename_i fin sups
  refine Expand.mk (fin := fin) (sups := sups.subst σ) ?_
  rw [unrolldt_subst σ hσ hσu, hu]
  rfl

theorem use_dt_of_empty {u : CTypeUse} (h : TyOk {} (Ty.use u)) :
    ∃ e, u = .dt e ∧ TyOk {} e := by
  cases h with
  | use h =>
    cases h with
    | idx hx => simp at hx
    | recv hx => simp at hx
    | dt h => exact ⟨_, rfl, h⟩

theorem sub_toEmpty {Δ : TypeCtx} (hΔ : TypesOk Δ) :
    ∀ {k : TKind} {a b : Ty k}, Sub Δ a b → SMot Δ k a b
  | _, _, _, .heapRefl => fun hI => ⟨.heapRefl, hI⟩
  | _, _, _, .heapTrans _ h₁ h₂ => fun hI => by
    obtain ⟨s₁, i₁⟩ := sub_toEmpty hΔ h₁ hI
    obtain ⟨s₂, i₂⟩ := sub_toEmpty hΔ h₂ i₁
    exact ⟨.heapTrans (HeapI.tyOk i₁) s₁ s₂, i₂⟩
  | _, _, _, .eqAny => fun _ => ⟨.eqAny, by simp [HeapI, Ty.subst]⟩
  | _, _, _, .i31Eq => fun _ => ⟨.i31Eq, by simp [HeapI, Ty.subst]⟩
  | _, _, _, .structEq => fun _ => ⟨.structEq, by simp [HeapI, Ty.subst]⟩
  | _, _, _, .arrayEq => fun _ => ⟨.arrayEq, by simp [HeapI, Ty.subst]⟩
  | _, _, _, .defStruct h => fun _ => by
    refine ⟨?_, by simp [HeapI, Ty.subst]⟩
    simp only [Ty.subst]
    exact .defStruct (expand_subst h _ (TypeCtx.closSubst_recv Δ) (TypeCtx.closSubst_recFree Δ))
  | _, _, _, .defArray h => fun _ => by
    refine ⟨?_, by simp [HeapI, Ty.subst]⟩
    simp only [Ty.subst]
    exact .defArray (expand_subst h _ (TypeCtx.closSubst_recv Δ) (TypeCtx.closSubst_recFree Δ))
  | _, _, _, .defFunc h => fun _ => by
    refine ⟨?_, by simp [HeapI, Ty.subst]⟩
    simp only [Ty.subst]
    exact .defFunc (expand_subst h _ (TypeCtx.closSubst_recv Δ) (TypeCtx.closSubst_recFree Δ))
  | _, _, _, .defDef h => fun hI => by
    simp only [Ty.subst, HeapI] at hI ⊢
    obtain ⟨s, t⟩ := sub_toEmpty hΔ h hI
    exact ⟨.defDef s, t⟩
  | _, _, _, .idxL (x := x) (d := d) hx hs => fun _ => by
    have hd := hΔ.get hx
    have e : ((Ty.use (.idx x) : CHeapType).subst Δ.closSubst) = .use (.dt d) := by
      simp [Ty.subst, TypeCtx.closSubst_idx, hx]
    rw [e]
    have := sub_toEmpty hΔ hs
    simp only [SMot, Ty.subst, HeapI, subst_of_empty hd _ (TypeCtx.closSubst_recv Δ)] at this
    exact this hd
  | _, _, _, .idxR (x := x) (d := d) hx hs => fun hI => by
    have hd := hΔ.get hx
    have e : ((Ty.use (.idx x) : CHeapType).subst Δ.closSubst) = .use (.dt d) := by
      simp [Ty.subst, TypeCtx.closSubst_idx, hx]
    rw [e]
    have := sub_toEmpty hΔ hs hI
    simp only [Ty.subst, HeapI, subst_of_empty hd _ (TypeCtx.closSubst_recv Δ)] at this
    exact this
  | _, _, _, .recStruct _ => fun hI => by
    simp [Ty.subst, TypeCtx.closSubst_recv, HeapI] at hI
  | _, _, _, .recArray _ => fun hI => by
    simp [Ty.subst, TypeCtx.closSubst_recv, HeapI] at hI
  | _, _, _, .recFunc _ => fun hI => by
    simp [Ty.subst, TypeCtx.closSubst_recv, HeapI] at hI
  | _, _, _, .recSub _ _ => fun hI => by
    simp [Ty.subst, TypeCtx.closSubst_recv, HeapI] at hI
  | _, _, _, .none _ _ => fun hI => by simp [Ty.subst, HeapI] at hI
  | _, _, _, .nofunc _ _ => fun hI => by simp [Ty.subst, HeapI] at hI
  | _, _, _, .noexn _ _ => fun hI => by simp [Ty.subst, HeapI] at hI
  | _, _, _, .noextern _ _ => fun hI => by simp [Ty.subst, HeapI] at hI
  | _, _, _, .bot => fun hI => by simp [Ty.subst, HeapI] at hI
  | _, _, _, .refNonNull h => fun hI => by
    simp only [Ty.subst, RefI] at hI ⊢
    obtain ⟨s, t⟩ := sub_toEmpty hΔ h hI
    exact ⟨.refNonNull s, t⟩
  | _, _, _, .refNull h => fun hI => by
    simp only [Ty.subst, RefI] at hI ⊢
    obtain ⟨s, t⟩ := sub_toEmpty hΔ h hI
    exact ⟨.refNull s, t⟩
  | _, _, _, .num => fun _ => ⟨.num, by simp [Ty.subst, ValI]⟩
  | _, _, _, .vec => fun _ => ⟨.vec, by simp [Ty.subst, ValI]⟩
  | _, _, _, .refv h => fun hI => by
    simp only [Ty.subst, ValI] at hI ⊢
    obtain ⟨s, t⟩ := sub_toEmpty hΔ h hI
    exact ⟨.refv s, t⟩
  | _, _, _, .botv => fun hI => by simp [Ty.subst, ValI] at hI
  | _, _, _, .val _ => trivial
  | _, _, _, .pack => trivial
  | _, _, _, .fieldConst _ => trivial
  | _, _, _, .fieldVar _ _ => trivial
  | _, _, _, .struct _ => trivial
  | _, _, _, .array _ => trivial
  | _, _, _, .func _ _ => trivial
  | _, _, _, .defRefl h => fun hI => by
    have hOk := hΔ.ok
    rw [hOk.clos_eq, hOk.clos_eq] at h
    rw [← h]
    exact ⟨.defRefl rfl, hI⟩
  | _, _, _, .defSuper (d₁ := d₁) (d₂ := d₂) (fin := fin) (sups := sups) (ct := ct) (j := j)
      (u := u) h hj hs => fun hI => by
    have hun : unrolldt (d₁.subst Δ.closSubst) =
        some (.sub fin (sups.subst Δ.closSubst) (ct.subst Δ.closSubst)) := by
      rw [unrolldt_subst _ (TypeCtx.closSubst_recv Δ) (TypeCtx.closSubst_recFree Δ), h]; rfl
    have hj' : (sups.subst Δ.closSubst).toList[j]? = some (u.subst Δ.closSubst) := by
      rw [Ty.toList_subst, List.getElem?_map, hj]; rfl
    have hu := TyOk.unroll_super hI hun (List.mem_of_getElem? hj')
    obtain ⟨e, he, heok⟩ := use_dt_of_empty hu
    have := sub_toEmpty hΔ hs
    simp only [SMot, Ty.subst, he, HeapI] at this
    obtain ⟨s, t⟩ := this heok
    refine ⟨.defSuper hun hj' ?_, t⟩
    rw [he]; exact s
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ _ => trivial

/-- Heap-level transfer to the empty context. -/
theorem heap_toEmpty {Δ : TypeCtx} (hΔ : TypesOk Δ) {a b : CHeapType} (h : Sub Δ a b)
    (ha : HeapI a) (hb : TyOk {} b) : Sub {} a b ∧ HeapI b := by
  have := sub_toEmpty hΔ h
  simp only [SMot, subst_of_empty ha.tyOk _ (TypeCtx.closSubst_recv Δ),
    subst_of_empty hb _ (TypeCtx.closSubst_recv Δ)] at this
  exact this ha

theorem ref_toEmpty {Δ : TypeCtx} (hΔ : TypesOk Δ) {a b : CRefType} (h : Sub Δ a b)
    (ha : RefI a) (hb : TyOk {} b) : Sub {} a b ∧ RefI b := by
  have := sub_toEmpty hΔ h
  simp only [SMot, subst_of_empty ha.tyOk _ (TypeCtx.closSubst_recv Δ),
    subst_of_empty hb _ (TypeCtx.closSubst_recv Δ)] at this
  exact this ha

theorem val_toEmpty {Δ : TypeCtx} (hΔ : TypesOk Δ) {a b : CValType} (h : Sub Δ a b)
    (ha : ValI a) (hb : TyOk {} b) : Sub {} a b ∧ ValI b := by
  have := sub_toEmpty hΔ h
  simp only [SMot, subst_of_empty ha.tyOk _ (TypeCtx.closSubst_recv Δ),
    subst_of_empty hb _ (TypeCtx.closSubst_recv Δ)] at this
  exact this ha

theorem typesOk_empty : TypesOk ({} : TypeCtx) := by simp [TypesOk]

/-! ## Subtyping inside a recursive group, unrolled -/

/-- The substitution performed by `unrollrt (.group g)`. -/
def unrollSubst (g : Ty (.list .sub)) : Subst
  | .recv i => if i < g.length then some (.dt (.defn (.group g) i)) else none
  | .idx _ => none

theorem unrollrt_eq (g : Ty (.list .sub)) :
    unrollrt (.group g) = .group (g.subst (unrollSubst g)) := by
  simp only [unrollrt]
  congr 2

theorem unrolldt_defn_get {g : Ty (.list .sub)} {i : Nat} {st : CSubType}
    (h : g.toList[i]? = some st) :
    unrolldt (.defn (.group g) i) = some (st.subst (unrollSubst g)) := by
  simp only [unrolldt, unrollrt_eq, Ty.subs, Ty.toList_subst, List.getElem?_map, h]
  rfl

theorem unrollSubst_idx (g : Ty (.list .sub)) (x : Nat) : unrollSubst g (.idx x) = none := rfl

theorem subst_dt_recFree (σ : Subst) (hσ : ∀ x, σ (.idx x) = none) (d : DefType) :
    d.subst σ = d := Ty.recFree_def d σ hσ

/-- A type valid in a context without `RECS` has no free `REC`. -/
theorem subst_recs_of_noRecs {Δ : TypeCtx} (hr : Δ.recs = []) (σ : Subst)
    (hσ : ∀ x, σ (.idx x) = none) : ∀ {k : TKind} (t : Ty k), TyOk Δ t → t.subst σ = t := by
  intro k t
  induction t with
  | nil => intro _; rfl
  | cons a l iha ihl =>
    intro h; cases h with | cons ha hl => simp [Ty.subst, iha ha, ihl hl]
  | idx x => intro _; simp [Ty.subst, hσ]
  | recv i => intro h; cases h with | recv h => simp [hr] at h
  | dt d _ => intro _; exact Ty.recFree_dt d σ hσ
  | defn g i _ => intro _; exact Ty.recFree_def _ σ hσ
  | abs a => intro _; rfl
  | bot => intro _; rfl
  | use u ih => intro h; cases h with | use h => simp [Ty.subst, ih h]
  | ref n hh ih => intro h; cases h with | ref h => simp [Ty.subst, ih h]
  | num t => intro _; rfl
  | vec t => intro _; rfl
  | refv r ih => intro h; cases h with | refv h => simp [Ty.subst, ih h]
  | botv => intro _; rfl
  | val t ih => intro h; cases h with | val h => simp [Ty.subst, ih h]
  | pack p => intro _; rfl
  | field m s ih => intro h; cases h with | field h => simp [Ty.subst, ih h]
  | struct fs ih => intro h; cases h with | struct h => simp [Ty.subst, ih h]
  | array f ih => intro h; cases h with | array h => simp [Ty.subst, ih h]
  | func ps rs ihp ihr =>
    intro h; cases h with | func hp hq => simp [Ty.subst, ihp hp, ihr hq]
  | sub fin sups b => intro h; cases h
  | group subs => intro h; cases h

theorem subst_app {k : TKind} (σ : Subst) (a b : Ty (.list k)) :
    (a.app b).subst σ = (a.subst σ).app (b.subst σ) := by
  simp [Ty.app, Ty.subst_ofList, Ty.toList_subst]

theorem heap_subst_ne_bot {h : CHeapType} (hb : h ≠ .bot) (σ : Subst) : h.subst σ ≠ .bot := by
  cases h with
  | abs a => simp [Ty.subst]
  | bot => exact absurd rfl hb
  | use u => simp [Ty.subst]

theorem tyOk_group_recv {g : Ty (.list .sub)} {Δ : TypeCtx} (hr : Δ.recs = g.toList)
    {i : Nat} (h : TyOk Δ (Ty.recv i)) :
    unrollSubst g (.recv i) = some (.dt (.defn (.group g) i)) := by
  cases h with
  | recv h =>
    rw [hr] at h
    have : i < g.length := by
      have := (List.getElem?_eq_some_iff.1 h).1
      simpa [Ty.length] using this
    simp [unrollSubst, this]

theorem recv_use_subst {g : Ty (.list .sub)} {Δ : TypeCtx} (hr : Δ.recs = g.toList)
    {i : Nat} (h : TyOk Δ (Ty.recv i)) :
    ((Ty.use (.recv i) : CHeapType).subst (unrollSubst g)) = .use (.dt (.defn (.group g) i)) := by
  simp [Ty.subst, tyOk_group_recv hr h]

/-- Subtyping inside a valid recursive group transfers to `{}` under unrolling. -/
theorem sub_substRecs {g : Ty (.list .sub)} (hg : GroupOk2 (({} : TypeCtx).withRecs g.toList) (.group g) 0)
    {Δ : TypeCtx} (ht : Δ.types = [])
    (hr : Δ.recs = g.toList) :
    ∀ {k : TKind} {a b : Ty k}, Sub Δ a b → TyOk Δ a → TyOk Δ b →
      Sub {} (a.subst (unrollSubst g)) (b.subst (unrollSubst g))
  | _, _, _, .heapRefl, _, _ => .heapRefl
  | _, _, _, .heapTrans hok h₁ h₂, ha, hb =>
    .heapTrans (TyOk.subst_recs (R := g.toList) (Δ := {}) (unrollSubst_idx g)
        (fun j hj => ⟨.dt (.defn (.group g) j), by simp [unrollSubst, Ty.length, hj], .dt (.defn hg (by simpa [Ty.length] using hj))⟩) _ (by
          have : Δ = ({} : TypeCtx).withRecs g.toList := by
            cases Δ; simp_all [TypeCtx.withRecs]
          rw [← this]; exact hok))
      (sub_substRecs hg ht hr h₁ ha hok) (sub_substRecs hg ht hr h₂ hok hb)
  | _, _, _, .eqAny, _, _ => .eqAny
  | _, _, _, .i31Eq, _, _ => .i31Eq
  | _, _, _, .structEq, _, _ => .structEq
  | _, _, _, .arrayEq, _, _ => .arrayEq
  | _, _, _, .defStruct h, _, _ => by
    simp only [Ty.subst, subst_dt_recFree _ (unrollSubst_idx g)]; exact .defStruct h
  | _, _, _, .defArray h, _, _ => by
    simp only [Ty.subst, subst_dt_recFree _ (unrollSubst_idx g)]; exact .defArray h
  | _, _, _, .defFunc h, _, _ => by
    simp only [Ty.subst, subst_dt_recFree _ (unrollSubst_idx g)]; exact .defFunc h
  | _, _, _, .defDef h, ha, hb => by
    simp only [Ty.subst]
    exact .defDef (sub_substRecs hg ht hr h ha.use_inv.dt_inv hb.use_inv.dt_inv)
  | _, _, _, .idxL hx _, _, _ => by simp [ht] at hx
  | _, _, _, .idxR hx _, _, _ => by simp [ht] at hx
  | _, _, _, .recStruct (i := i) (fin := fin) (sups := sups) (fs := fs) h, ha, _ => by
    rw [recv_use_subst hr ha.use_inv]
    rw [hr] at h
    exact .defStruct (Expand.mk (fin := fin) (sups := sups.subst (unrollSubst g))
      (unrolldt_defn_get h))
  | _, _, _, .recArray (i := i) (fin := fin) (sups := sups) h, ha, _ => by
    rw [recv_use_subst hr ha.use_inv]
    rw [hr] at h
    exact .defArray (Expand.mk (fin := fin) (sups := sups.subst (unrollSubst g))
      (unrolldt_defn_get h))
  | _, _, _, .recFunc (i := i) (fin := fin) (sups := sups) h, ha, _ => by
    rw [recv_use_subst hr ha.use_inv]
    rw [hr] at h
    exact .defFunc (Expand.mk (fin := fin) (sups := sups.subst (unrollSubst g))
      (unrolldt_defn_get h))
  | _, _, _, .recSub (i := i) (j := j) (fin := fin) (sups := sups) (ct := ct) (u := u) h hj,
      ha, hb => by
    rw [recv_use_subst hr ha.use_inv]
    rw [hr] at h
    have hun := unrolldt_defn_get h
    have hj' : (sups.subst (unrollSubst g)).toList[j]? = some (u.subst (unrollSubst g)) := by
      rw [Ty.toList_subst, List.getElem?_map, hj]; rfl
    have hu := hb.use_inv
    cases u with
    | idx x => cases hu with | idx hx => simp [ht] at hx
    | recv k =>
      have e1 : (Ty.recv k : CTypeUse).subst (unrollSubst g) = .dt (.defn (.group g) k) := by
        simp [Ty.subst, tyOk_group_recv hr hu]
      rw [e1] at hj'
      simp only [Ty.subst] at e1 ⊢
      rw [e1]
      exact .defDef (.defSuper hun hj' .heapRefl)
    | dt e =>
      simp only [Ty.subst, subst_dt_recFree _ (unrollSubst_idx g)] at hj' ⊢
      exact .defDef (.defSuper hun hj' .heapRefl)
  | _, _, _, .none hs hb', _, hb => .none (sub_substRecs hg ht hr hs hb (.abs _))
      (heap_subst_ne_bot hb' _)
  | _, _, _, .nofunc hs hb', _, hb => .nofunc (sub_substRecs hg ht hr hs hb (.abs _))
      (heap_subst_ne_bot hb' _)
  | _, _, _, .noexn hs hb', _, hb => .noexn (sub_substRecs hg ht hr hs hb (.abs _))
      (heap_subst_ne_bot hb' _)
  | _, _, _, .noextern hs hb', _, hb => .noextern (sub_substRecs hg ht hr hs hb (.abs _))
      (heap_subst_ne_bot hb' _)
  | _, _, _, .bot, _, _ => .bot
  | _, _, _, .refNonNull h, ha, hb => .refNonNull (sub_substRecs hg ht hr h ha.ref_inv hb.ref_inv)
  | _, _, _, .refNull h, ha, hb => .refNull (sub_substRecs hg ht hr h ha.ref_inv hb.ref_inv)
  | _, _, _, .num, _, _ => .num
  | _, _, _, .vec, _, _ => .vec
  | _, _, _, .refv h, ha, hb => .refv (sub_substRecs hg ht hr h ha.refv_inv hb.refv_inv)
  | _, _, _, .botv, _, _ => .botv
  | _, _, _, .val h, ha, hb => .val (sub_substRecs hg ht hr h ha.val_inv hb.val_inv)
  | _, _, _, .pack, _, _ => .pack
  | _, _, _, .fieldConst h, ha, hb =>
    .fieldConst (sub_substRecs hg ht hr h ha.field_inv hb.field_inv)
  | _, _, _, .fieldVar h₁ h₂, ha, hb =>
    .fieldVar (sub_substRecs hg ht hr h₁ ha.field_inv hb.field_inv)
      (sub_substRecs hg ht hr h₂ hb.field_inv ha.field_inv)
  | _, _, _, .struct h, ha, hb => by
    simp only [Ty.subst, subst_app]
    exact .struct (sub_substRecs hg ht hr h ha.struct_inv.app_left hb.struct_inv)
  | _, _, _, .array h, ha, hb => .array (sub_substRecs hg ht hr h ha.array_inv hb.array_inv)
  | _, _, _, .func hp hq, ha, hb =>
    .func (sub_substRecs hg ht hr hp hb.func_inv.1 ha.func_inv.1)
      (sub_substRecs hg ht hr hq ha.func_inv.2 hb.func_inv.2)
  | _, _, _, .defRefl h, _, _ => by
    rw [ht, Ty.clos_nil, Ty.clos_nil] at h
    subst h; exact .defRefl rfl
  | _, _, _, .defSuper (u := u) h hj hs, ha, hb => by
    rw [subst_dt_recFree _ (unrollSubst_idx g), subst_dt_recFree _ (unrollSubst_idx g)]
    have ha0 : TyOk {} _ := TyOk.def_congr (Δ₁ := Δ) (by simp [ht]) ha
    have hu := TyOk.unroll_super ha0 h (List.mem_of_getElem? hj)
    have := sub_substRecs hg ht hr hs (TyOk.of_empty Δ hu) (.use (.dt hb))
    obtain ⟨e, he_eq, he⟩ := use_dt_of_empty hu
    subst he_eq
    simp only [Ty.subst, subst_dt_recFree _ (unrollSubst_idx g)] at this
    exact .defSuper h hj this
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .cons h hl, ha, hb =>
    .cons (sub_substRecs hg ht hr h ha.cons_inv.1 hb.cons_inv.1)
      (sub_substRecs hg ht hr hl ha.cons_inv.2 hb.cons_inv.2)

/-! ## Defined function types: subtyping of parameters and results -/

theorem ds_step {d d' : DefType} {u : CTypeUse} (hd : TyOk {} d) (hu : u ∈ supersOf d)
    (hr : ({} : TypeCtx).resolve u = some d') {ct : CCompType} (he : Expand d ct) :
    ∃ ct', Expand d' ct' ∧ Sub {} ct ct' := by
  cases hd with
  | @defn _ subs i hg hi =>
    have hi' : i < subs.toList.length := by simpa [Ty.length] using hi
    have hst : subs.toList[i]? = some subs.toList[i] := List.getElem?_eq_getElem hi'
    generalize subs.toList[i] = st at hst
    have hso := GroupOk2.get subs hg hst
    rw [Nat.zero_add] at hso
    have hun := unrolldt_defn_get (g := subs) hst
    rw [supersOf_of_unroll hun] at hu
    obtain ⟨hu'⟩ := he
    rw [hun] at hu'
    cases hso with
    | noSuper hct => simp [Ty.subst, Ty.supers] at hu
    | @oneSuper _ fin u0 ct0 _ sups' ct' hu0 hb hunroll hct hsub =>
      simp only [Ty.subst, Ty.supers, Ty.toList_cons, Ty.toList_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hu
      simp only [Ty.subst, Option.some.injEq, Ty.sub.injEq] at hu'
      obtain ⟨-, -, rfl⟩ := hu'
      subst hu
      cases u0 with
      | idx x => cases hu0 with | idx hx => simp [TypeCtx.withRecs] at hx
      | recv j =>
        have e := tyOk_group_recv (Δ := ({} : TypeCtx).withRecs subs.toList) rfl hu0
        simp only [TypeCtx.unrollUse, TypeCtx.withRecs] at hunroll
        simp only [Ty.subst, e, Option.getD_some, TypeCtx.resolve, Option.some.injEq] at hr
        subst hr
        have hso' := GroupOk2.get subs hg hunroll
        have hsub' := sub_substRecs hg (Δ := ({} : TypeCtx).withRecs subs.toList) rfl rfl hsub
          hct hso'.body
        exact ⟨ct'.subst (unrollSubst subs),
          Expand.mk (fin := false) (sups := sups'.subst (unrollSubst subs))
            (unrolldt_defn_get hunroll), hsub'⟩
      | dt e =>
        simp only [Ty.subst, subst_dt_recFree _ (unrollSubst_idx subs), TypeCtx.resolve,
          Option.some.injEq] at hr
        subst hr
        simp only [TypeCtx.unrollUse] at hunroll
        have heok : TyOk {} e :=
          TyOk.def_congr (Δ₁ := ({} : TypeCtx).withRecs subs.toList) (Δ₂ := {}) rfl hu0.dt_inv
        have hct'ok : TyOk {} ct' := Expand.tyOk heok ⟨hunroll⟩
        have hsub' := sub_substRecs hg (Δ := ({} : TypeCtx).withRecs subs.toList) rfl rfl hsub
          hct (TyOk.of_empty _ hct'ok)
        rw [subst_recs_of_noRecs rfl _ (unrollSubst_idx subs) ct' hct'ok] at hsub'
        exact ⟨ct', ⟨hunroll⟩, hsub'⟩

theorem ds_reach {d₁ d₂ : DefType} (h : ({} : TypeCtx).Reach d₁ d₂) :
    ∀ {p₁ r₁ p₂ r₂ : Ty (.list .val)}, TyOk {} d₁ → Expand d₁ (.func p₁ r₁) →
      Expand d₂ (.func p₂ r₂) → ResultSub {} p₂.toList p₁.toList ∧ ResultSub {} r₁.toList r₂.toList := by
  induction h with
  | refl d =>
    intro p₁ r₁ p₂ r₂ _ he₁ he₂
    have := Expand.func_eq he₁ he₂
    cases this
    exact ⟨ResultSub.refl _ _, ResultSub.refl _ _⟩
  | step hu hr _ ih =>
    intro p₁ r₁ p₂ r₂ hd he₁ he₂
    obtain ⟨ct', he', hs⟩ := ds_step hd hu hr he₁
    have hd' := (TypeCtx.super_step TypeCtx.ok_empty hd hu hr).1
    cases hs with
    | func hp hq =>
      obtain ⟨ih₁, ih₂⟩ := ih hd' he' he₂
      have hok := Expand.func_ok hd' he'
      exact ⟨ResultSub.trans TypeCtx.ok_empty hok.1 ih₁ ((Sub.list_iff _ _ _).1 hp),
        ResultSub.trans TypeCtx.ok_empty hok.2 ((Sub.list_iff _ _ _).1 hq) ih₂⟩

/-- Subtyping between valid defined function types, in `{}`. -/
theorem ds_func {d₁ d₂ : DefType} (h1 : TyOk {} d₁) (h2 : TyOk {} d₂)
    (hs : Sub {} (Ty.use (.dt d₁) : CHeapType) (.use (.dt d₂))) {p₁ r₁ p₂ r₂ : Ty (.list .val)}
    (he₁ : Expand d₁ (.func p₁ r₁)) (he₂ : Expand d₂ (.func p₂ r₂)) :
    ResultSub {} p₂.toList p₁.toList ∧ ResultSub {} r₁.toList r₂.toList := by
  have hc := Sub.complete TypeCtx.ok_empty rfl hs (.use (.dt h1)) (.use (.dt h2))
  simp only [Sub.checkK, TypeCtx.checkHeap, TypeCtx.resolve] at hc
  obtain ⟨e, he, hcl⟩ := TypeCtx.checkDef_exists hc
  simp only [Ty.clos_nil] at hcl
  subst hcl
  exact ds_reach he h1 he₁ he₂

end Silmaril.Wasm.Execution.Core.PC

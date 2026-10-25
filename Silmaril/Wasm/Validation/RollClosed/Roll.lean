module

public import Silmaril.Wasm.Validation.RollClosed.Fold
public import Silmaril.Wasm.Validation.Modules

@[expose] public section

/-! # Rolling a source group: substitution bookkeeping

Source types only mention `_IDX` (`Src`). Rolling at `x₀` (`rho`) and closing
against the earlier types `T` (`Subst.all (T.map .dt)`) gives the members of the
rolled group; unrolling those again is the closure against `T ++ rollGroup`.
-/

namespace Silmaril.Wasm.Validation

namespace RollClosed

open DefInv

/-- Source-shaped types: only `_IDX` leaves. -/
def Src : {k : TKind} → Ty k → Prop
  | _, .nil => True
  | _, .cons a l => Src a ∧ Src l
  | _, .idx _ => True
  | _, .recv _ => False
  | _, .dt _ => False
  | _, .defn _ _ => False
  | _, .abs _ => True
  | _, .bot => True
  | _, .use u => Src u
  | _, .ref _ h => Src h
  | _, .num _ => True
  | _, .vec _ => True
  | _, .refv r => Src r
  | _, .botv => True
  | _, .val t => Src t
  | _, .pack _ => True
  | _, .field _ s => Src s
  | _, .struct fs => Src fs
  | _, .array f => Src f
  | _, .func ps rs => Src ps ∧ Src rs
  | _, .sub _ _ _ => False
  | _, .group _ => False

theorem src_ofList {k : TKind} : ∀ {l : List (Ty k)}, (∀ a ∈ l, Src a) → Src (Ty.ofList l)
  | [], _ => trivial
  | a :: l, h => ⟨h a (by simp), src_ofList fun b hb => h b (by simp [hb])⟩

theorem src_liftHeap (h : HeapType) : Src (liftHeap h) := by
  cases h <;> trivial

theorem src_liftVal (t : ValType) : Src (liftVal t) := by
  cases t with
  | ref r => exact src_liftHeap r.heap
  | _ => trivial

theorem src_liftField (f : FieldType) : Src (liftField f) := by
  cases f with
  | mk m st => cases st with
    | val t => exact src_liftVal t
    | packed p => trivial

theorem src_liftComp (ct : CompositeType) : Src (liftComp ct) := by
  cases ct with
  | func ft =>
    exact ⟨src_ofList (by simp only [List.mem_map]; rintro _ ⟨t, _, rfl⟩; exact src_liftVal t),
      src_ofList (by simp only [List.mem_map]; rintro _ ⟨t, _, rfl⟩; exact src_liftVal t)⟩
  | struct fs => exact src_ofList (by simp only [List.mem_map]; rintro _ ⟨f, _, rfl⟩; exact src_liftField f)
  | array f => exact src_liftField f

/-- `$rollrt`'s substitution at `x₀` for a group of `n` members. -/
def rho (x₀ n : Nat) : Subst
  | .idx y => if x₀ ≤ y ∧ y < x₀ + n then some (.recv (y - x₀)) else none
  | .recv _ => none

/-- Rolled members' leaves: earlier types (`T`) or `REC j` with `j < m`. -/
theorem lv_roll (T : List DefType) (n m : Nat) {k : TKind} (t : Ty k) :
    Src t → (∀ y ∈ t.freeIdx, y < T.length + m) → m ≤ n →
      Lv m (fun e => e ∈ T) ((t.subst (rho T.length n)).subst (Subst.all (T.map .dt))) := by
  induction t with
  | idx y =>
    intro _ hy hm
    have hy := hy y (by simp [Ty.freeIdx])
    by_cases h : T.length ≤ y
    · have e1 : (Ty.idx y).subst (rho T.length n) = .recv (y - T.length) := by
        simp [Ty.subst, rho, h, show y < T.length + n by omega]
      rw [e1]
      simp only [Ty.subst, Subst.all, Option.getD_none, Lv]
      omega
    · have e1 : (Ty.idx y).subst (rho T.length n) = .idx y := by
        simp [Ty.subst, rho, h]
      rw [e1]
      have hy' : y < T.length := by omega
      simp only [Ty.subst, Subst.all, List.getElem?_map, List.getElem?_eq_getElem hy',
        Option.map_some, Option.getD_some, Lv]
      exact List.getElem_mem hy'
  | recv _ => intro h; exact h.elim
  | dt _ _ => intro h; exact h.elim
  | defn _ _ _ => intro h; exact h.elim
  | group _ _ => intro h; exact h.elim
  | cons a l iha ihl =>
    intro hs hy hm
    exact ⟨iha hs.1 (fun y h => hy y (by simp [Ty.freeIdx, h])) hm,
      ihl hs.2 (fun y h => hy y (by simp [Ty.freeIdx, h])) hm⟩
  | func a l iha ihl =>
    intro hs hy hm
    exact ⟨iha hs.1 (fun y h => hy y (by simp [Ty.freeIdx, h])) hm,
      ihl hs.2 (fun y h => hy y (by simp [Ty.freeIdx, h])) hm⟩
  | sub _ _ _ _ _ => intro h; exact h.elim
  | use u ih => exact ih
  | ref _ h ih => exact ih
  | refv r ih => exact ih
  | val t ih => exact ih
  | field _ s ih => exact ih
  | struct fs ih => exact ih
  | array f ih => exact ih
  | _ => intro _ _ _; trivial

/-- Unrolling the rolled, `T`-closed form is the closure against `T ++ rollGroup`. -/
theorem roll_unroll (T : List DefType) (n : Nat) (s : Ty (.list .sub)) (hs : s.length = n)
    {k : TKind} (t : Ty k) : Src t → (∀ y ∈ t.freeIdx, y < T.length + n) →
      ((t.subst (rho T.length n)).subst (Subst.all (T.map .dt))).subst (unrollSubst s) =
        t.subst (Subst.all ((T ++ (List.range n).map (Ty.defn (.group s))).map .dt)) := by
  induction t with
  | idx y =>
    intro _ hy
    have hy := hy y (by simp [Ty.freeIdx])
    by_cases h : T.length ≤ y
    · have e1 : (Ty.idx y).subst (rho T.length n) = .recv (y - T.length) := by
        simp [Ty.subst, rho, h, show y < T.length + n by omega]
      rw [e1]
      simp only [Ty.subst, Subst.all, Option.getD_none]
      rw [subst_recv' (by omega)]
      rw [List.getElem?_map, List.getElem?_append_right h, List.getElem?_map,
        List.getElem?_range (by omega)]
      rfl
    · have e1 : (Ty.idx y).subst (rho T.length n) = .idx y := by
        simp [Ty.subst, rho, h]
      rw [e1]
      have hy' : y < T.length := by omega
      simp only [Ty.subst, Subst.all, List.getElem?_map, List.getElem?_eq_getElem hy',
        Option.map_some, Option.getD_some, subst_def_u]
      rw [List.getElem?_append_left hy', List.getElem?_eq_getElem hy']
      rfl
  | recv _ => intro h; exact h.elim
  | dt _ _ => intro h; exact h.elim
  | defn _ _ _ => intro h; exact h.elim
  | group _ _ => intro h; exact h.elim
  | sub _ _ _ _ _ => intro h; exact h.elim
  | cons a l iha ihl =>
    intro hs hy
    simp only [Ty.subst]
    rw [iha hs.1 (fun y h => hy y (by simp [Ty.freeIdx, h])),
      ihl hs.2 (fun y h => hy y (by simp [Ty.freeIdx, h]))]
  | func a l iha ihl =>
    intro hs hy
    simp only [Ty.subst]
    rw [iha hs.1 (fun y h => hy y (by simp [Ty.freeIdx, h])),
      ihl hs.2 (fun y h => hy y (by simp [Ty.freeIdx, h]))]
  | use u ih => intro hs hy; simp only [Ty.subst]; rw [ih hs hy]
  | ref _ h ih => intro hs hy; simp only [Ty.subst]; rw [ih hs hy]
  | refv r ih => intro hs hy; simp only [Ty.subst]; rw [ih hs hy]
  | val t ih => intro hs hy; simp only [Ty.subst]; rw [ih hs hy]
  | field _ s ih => intro hs hy; simp only [Ty.subst]; rw [ih hs hy]
  | struct fs ih => intro hs hy; simp only [Ty.subst]; rw [ih hs hy]
  | array f ih => intro hs hy; simp only [Ty.subst]; rw [ih hs hy]
  | _ => intro _ _; rfl

/-- Validity of a closed source type includes validity of every defined type an
`_IDX` leaf was closed to. -/
theorem tyOk_extract {Δ : TypeCtx} {σ : Subst} {k : TKind} (t : Ty k) : Src t →
    TyOk Δ (t.subst σ) → ∀ y ∈ t.freeIdx, ∀ e, σ (.idx y) = some (.dt e) → TyOk Δ e := by
  induction t with
  | idx x =>
    intro _ h y hy e he
    simp only [Ty.freeIdx, List.mem_singleton] at hy
    subst hy
    simp only [Ty.subst, he, Option.getD_some] at h
    exact h.dt_inv
  | recv _ => intro h; exact h.elim
  | dt _ _ => intro h; exact h.elim
  | defn _ _ _ => intro h; exact h.elim
  | group _ _ => intro h; exact h.elim
  | sub _ _ _ _ _ => intro h; exact h.elim
  | cons a l iha ihl =>
    intro hs h y hy
    simp only [Ty.freeIdx, List.mem_append] at hy
    have h' := h.cons_inv
    rcases hy with hy | hy
    · exact iha hs.1 h'.1 y hy
    · exact ihl hs.2 h'.2 y hy
  | func a l iha ihl =>
    intro hs h y hy
    simp only [Ty.freeIdx, List.mem_append] at hy
    have h' := h.func_inv
    rcases hy with hy | hy
    · exact iha hs.1 h'.1 y hy
    · exact ihl hs.2 h'.2 y hy
  | use u ih => intro hs h; exact ih hs h.use_inv
  | ref _ h ih => intro hs hh; exact ih hs hh.ref_inv
  | refv r ih => intro hs h; exact ih hs h.refv_inv
  | val t ih => intro hs h; exact ih hs h.val_inv
  | field _ s ih => intro hs h; exact ih hs h.field_inv
  | struct fs ih => intro hs h; exact ih hs h.struct_inv
  | array f ih => intro hs h; exact ih hs h.array_inv
  | _ => intro _ _ y hy; simp [Ty.freeIdx] at hy

/-- The members of the rolled, `T`-closed group. -/
def rsubs (T : List DefType) (sts : List SubType) : Ty (.list .sub) :=
  ((Ty.ofList (sts.map liftSub)).subst (rho T.length sts.length)).subst (Subst.all (T.map .dt))

theorem length_rsubs (T : List DefType) (sts : List SubType) :
    (rsubs T sts).length = sts.length := by
  simp [rsubs, Ty.length_subst, Ty.length_ofList]

theorem rsubs_get (T : List DefType) (sts : List SubType) (k : Nat) :
    (rsubs T sts).toList[k]? = (sts[k]?).map fun st =>
      ((liftSub st).subst (rho T.length sts.length)).subst (Subst.all (T.map .dt)) := by
  simp [rsubs, Ty.toList_subst, List.getElem?_map]
  rfl

theorem rollGroup_eq (C : Context) (rt : RecType) :
    C.rollGroup rt = (List.range rt.types.length).map
      (Ty.defn (.group (rsubs C.types rt.types))) := by
  have hl : (Ty.ofList (rt.types.map liftSub)).length = rt.types.length := by
    simp [Ty.length_ofList]
  have hr : rollrt C.types.length (liftRec rt) =
      .group ((Ty.ofList (rt.types.map liftSub)).subst (rho C.types.length rt.types.length)) := by
    simp only [rollrt, liftRec, hl]
    congr 2
  simp only [Context.rollGroup, rolldt, hr, Ty.subs, Ty.length_subst, hl, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp, Ty.substAll, Ty.subst, rsubs]
  rw [Subst.minusRecs_eq (fun _ => rfl)]

end RollClosed

end Silmaril.Wasm.Validation

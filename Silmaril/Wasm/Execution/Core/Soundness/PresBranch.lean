module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.RedexTyping
public import Silmaril.Wasm.Execution.Core.Soundness.RefTyping
public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # Preservation for the conditional-branch rules of `Step`

`AdminsOk`-level replacement lemmas for `br_if`, `br_table`, `br_on_null` and
`br_on_non_null` (spec 4.3 `Step_pure/br_if-true|false`, `br_table-lt|ge`,
`br_on_null-null|addr`, `br_on_non_null-null|addr`): a typing of the left-hand
side at any `it` yields a typing of the right-hand side at the same `it`.
Names carry the suffix `Br`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## `br_if` -/

/-- Inversion and replacement for `i32.const c; br_if l`. -/
theorem brIf_invBr {s : Store H} {C : Context} {c : BitVec 32} {l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [constI32 c, .plain (.brIf l)] it) :
    ∃ ts, C.labels[l.toNat]? = some ts ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨ts, [], ts⟩ → AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brIf l)) it' →
      it'.inits = [] ∧ [Val.i32 c].length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brIf _ => exact ⟨rfl, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, B, t₂', tv, hi, hvs, hB, hrep⟩ := redex_inv_gen (vs := [Val.i32 c]) hI h
  generalize hP : A ++ B = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brIf hl =>
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      obtain ⟨rfl, -⟩ := List.append_inj' hP (by simp at l1 l2 ⊢; omega)
      exact ⟨_, hl, fun out hout => hrep s out hout⟩
    | _ => rename_i hh; cases hh

/-- `Step_pure/br_if-true`. -/
theorem Step.brIfTrue_presBr {s : Store H} {C : Context} {c : BitVec 32} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [constI32 c, .plain (.brIf l)] it) (_hc : c ≠ 0)
    (hC : C.Wf) : AdminsOk s C [.plain (.br l)] it := by
  obtain ⟨ts, hl, hrep⟩ := brIf_invBr h
  have hts := hC.label hl
  exact hrep _ (.single (.plain (by simpa using InstrOk.br (t₁ := []) hl ⟨by simp, hts, by simp⟩)))

/-- `Step_pure/br_if-false`. -/
theorem Step.brIfFalse_presBr {s : Store H} {C : Context} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [constI32 0, .plain (.brIf l)] it) (hC : C.Wf) :
    AdminsOk s C [] it := by
  obtain ⟨ts, hl, hrep⟩ := brIf_invBr h
  exact hrep _ (AdminsOk.id (hC.label hl))

/-! ## `br_table` -/

/-- Inversion and replacement for `i32.const i; br_table ls l'`. -/
theorem brTable_invBr {s : Store H} {C : Context} {i : BitVec 32} {ls : List LabelIdx}
    {l' : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [constI32 i, .plain (.brTable ls l')] it) :
    ∃ ts t₁ t₂, (∀ l ∈ ls, ∃ lt, C.labels[l.toNat]? = some lt ∧ ResultSub C.toTypeCtx ts lt) ∧
      (∃ lt, C.labels[l'.toNat]? = some lt ∧ ResultSub C.toTypeCtx ts lt) ∧
      InstrTypeOk C (.plain (t₁ ++ ts ++ [.i32]) t₂) ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨t₁ ++ ts, [], t₂⟩ → AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brTable ls l')) it' →
      it'.inits = [] ∧ [Val.i32 i].length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brTable _ _ _ => exact ⟨rfl, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | _ => rename_i hh; cases hh
  obtain ⟨A, B, t₂', tv, hi, hvs, hB, hrep⟩ := redex_inv_gen (vs := [Val.i32 i]) hI h
  generalize hP : A ++ B = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brTable hls hl' hok =>
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      obtain ⟨rfl, -⟩ := List.append_inj' hP (by simp at l1 l2 ⊢; omega)
      exact ⟨_, _, _, hls, hl', hok, fun out hout => hrep s out hout⟩
    | _ => rename_i hh; cases hh

/-- `br l` typed at `t₁ ++ ts → t₂` when `ts` is below the label type. -/
theorem br_subBr {s : Store H} {C : Context} {l : LabelIdx} {ts lt t₁ t₂ : List CValType}
    (hl : C.labels[l.toNat]? = some lt) (hs : ResultSub C.toTypeCtx ts lt)
    (hok : InstrTypeOk C (.plain (t₁ ++ ts) t₂)) :
    AdminsOk s C [.plain (.br l)] (.plain (t₁ ++ ts) t₂) := by
  have hok₁ : ResultOk C.toTypeCtx t₁ := ResultOk.left hok.1
  exact .sub (.single (.plain (.br hl ⟨hok₁, hok.2.1, by simp⟩)))
    ⟨ResultSub.append (ResultSub.refl _ _) hs, ResultSub.refl _ _, by simp⟩ hok

/-- `Step_pure/br_table-lt`. -/
theorem Step.brTableLt_presBr {s : Store H} {C : Context} {i : BitVec 32} {ls : List LabelIdx}
    {l' l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [constI32 i, .plain (.brTable ls l')] it)
    (hi : ls[i.toNat]? = some l) : AdminsOk s C [.plain (.br l)] it := by
  obtain ⟨ts, t₁, t₂, hls, -, hok, hrep⟩ := brTable_invBr h
  obtain ⟨lt, hl, hs⟩ := hls l (List.mem_of_getElem? hi)
  refine hrep _ (br_subBr hl hs ⟨?_, hok.2.1, by simp⟩)
  have := hok.1
  simp only [ResultOk.append_iff] at this ⊢
  exact ⟨this.1.1, this.1.2⟩

/-- `Step_pure/br_table-ge`. -/
theorem Step.brTableGe_presBr {s : Store H} {C : Context} {i : BitVec 32} {ls : List LabelIdx}
    {l' : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [constI32 i, .plain (.brTable ls l')] it)
    (_hi : ls.length ≤ i.toNat) :
    AdminsOk s C [.plain (.br l')] it := by
  obtain ⟨ts, t₁, t₂, -, ⟨lt, hl, hs⟩, hok, hrep⟩ := brTable_invBr h
  refine hrep _ (br_subBr hl hs ⟨?_, hok.2.1, by simp⟩)
  have := hok.1
  simp only [ResultOk.append_iff] at this ⊢
  exact ⟨this.1.1, this.1.2⟩

/-! ## `br_on_null` / `br_on_non_null` -/

/-- A non-null value typed below `ref m ht` is typed at `ref n ht` for any `n`. -/
theorem AdminsOk.val_nonnullBr {s : Store H} {C : Context} {v : Val} {tv : CValType}
    {m n : Bool} {ht : CHeapType} (hv : ValOk s v tv) (hs : Sub C.toTypeCtx tv (Ty.refT m ht))
    (hn : v ≠ .ref .null) (hh : TyOk C.toTypeCtx ht) :
    AdminsOk s C [v.toAdmin] (.plain [] [Ty.refT n ht]) := by
  obtain ⟨r, rt₀, rfl, hb, hs₀⟩ := ValOk.ref_invRT hv hs
  have hr : r ≠ .null := fun e => hn (by rw [e])
  cases rt₀ with
  | ref n₀ h₀ =>
    have e := hb.nonnull hr
    subst e
    have hsh := (Sub.ref_inv hs₀).1
    have hsub : Sub C.toTypeCtx (Ty.refv (Ty.ref false h₀)) (Ty.refT n ht) := by
      cases n
      · exact .refv (.refNonNull hsh)
      · exact .refv (.refNull hsh)
    exact AdminsOk.val_sub (.ref hb.refOk) hsub (.refv (.ref hh))

/-- Inversion and replacement for `v; br_on_null l`. -/
theorem brOnNull_invBr {s : Store H} {C : Context} {v : Val} {l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [v.toAdmin, .plain (.brOnNull l)] it) :
    ∃ ts ht tv, C.labels[l.toNat]? = some ts ∧ TyOk C.toTypeCtx ht ∧ ValOk s v tv ∧
      Sub C.toTypeCtx tv (Ty.refT true ht) ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨ts, [], ts ++ [Ty.refT false ht]⟩ →
        AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brOnNull l)) it' →
      it'.inits = [] ∧ [v].length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brOnNull _ _ => exact ⟨rfl, by simp⟩
      | _ => rename_i hh; cases hh
  have h' : AdminsOk s C (vals [v] ++ [.plain (.brOnNull l)]) it := by simpa [vals] using h
  obtain ⟨A, B, t₂', tvs, hi, hvs, hB, hrep⟩ := redex_inv_gen hI h'
  generalize hP : A ++ B = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brOnNull hl hh =>
      rename_i ts ht
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      obtain ⟨rfl, rfl⟩ := List.append_inj' hP (by simp at l1 l2 ⊢; omega)
      cases hvs with
      | cons hv hnil =>
        cases hnil
        cases hB with
        | cons hs _ => exact ⟨_, _, _, hl, hh, hv, hs, fun out hout => hrep s out hout⟩
    | _ => rename_i hh; cases hh

/-- `Step_pure/br_on_null-null`. -/
theorem Step.brOnNullNull_presBr {s : Store H} {C : Context} {l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [.ref .null, .plain (.brOnNull l)] it) (hC : C.Wf) :
    AdminsOk s C [.plain (.br l)] it := by
  obtain ⟨ts, ht, tv, hl, hh, -, -, hrep⟩ := brOnNull_invBr (v := .ref .null) h
  have hts := hC.label hl
  have hres : ResultOk C.toTypeCtx (ts ++ [Ty.refT false ht]) :=
    ResultOk.append hts (ResultOk.single (TyOk.refv (TyOk.ref hh)))
  exact hrep _ (.single (.plain (by simpa using InstrOk.br (t₁ := []) hl ⟨by simp, hres, by simp⟩)))

/-- `Step_pure/br_on_null-addr`. -/
theorem Step.brOnNullAddr_presBr {s : Store H} {C : Context} {v : Val} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [v.toAdmin, .plain (.brOnNull l)] it)
    (hv : v ≠ .ref .null) (hC : C.Wf) :
    AdminsOk s C [v.toAdmin] it := by
  obtain ⟨ts, ht, tv, hl, hh, hvt, hs, hrep⟩ := brOnNull_invBr h
  have := AdminsOk.frame (AdminsOk.val_nonnullBr (n := false) hvt hs hv hh) (hC.label hl)
  exact hrep _ (by simpa using this)

/-- Inversion and replacement for `v; br_on_non_null l`. -/
theorem brOnNonNull_invBr {s : Store H} {C : Context} {v : Val} {l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [v.toAdmin, .plain (.brOnNonNull l)] it) :
    ∃ ts n ht tv, C.labels[l.toNat]? = some (ts ++ [Ty.refT n ht]) ∧ ValOk s v tv ∧
      Sub C.toTypeCtx tv (Ty.refT true ht) ∧
      ∀ (out : List Admin), AdminsOk s C out ⟨ts, [], ts⟩ → AdminsOk s C out it := by
  have hI : ∀ it', AdminOk s C (.plain (.brOnNonNull l)) it' →
      it'.inits = [] ∧ [v].length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | brOnNonNull _ => exact ⟨rfl, by simp⟩
      | _ => rename_i hh; cases hh
  have h' : AdminsOk s C (vals [v] ++ [.plain (.brOnNonNull l)]) it := by simpa [vals] using h
  obtain ⟨A, B, t₂', tvs, hi, hvs, hB, hrep⟩ := redex_inv_gen hI h'
  generalize hP : A ++ B = P at hi
  cases hi with
  | plain hi =>
    cases hi with
    | brOnNonNull hl =>
      have l1 := hB.length_eq
      have l2 := hvs.length_eq
      obtain ⟨rfl, rfl⟩ := List.append_inj' hP (by simp at l1 l2 ⊢; omega)
      cases hvs with
      | cons hv hnil =>
        cases hnil
        cases hB with
        | cons hs _ => exact ⟨_, _, _, _, hl, hv, hs, fun out hout => hrep s out hout⟩
    | _ => rename_i hh; cases hh

/-- `Step_pure/br_on_non_null-null`. -/
theorem Step.brOnNonNullNull_presBr {s : Store H} {C : Context} {l : LabelIdx} {it : InstrType}
    (h : AdminsOk s C [.ref .null, .plain (.brOnNonNull l)] it) (hC : C.Wf) :
    AdminsOk s C [] it := by
  obtain ⟨ts, n, ht, tv, hl, -, -, hrep⟩ := brOnNonNull_invBr (v := .ref .null) h
  exact hrep _ (AdminsOk.id (ResultOk.left (hC.label hl)))

/-- `Step_pure/br_on_non_null-addr`. -/
theorem Step.brOnNonNullAddr_presBr {s : Store H} {C : Context} {v : Val} {l : LabelIdx}
    {it : InstrType} (h : AdminsOk s C [v.toAdmin, .plain (.brOnNonNull l)] it)
    (hv : v ≠ .ref .null) (hC : C.Wf) :
    AdminsOk s C [v.toAdmin, .plain (.br l)] it := by
  obtain ⟨ts, n, ht, tv, hl, hvt, hs, hrep⟩ := brOnNonNull_invBr h
  have hlab := hC.label hl
  have hts : ResultOk C.toTypeCtx ts := ResultOk.left hlab
  have hrt : TyOk C.toTypeCtx (Ty.refT n ht) := hlab _ (by simp)
  have hh : TyOk C.toTypeCtx ht := by
    cases hrt with
    | refv hr => cases hr with
      | ref hh => exact hh
  have hV : AdminsOk s C [v.toAdmin] ⟨ts ++ [], [], ts ++ [Ty.refT n ht]⟩ :=
    AdminsOk.frame (AdminsOk.val_nonnullBr (n := n) hvt hs hv hh) hts
  have hB : AdminsOk s C [.plain (.br l)] ⟨ts ++ [Ty.refT n ht], [], ts⟩ :=
    .single (.plain (by simpa using InstrOk.br (t₁ := []) hl ⟨by simp, hts, by simp⟩))
  have := AdminsOk.seq hV (by simp) (by simpa using hB)
  exact hrep _ (by simpa using this)

end Silmaril.Wasm.Execution.Core

module

public import Silmaril.Libc.Alloc.Defs

/-! # The loose allocator: safety violations, invariants, non-vacuity

PROVED (standard axioms), names in `Silmaril.Libc`:

* `Heap.wf_empty`, `Heap.wf_add` (a fresh block keeps footprints disjoint), `Heap.wf_remove`,
  and `allocLoose_malloc_wf`, `allocLoose_free_wf`: `malloc` and `free` keep `Heap.WF`;
* `allocLoose_malloc_fail`: every `malloc` may return `0`;
* **`allocLoose_double_free`**: after a successful `free p` with `p ≠ 0`, every outcome of
  `free p` is `ub`;
* **`allocLoose_use_after_free`**: on a well-formed heap, after `free p` of the block at `p`
  (of any size), every outcome of `access p` is `ub`; `allocLoose_access_live`: before it,
  `access p` of a nonempty block is fine;
* the order and non-vacuity: `AllocRel.Le.refl`, `AllocRel.Le.trans`,
  `AllocRel.Admissible.mono`, `allocNever_le_loose`, `allocLoose_progress`,
  `allocNever_progress`.
-/

@[expose] public section

namespace Silmaril.Libc

theorem AllocRel.Le.refl (R : AllocRel) : R.Le R := fun _ _ _ h => h

theorem AllocRel.Le.trans {R S T : AllocRel} (h₁ : R.Le S) (h₂ : S.Le T) : R.Le T :=
  fun h c o hr => h₂ h c o (h₁ h c o hr)

theorem AllocRel.Admissible.mono {T U R : AllocRel} (h : T.Admissible R) (hT : T.Le U) :
    U.Admissible R :=
  ⟨h.1.trans hT, h.2⟩

theorem Heap.wf_empty : Heap.empty.WF := ⟨rfl, fun _ _ _ _ h => by cases h⟩

theorem Heap.wf_add {h : Heap} {p n : Nat} (hw : h.WF) (hf : h.Fresh p n) : (h.add p n).WF := by
  obtain ⟨h0, hd⟩ := hw
  obtain ⟨hp0, -, hfr⟩ := hf
  refine ⟨?_, ?_⟩
  · simp [Heap.add, h0, Ne.symm hp0]
  · intro a b m k ha hb hab
    simp only [Heap.add] at ha hb
    by_cases hap : a = p <;> by_cases hbp : b = p
    · exact absurd (hap.trans hbp.symm) hab
    · simp only [hap, hbp, ↓reduceIte] at ha hb
      cases ha; subst hap
      exact hfr b k hb
    · simp only [hap, hbp, ↓reduceIte] at ha hb
      cases hb; subst hbp
      exact (hfr a m ha).symm
    · simp only [hap, hbp, ↓reduceIte] at ha hb
      exact hd a b m k ha hb hab

theorem Heap.wf_remove {h : Heap} (p : Nat) (hw : h.WF) : (h.remove p).WF := by
  obtain ⟨h0, hd⟩ := hw
  refine ⟨?_, ?_⟩
  · simp [Heap.remove, h0]
  · intro a b m k ha hb hab
    simp only [Heap.remove] at ha hb
    split at ha
    · cases ha
    · split at hb
      · cases hb
      · exact hd a b m k ha hb hab

theorem allocLoose_malloc_wf {h h' : Heap} {n r : Nat} (hw : h.WF)
    (hc : allocLoose h (.malloc n) (.ok h' r)) : h'.WF := by
  rcases hc with hc | ⟨p, hf, hc⟩
  · cases hc; exact hw
  · cases hc; exact Heap.wf_add hw hf

theorem allocLoose_free_wf {h h' : Heap} {p r : Nat} (hw : h.WF)
    (hc : allocLoose h (.free p) (.ok h' r)) : h'.WF := by
  simp only [allocLoose] at hc
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte, AOut.ok.injEq] at hc
    rw [hc.1]; exact hw
  · by_cases hl : (h p).isSome = true
    · simp only [hp, hl, ↓reduceIte, AOut.ok.injEq] at hc
      rw [hc.1]; exact Heap.wf_remove p hw
    · simp only [hp, hl, ↓reduceIte, reduceCtorEq] at hc

theorem allocLoose_malloc_fail (h : Heap) (n : Nat) : allocLoose h (.malloc n) (.ok h 0) :=
  Or.inl rfl

theorem allocLoose_double_free {h h' : Heap} {p r : Nat} {o : AOut} (hp : p ≠ 0)
    (h₁ : allocLoose h (.free p) (.ok h' r)) (h₂ : allocLoose h' (.free p) o) : o = .ub := by
  simp only [allocLoose, hp, ↓reduceIte] at h₁ h₂
  by_cases hl : (h p).isSome = true
  · simp only [hl, ↓reduceIte, AOut.ok.injEq] at h₁
    rw [h₁.1] at h₂
    simpa [Heap.remove] using h₂
  · simp only [hl, ↓reduceIte, reduceCtorEq] at h₁

theorem allocLoose_access_live {h : Heap} {p n : Nat} {o : AOut} (hb : h p = some n)
    (hn : 0 < n) (hc : allocLoose h (.access p) o) : o = .ok h 0 := by
  rcases hc with ⟨-, hc⟩ | ⟨hno, -⟩
  · exact hc
  · exact absurd ⟨p, n, hb, Nat.le_refl p, by omega⟩ hno

theorem allocLoose_use_after_free {h h' : Heap} {p n r : Nat} {o : AOut} (hw : h.WF)
    (hb : h p = some n) (h₁ : allocLoose h (.free p) (.ok h' r))
    (h₂ : allocLoose h' (.access p) o) : o = .ub := by
  have hp : p ≠ 0 := by rintro rfl; rw [hw.1] at hb; cases hb
  simp only [allocLoose, hp, hb, Option.isSome_some, ↓reduceIte, AOut.ok.injEq] at h₁
  rw [h₁.1] at h₂
  rcases h₂ with ⟨hown, -⟩ | ⟨-, h₂⟩
  · exfalso
    obtain ⟨a, m, ha, hle, hlt⟩ := hown
    simp only [Heap.remove] at ha
    split at ha
    · cases ha
    · rename_i hap
      rcases hw.2 a p m n ha hb hap with hd | hd <;> omega
  · exact h₂

theorem allocNever_le_loose : allocNever.Le allocLoose := by
  intro h c o hc
  cases c with
  | malloc n => exact Or.inl hc
  | calloc k m =>
    simp only [allocLoose]
    split
    · exact hc
    · exact Or.inl hc
  | realloc p n =>
    simp only [allocNever, allocLoose] at hc ⊢
    by_cases hp : p = 0
    · simp only [hp, ↓reduceIte] at hc ⊢; exact Or.inl hc
    · simp only [hp, ↓reduceIte] at hc ⊢
      by_cases hl : (h p).isSome = true
      · simp only [hl, ↓reduceIte] at hc ⊢
        by_cases hn : n = 0
        · simp only [hn, ↓reduceIte] at hc ⊢; exact Or.inl hc
        · simp only [hn, ↓reduceIte] at hc ⊢; exact Or.inl hc
      · simp only [hl] at hc ⊢; exact hc
  | free p => exact hc
  | access p => exact hc

theorem allocLoose_progress : allocLoose.Progress := by
  intro h c
  cases c with
  | malloc n => exact ⟨_, Or.inl rfl⟩
  | calloc k m =>
    simp only [allocLoose]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, Or.inl rfl⟩
  | realloc p n =>
    simp only [allocLoose]
    split
    · exact ⟨_, Or.inl rfl⟩
    · split
      · split
        · exact ⟨_, Or.inl rfl⟩
        · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, rfl⟩
  | free p =>
    simp only [allocLoose]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  | access p =>
    by_cases ho : h.Owns p
    · exact ⟨_, Or.inl ⟨ho, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨ho, rfl⟩⟩

theorem allocNever_progress : allocNever.Progress := by
  intro h c
  cases c with
  | malloc n => exact ⟨_, rfl⟩
  | calloc k m => exact ⟨_, rfl⟩
  | realloc p n =>
    simp only [allocNever]
    split
    · exact ⟨_, rfl⟩
    · split
      · split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  | free p => exact allocLoose_progress h (.free p)
  | access p => exact allocLoose_progress h (.access p)

end Silmaril.Libc

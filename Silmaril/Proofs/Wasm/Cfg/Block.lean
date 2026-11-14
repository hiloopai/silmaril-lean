module

public import Silmaril.Wasm.Cfg.Block.Defs

/-!
# The canonical segmentation: proofs

Existence (`segment` is a segmentation) and uniqueness (two segmentations of a sequence are
equal), for `Silmaril.Wasm.Cfg.Block.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Cfg

open Silmaril.Wasm Silmaril.Wasm.Cfg

theorem segmentAux_spec : ∀ (is acc : List Instr), (∀ i ∈ acc, isTerminator i = false) →
    IsSegmentation (acc.reverse ++ is) (segmentAux acc is)
  | [], acc, hacc => by
    by_cases h : acc.isEmpty
    · simp only [List.isEmpty_iff] at h; subst h
      simp [segmentAux, IsSegmentation]
    · simp only [segmentAux, h, Bool.false_eq_true, ↓reduceIte]
      refine ⟨by simp [Segment.instrs], ?_, by simp, ?_⟩
      · intro s hs; simp at hs; subst hs
        exact ⟨fun i hi => hacc i (List.mem_reverse.mp hi), by simp⟩
      · intro s hs; simp at hs; subst hs
        simpa [Segment.instrs, List.isEmpty_iff] using h
  | i :: is, acc, hacc => by
    by_cases ht : isTerminator i
    · simp only [segmentAux, ht, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4⟩ := segmentAux_spec is [] (by simp)
      simp only [List.reverse_nil, List.nil_append] at h1
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Segment.instrs, h1]
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨fun j hj => hacc j (List.mem_reverse.mp hj), by simpa using ht⟩
        · exact h2 s hs
      · intro s hs
        cases hrest : segmentAux [] is with
        | nil => rw [hrest] at hs; simp at hs
        | cons x xs =>
          rw [hrest, List.dropLast_cons_cons] at hs
          rcases List.mem_cons.mp hs with rfl | hs
          · rfl
          · exact h3 s (by rw [hrest]; exact hs)
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · simp [Segment.instrs]
        · exact h4 s hs
    · simp only [segmentAux, ht, Bool.false_eq_true, ↓reduceIte]
      have := segmentAux_spec is (i :: acc) (by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · simpa using ht
        · exact hacc j hj)
      simpa using this

theorem segment_isSegmentation (is : List Instr) : IsSegmentation is (segment is) := by
  have := segmentAux_spec is [] (by simp)
  simpa [segment] using this

theorem takeWhile_simple (p r : List Instr) (hp : ∀ i ∈ p, isTerminator i = false)
    (hr : ∀ x ∈ r.head?, isTerminator x = true) :
    (p ++ r).takeWhile (fun i => !isTerminator i) = p ∧
      (p ++ r).dropWhile (fun i => !isTerminator i) = r := by
  induction p with
  | nil =>
    cases r with
    | nil => simp
    | cons x xs =>
      have : isTerminator x = true := hr x rfl
      simp [this]
  | cons y ys ih =>
    have hy : isTerminator y = false := hp y (by simp)
    obtain ⟨h1, h2⟩ := ih (fun i hi => hp i (by simp [hi]))
    simp [hy, h1, h2]

/-- The first segment of a segmentation is determined by the sequence. -/
theorem head_determined {is : List Instr} {s : Segment} {a : List Segment}
    (h : IsSegmentation is (s :: a)) :
    s.body = is.takeWhile (fun i => !isTerminator i) ∧
      s.term = (is.dropWhile (fun i => !isTerminator i)).head? ∧
      IsSegmentation (a.flatMap Segment.instrs) a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs := h2 s (by simp)
  have ha : IsSegmentation (a.flatMap Segment.instrs) a :=
    ⟨rfl, fun t ht => h2 t (by simp [ht]),
     fun t ht => h3 t (by
       cases a with
       | nil => simp at ht
       | cons x xs => rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ ht),
     fun t ht => h4 t (by simp [ht])⟩
  refine ⟨?_, ?_, ha⟩ <;> rw [← h1] <;> simp only [List.flatMap_cons, Segment.instrs]
  · cases ht : s.term with
    | none =>
      -- `s` has no terminator, so it is the last segment
      have : a = [] := by
        cases a with
        | nil => rfl
        | cons x xs => have := h3 s (by simp [List.dropLast_cons_cons]); rw [ht] at this; simp at this
      subst this
      have := takeWhile_simple s.body [] hs.1 (by simp)
      simp only [List.append_nil] at this
      simp [this.1]
    | some x =>
      have := takeWhile_simple s.body (x :: a.flatMap Segment.instrs) hs.1
        (by simpa [ht] using hs.2)
      simp [List.append_assoc, this.1]
  · cases ht : s.term with
    | none =>
      have : a = [] := by
        cases a with
        | nil => rfl
        | cons x xs => have := h3 s (by simp [List.dropLast_cons_cons]); rw [ht] at this; simp at this
      subst this
      have := takeWhile_simple s.body [] hs.1 (by simp)
      simp only [List.append_nil] at this
      simp [this.2]
    | some x =>
      have := takeWhile_simple s.body (x :: a.flatMap Segment.instrs) hs.1
        (by simpa [ht] using hs.2)
      simp [List.append_assoc, this.2]

theorem segment_ext {s t : Segment} (h1 : s.body = t.body) (h2 : s.term = t.term) : s = t := by
  cases s; cases t; simp_all

/-- **The segmentation of a sequence is unique.** -/
theorem isSegmentation_unique : ∀ {is : List Instr} {a b : List Segment},
    IsSegmentation is a → IsSegmentation is b → a = b
  | is, [], b, ha, hb => by
    obtain ⟨h1, -, -, -⟩ := ha
    obtain ⟨g1, -, -, g4⟩ := hb
    cases b with
    | nil => rfl
    | cons t bs =>
      exfalso
      have : t.instrs = [] := by
        simp only [List.flatMap_nil] at h1; subst h1
        simp only [List.flatMap_cons, List.append_eq_nil_iff] at g1; exact g1.1
      exact g4 t (by simp) this
  | is, s :: as, b, ha, hb => by
    cases b with
    | nil =>
      exfalso
      obtain ⟨g1, -, -, -⟩ := hb
      obtain ⟨h1, -, -, h4⟩ := ha
      simp only [List.flatMap_nil] at g1; subst g1
      simp only [List.flatMap_cons, List.append_eq_nil_iff] at h1
      exact h4 s (by simp) h1.1
    | cons t bs =>
      obtain ⟨sb, st, ha'⟩ := head_determined ha
      obtain ⟨tb, tt, hb'⟩ := head_determined hb
      have hst : s = t := segment_ext (sb.trans tb.symm) (st.trans tt.symm)
      subst hst
      -- the rest are segmentations of the same sequence
      have e : as.flatMap Segment.instrs = bs.flatMap Segment.instrs := by
        have h1 := ha.1; have g1 := hb.1
        rw [← g1] at h1
        simp only [List.flatMap_cons, List.append_cancel_left_eq] at h1
        exact h1
      rw [e] at ha'
      rw [isSegmentation_unique ha' hb']

end Silmaril.Proofs.Wasm.Cfg

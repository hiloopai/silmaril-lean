module

public import Silmaril.Wasm.Tools.Gen.Cmd.Sections.Defs

/-!
# Custom sections kept: specification

* `customs_splice`: the custom sections of `splice cs secs` are those of `cs`, in order, when
  `secs` has none;
* `nonCustom_splice`: its other sections are `secs`, in order;
* `anchors_customs`: `anchors` lists every custom section of its input, in order.

So `restore (customsOf input) enc` writes the custom sections of the input in their input
order, and the non-custom sections of the encoder's output in its order.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Sections

theorem filter_custom_map (cs : List (Nat × Sec)) (h : ∀ c ∈ cs, c.2.isCustom = true) :
    (cs.map (·.2)).filter Sec.isCustom = cs.map (·.2) := by
  rw [List.filter_eq_self]
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact h c hc

theorem filter_noncustom_map (cs : List (Nat × Sec)) (h : ∀ c ∈ cs, c.2.isCustom = true) :
    (cs.map (·.2)).filter (fun s => !s.isCustom) = [] := by
  rw [List.filter_eq_nil_iff]
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  simp [h c hc]

/-- **`splice` keeps every custom section, in order.** -/
theorem customs_splice : ∀ (secs : List Sec) (cs : List (Nat × Sec)),
    (∀ c ∈ cs, c.2.isCustom = true) → (∀ s ∈ secs, s.isCustom = false) →
    (splice cs secs).filter Sec.isCustom = cs.map (·.2)
  | [], cs, hc, _ => filter_custom_map cs hc
  | s :: ss, cs, hc, hs => by
    have hs0 : s.isCustom = false := hs s (by simp)
    have hsp : (cs.span (·.1 < rank s.id)).1 ++ (cs.span (·.1 < rank s.id)).2 = cs := by
      rw [List.span_eq_takeWhile_dropWhile]
      exact List.takeWhile_append_dropWhile
    have h1 : ∀ c ∈ (cs.span (·.1 < rank s.id)).1, c.2.isCustom = true :=
      fun c h => hc c (hsp ▸ List.mem_append_left _ h)
    have h2 : ∀ c ∈ (cs.span (·.1 < rank s.id)).2, c.2.isCustom = true :=
      fun c h => hc c (hsp ▸ List.mem_append_right _ h)
    have ih := customs_splice ss _ h2 (fun t ht => hs t (by simp [ht]))
    show ((cs.span (·.1 < rank s.id)).1.map (·.2) ++ s :: splice _ ss).filter Sec.isCustom = _
    rw [List.filter_append, filter_custom_map _ h1, List.filter_cons, hs0]
    simp only [Bool.false_eq_true, ↓reduceIte, ih]
    rw [← List.map_append, hsp]

/-- **`splice` keeps every non-custom section, in order.** -/
theorem nonCustom_splice : ∀ (secs : List Sec) (cs : List (Nat × Sec)),
    (∀ c ∈ cs, c.2.isCustom = true) → (∀ s ∈ secs, s.isCustom = false) →
    (splice cs secs).filter (fun s => !s.isCustom) = secs
  | [], cs, hc, _ => filter_noncustom_map cs hc
  | s :: ss, cs, hc, hs => by
    have hs0 : s.isCustom = false := hs s (by simp)
    have hsp : (cs.span (·.1 < rank s.id)).1 ++ (cs.span (·.1 < rank s.id)).2 = cs := by
      rw [List.span_eq_takeWhile_dropWhile]
      exact List.takeWhile_append_dropWhile
    have h1 : ∀ c ∈ (cs.span (·.1 < rank s.id)).1, c.2.isCustom = true :=
      fun c h => hc c (hsp ▸ List.mem_append_left _ h)
    have h2 : ∀ c ∈ (cs.span (·.1 < rank s.id)).2, c.2.isCustom = true :=
      fun c h => hc c (hsp ▸ List.mem_append_right _ h)
    have ih := nonCustom_splice ss _ h2 (fun t ht => hs t (by simp [ht]))
    show ((cs.span (·.1 < rank s.id)).1.map (·.2) ++ s :: splice _ ss).filter
      (fun s => !s.isCustom) = s :: ss
    rw [List.filter_append, filter_noncustom_map _ h1, List.filter_cons, hs0]
    simp only [Bool.not_false, ↓reduceIte, List.nil_append, ih]

/-- **`anchors` lists the custom sections, in order**, each a custom section. -/
theorem anchors_customs : ∀ (r : Nat) (secs : List Sec),
    (anchorsFrom r secs).map (·.2) = secs.filter Sec.isCustom ∧
      ∀ c ∈ anchorsFrom r secs, c.2.isCustom = true
  | _, [] => ⟨rfl, by simp [anchorsFrom]⟩
  | r, s :: ss => by
    by_cases h : s.isCustom = true
    · obtain ⟨ih1, ih2⟩ := anchors_customs r ss
      refine ⟨?_, ?_⟩
      · simp [anchorsFrom, h, ih1]
      · intro c hc
        simp only [anchorsFrom, h, ↓reduceIte, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact h
        · exact ih2 c hc
    · obtain ⟨ih1, ih2⟩ := anchors_customs (rank s.id) ss
      have h' : s.isCustom = false := by simpa using h
      exact ⟨by simp [anchorsFrom, h', ih1], by simpa [anchorsFrom, h'] using ih2⟩

/-- **What `restore` writes**: when the encoder's output splits into sections, the input's
custom sections in order, and the output's non-custom sections in order, after its header. -/
theorem restore_spec (input enc : ByteArray) (secs : List Sec) (hne : customsOf input ≠ [])
    (h : split enc = some secs) :
    ∃ out, restore (customsOf input) enc = join (enc.extract 0 8) out ∧
      out.filter (fun s => !s.isCustom) = secs.filter (fun s => !s.isCustom) ∧
      out.filter Sec.isCustom = (customsOf input).map (·.2) := by
  have hc : ∀ c ∈ customsOf input, c.2.isCustom = true := by
    unfold customsOf
    split
    · exact (anchors_customs 0 _).2
    · simp
  have hs : ∀ s ∈ secs.filter (fun s => !s.isCustom), s.isCustom = false := by
    intro s hs
    simpa using (List.mem_filter.mp hs).2
  refine ⟨splice (customsOf input) (secs.filter (fun s => !s.isCustom)), ?_, ?_, ?_⟩
  · simp [restore, hne, h]
  · exact nonCustom_splice _ _ hc hs
  · exact customs_splice _ _ hc hs

/-- **What `restore` writes, for any custom sections**: the encoder's output unchanged, or
its header followed by sections whose non-custom ones are the encoder's, in order, and whose
custom ones are `cs`, in order. -/
theorem restore_spec' (cs : List (Nat × Sec)) (enc : ByteArray)
    (hc : ∀ c ∈ cs, c.2.isCustom = true) :
    restore cs enc = enc ∨ ∃ secs out, split enc = some secs ∧
      restore cs enc = join (enc.extract 0 8) out ∧
      out.filter (fun s => !s.isCustom) = secs.filter (fun s => !s.isCustom) ∧
      out.filter Sec.isCustom = cs.map (·.2) := by
  unfold restore
  split
  · exact .inl rfl
  · split
    · rename_i secs h
      have hs : ∀ s ∈ secs.filter (fun s => !s.isCustom), s.isCustom = false := by
        intro s hs
        simpa using (List.mem_filter.mp hs).2
      exact .inr ⟨secs, _, h, rfl, nonCustom_splice _ _ hc hs, customs_splice _ _ hc hs⟩
    · exact .inl rfl

end Silmaril.Wasm.Tools.Gen.Cmd.Sections

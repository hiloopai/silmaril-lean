module

public import Silmaril.Automata.Spec.Defs

/-!
# Machine documents: proofs

For `Silmaril.Automata.Spec.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open Silmaril.Automata

section Named

variable {α : Type} [FinNamed α]

theorem name_inj {a b : α} (h : FinNamed.name a = FinNamed.name b) : a = b :=
  List.inj_on_of_nodup_map FinNamed.nodup (FinNamed.complete a) (FinNamed.complete b) h

theorem mem_names (a : α) : FinNamed.name a ∈ FinNamed.names α :=
  List.mem_map_of_mem (FinNamed.complete a)

theorem mem_names_iff (n : String) : n ∈ FinNamed.names α ↔ ∃ a : α, FinNamed.name a = n := by
  simp [FinNamed.names, FinNamed.complete]

theorem ofName?_name (a : α) : FinNamed.ofName? (FinNamed.name a) = some a := by
  unfold FinNamed.ofName?
  cases h : (FinNamed.elems (α := α)).find? (fun b => FinNamed.name b == FinNamed.name a) with
  | none =>
    exact absurd (List.find?_eq_none.mp h a (FinNamed.complete a)) (by simp)
  | some b =>
    have := List.find?_some h
    simp only [beq_iff_eq] at this
    rw [name_inj this]

end Named

section ToSpec

variable {S L : Type} [FinNamed S] [FinNamed L]

theorem mem_toSpec_edges (M : DMachine S L) (e : Edge) :
    e ∈ M.toSpec.edges ↔ ∃ s l s', M.step s l = some s' ∧
      e = ⟨FinNamed.name s, FinNamed.name l, FinNamed.name s'⟩ := by
  simp only [DMachine.toSpec, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨s, -, l, -, s', h, rfl⟩; exact ⟨s, l, s', h, rfl⟩
  · rintro ⟨s, l, s', h, rfl⟩
    exact ⟨s, FinNamed.complete s, l, FinNamed.complete l, s', h, rfl⟩

theorem toSpec_step_iff (M : DMachine S L) (s : S) (l : L) (s' : S) :
    M.toSpec.Step (FinNamed.name s) (FinNamed.name l) (FinNamed.name s') ↔ M.step s l = some s' := by
  unfold Spec.Step
  rw [mem_toSpec_edges]
  constructor
  · rintro ⟨a, b, c, h, he⟩
    simp only [Edge.mk.injEq] at he
    obtain ⟨h1, h2, h3⟩ := he
    rw [name_inj h1, name_inj h2, name_inj h3]; exact h
  · intro h; exact ⟨s, l, s', h, rfl⟩

theorem toSpec_wf (M : DMachine S L) : M.toSpec.wf = true := by
  simp only [Spec.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem]
  refine ⟨⟨FinNamed.nodup, FinNamed.nodup⟩, fun e he => ?_⟩
  obtain ⟨s, l, s', -, rfl⟩ := (mem_toSpec_edges M e).mp he
  exact ⟨⟨mem_names s, mem_names l⟩, mem_names s'⟩

theorem toSpec_deterministic (M : DMachine S L) : M.toSpec.Deterministic := by
  intro a b x y hx hy
  unfold Spec.Step at hx hy
  obtain ⟨s, l, s', h, he⟩ := (mem_toSpec_edges M _).mp hx
  obtain ⟨t, k, t', h', he'⟩ := (mem_toSpec_edges M _).mp hy
  simp only [Edge.mk.injEq] at he he'
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨h1, h2, rfl⟩ := he'
  rw [← name_inj h1, ← name_inj h2, h] at h'
  cases h'; rfl

end ToSpec

section StepFn

theorem stepFn_some {sp : Spec} {s l d : String} (h : sp.stepFn s l = some d) : sp.Step s l d := by
  unfold Spec.stepFn at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨h1, h2⟩ := hp
  unfold Spec.Step
  cases e; simp only at h1 h2; subst h1 h2; exact hm

theorem stepFn_none {sp : Spec} {s l : String} (h : sp.stepFn s l = none) (d : String) :
    ¬ sp.Step s l d := by
  unfold Spec.stepFn at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  intro hs
  have := h _ hs
  simp at this

theorem stepFn_eq_some_iff {sp : Spec} (hd : sp.Deterministic) (s l d : String) :
    sp.stepFn s l = some d ↔ sp.Step s l d := by
  constructor
  · exact stepFn_some
  · intro h
    cases h' : sp.stepFn s l with
    | none => exact absurd h (stepFn_none h' d)
    | some d' => rw [hd _ _ _ _ (stepFn_some h') h]

theorem stepFn_toSpec {S L : Type} [FinNamed S] [FinNamed L] (M : DMachine S L) (s : S) (l : L) :
    M.toSpec.stepFn (FinNamed.name s) (FinNamed.name l) = (M.step s l).map FinNamed.name := by
  cases h : M.step s l with
  | some s' =>
    rw [Option.map_some, stepFn_eq_some_iff (toSpec_deterministic M), toSpec_step_iff]; exact h
  | none =>
    rw [Option.map_none]
    cases h' : M.toSpec.stepFn (FinNamed.name s) (FinNamed.name l) with
    | none => rfl
    | some d =>
      exfalso
      have hs := stepFn_some h'
      unfold Spec.Step at hs
      obtain ⟨a, b, c, hab, he⟩ := (mem_toSpec_edges M _).mp hs
      simp only [Edge.mk.injEq] at he
      rw [← name_inj he.1, ← name_inj he.2.1, h] at hab
      cases hab

end StepFn

theorem deterministic_of_B {sp : Spec} (h : sp.deterministicB = true) : sp.Deterministic := by
  intro s l a b ha hb
  simp only [Spec.deterministicB, List.all_eq_true] at h
  have := h _ ha _ hb
  simpa using this

section Canon

theorem mem_canon_states (sp : Spec) (s : String) : s ∈ sp.canon.states ↔ s ∈ sp.states := by
  simp [Spec.canon, Finset.mem_sort]

theorem mem_canon_labels (sp : Spec) (l : String) : l ∈ sp.canon.labels ↔ l ∈ sp.labels := by
  simp [Spec.canon, Finset.mem_sort]

theorem mem_canon_edges (sp : Spec) (e : Edge) : e ∈ sp.canon.edges ↔ e ∈ sp.edges := by
  simp [Spec.canon, Finset.mem_sort]

theorem canon_step_iff (sp : Spec) (s l d : String) : sp.canon.Step s l d ↔ sp.Step s l d :=
  mem_canon_edges sp _

theorem canon_eq_iff (sp sp' : Spec) : sp.canon = sp'.canon ↔ sp.Equiv sp' := by
  constructor
  · intro h
    refine ⟨fun s => ?_, fun l => ?_, fun e => ?_⟩
    · rw [← mem_canon_states, h, mem_canon_states]
    · rw [← mem_canon_labels, h, mem_canon_labels]
    · rw [← mem_canon_edges, h, mem_canon_edges]
  · rintro ⟨h1, h2, h3⟩
    have e1 : sp.states.toFinset = sp'.states.toFinset := Finset.ext (by simp [h1])
    have e2 : sp.labels.toFinset = sp'.labels.toFinset := Finset.ext (by simp [h2])
    have e3 : sp.edges.toFinset = sp'.edges.toFinset := Finset.ext (by simp [h3])
    simp only [Spec.canon, e1, e2, e3]

theorem same_iff {α : Type} [DecidableEq α] (a b : List α) :
    (a.all b.contains && b.all a.contains) = true ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun ⟨h1, h2⟩ x => ⟨h1 x, h2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

theorem equivB_iff (sp sp' : Spec) : sp.equivB sp' = true ↔ sp.Equiv sp' := by
  have h1 := same_iff sp.states sp'.states
  have h2 := same_iff sp.labels sp'.labels
  have h3 := same_iff sp.edges sp'.edges
  simp only [Bool.and_eq_true] at h1 h2 h3
  simp only [Spec.equivB, Spec.Equiv, Bool.and_eq_true, ← h1, ← h2, ← h3]
  tauto

theorem sort_eq_of_mem {a b : List String} (h : ∀ x, x ∈ a ↔ x ∈ b) :
    a.toFinset.sort (· ≤ ·) = b.toFinset.sort (· ≤ ·) := by
  have : a.toFinset = b.toFinset := Finset.ext (by simp [h])
  rw [this]

theorem layers_canon_eq_of_equivB {ly ly' : Layers} (h : ly.equivB ly' = true) :
    ly.canon = ly'.canon := by
  have s1 := same_iff ly.initial ly'.initial
  have s2 := same_iff ly.accepting ly'.accepting
  have s3 := same_iff ly.rejecting ly'.rejecting
  have s4 := same_iff ly.error ly'.error
  simp only [Layers.equivB, Bool.and_eq_true] at h s1 s2 s3 s4
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  simp only [Layers.canon, sort_eq_of_mem (s1.mp a), sort_eq_of_mem (s2.mp b),
    sort_eq_of_mem (s3.mp c), sort_eq_of_mem (s4.mp d)]

theorem canon_canon (sp : Spec) : sp.canon.canon = sp.canon :=
  (canon_eq_iff _ _).mpr ⟨mem_canon_states sp, mem_canon_labels sp, mem_canon_edges sp⟩

/-- Two typed machines bound to the same canonical spec have the same steps, up to names. -/
theorem step_iff_of_canon_eq {S₁ L₁ S₂ L₂ : Type} [FinNamed S₁] [FinNamed L₁] [FinNamed S₂]
    [FinNamed L₂] (M₁ : DMachine S₁ L₁) (M₂ : DMachine S₂ L₂)
    (h : M₁.toSpec.canon = M₂.toSpec.canon) {s : S₁} {l : L₁} {s' : S₁} {t : S₂} {k : L₂}
    {t' : S₂} (hs : FinNamed.name s = FinNamed.name t) (hl : FinNamed.name l = FinNamed.name k)
    (hs' : FinNamed.name s' = FinNamed.name t') :
    M₁.step s l = some s' ↔ M₂.step t k = some t' := by
  rw [← toSpec_step_iff, ← toSpec_step_iff, ← canon_step_iff, h, canon_step_iff, hs, hl, hs']

end Canon

section Typed

theorem typed_step_iff (sp : Spec) (hd : sp.Deterministic) (s : sp.State) (l : sp.Label)
    (s' : sp.State) : sp.Typed.step s l = some s' ↔ sp.Step s.1 l.1 s'.1 := by
  rw [← stepFn_eq_some_iff hd]
  unfold Spec.Typed
  simp only
  split
  · next d hd' =>
    rw [hd']
    split
    · next hm =>
      simp only [Option.some.injEq]
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact Subtype.ext rfl
    · next hm =>
      simp only [reduceCtorEq, false_iff, Option.some.injEq]
      intro h; subst h; exact hm s'.2
  · next hn => rw [hn]; simp

end Typed

end Silmaril.Proofs.Automata

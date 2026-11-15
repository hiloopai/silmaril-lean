module

public import Silmaril.Semantics.Accept.Defs

/-!
# Acceptance: laws

Laws of `Silmaril.Semantics.Accept.Defs`:

* checkers: `decides_iff`, `decides_iff_ofBool_eq`, uniqueness of the decided language
  (`Decides.unique`), the canonical checker (`decides_checker`), and Bool connectives as set
  operations (`Decides.and`, `Decides.or`, `Decides.not`);
* outcome quantifiers: complements (`compl_rejectsSome`, `compl_acceptsSome`), the hierarchy
  `acceptsAll ⊆ neverRejects` for disjoint verdicts, `acceptsAll ⊆ acceptsSome` for runners that
  always produce an outcome, monotonicity, unions and intersections of verdict sets, and the
  deterministic collapse (`acceptsSome_detRun`, …);
* size filters: monotonicity and exhaustion (`iUnion_upTo`).
-/

@[expose] public section

namespace Silmaril.Accept

universe u v

variable {α : Type u} {ω : Type v}

/-! ## Bool checkers -/

@[simp] theorem mem_ofBool {check : α → Bool} {a : α} : a ∈ ofBool check ↔ check a = true :=
  Iff.rfl

theorem decides_iff {check : α → Bool} {L : Set α} :
    Decides check L ↔ Sound check L ∧ Complete check L :=
  ⟨fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩, fun h a => ⟨h.1 a, h.2 a⟩⟩

theorem Decides.sound {check : α → Bool} {L : Set α} (h : Decides check L) : Sound check L :=
  (decides_iff.1 h).1

theorem Decides.complete {check : α → Bool} {L : Set α} (h : Decides check L) :
    Complete check L :=
  (decides_iff.1 h).2

theorem decides_iff_ofBool_eq {check : α → Bool} {L : Set α} :
    Decides check L ↔ ofBool check = L :=
  ⟨fun h => Set.ext h, fun h a => by rw [← h]; rfl⟩

theorem decides_ofBool (check : α → Bool) : Decides check (ofBool check) := fun _ => Iff.rfl

/-- A checker decides at most one language. -/
theorem Decides.unique {check : α → Bool} {L L' : Set α} (h : Decides check L)
    (h' : Decides check L') : L = L' :=
  (decides_iff_ofBool_eq.1 h).symm.trans (decides_iff_ofBool_eq.1 h')

/-- Two checkers deciding one language agree pointwise. -/
theorem Decides.check_eq {check check' : α → Bool} {L : Set α} (h : Decides check L)
    (h' : Decides check' L) : check = check' :=
  _root_.funext fun a => Bool.eq_iff_iff.2 ((h a).trans (h' a).symm)

theorem Sound.mono {check : α → Bool} {L L' : Set α} (h : Sound check L) (hL : L ⊆ L') :
    Sound check L' := fun a ha => hL (h a ha)

theorem Complete.anti {check : α → Bool} {L L' : Set α} (h : Complete check L') (hL : L ⊆ L') :
    Complete check L := fun a ha => h a (hL ha)

theorem sound_iff_ofBool_subset {check : α → Bool} {L : Set α} :
    Sound check L ↔ ofBool check ⊆ L := Iff.rfl

theorem complete_iff_subset_ofBool {check : α → Bool} {L : Set α} :
    Complete check L ↔ L ⊆ ofBool check := Iff.rfl

theorem decides_checker (L : Set α) [DecidablePred (· ∈ L)] : Decides (checker L) L :=
  fun _ => decide_eq_true_iff

theorem Decides.and {c d : α → Bool} {L M : Set α} (hc : Decides c L) (hd : Decides d M) :
    Decides (fun a => c a && d a) (L ∩ M) := fun a => by
  simp only [Bool.and_eq_true, hc a, hd a, Set.mem_inter_iff]

theorem Decides.or {c d : α → Bool} {L M : Set α} (hc : Decides c L) (hd : Decides d M) :
    Decides (fun a => c a || d a) (L ∪ M) := fun a => by
  simp only [Bool.or_eq_true, hc a, hd a, Set.mem_union]

theorem Decides.not {c : α → Bool} {L : Set α} (hc : Decides c L) :
    Decides (fun a => !c a) Lᶜ := fun a => by
  simp only [Bool.not_eq_true', Set.mem_compl_iff, ← hc a, Bool.not_eq_true]

/-- Precomposition: a checker for `L` gives a checker for the preimage `f ⁻¹' L`. -/
theorem Decides.comp {β : Type v} {c : β → Bool} {L : Set β} (hc : Decides c L) (f : α → β) :
    Decides (c ∘ f) (f ⁻¹' L) := fun a => hc (f a)

/-! ## Outcome quantifiers -/

section Outcomes

variable {run : α → Set ω} {acc acc' rej rej' : Set ω} {a : α}

@[simp] theorem mem_acceptsSome : a ∈ acceptsSome run acc ↔ ∃ o ∈ run a, o ∈ acc := Iff.rfl
@[simp] theorem mem_acceptsAll : a ∈ acceptsAll run acc ↔ ∀ o ∈ run a, o ∈ acc := Iff.rfl
@[simp] theorem mem_rejectsSome : a ∈ rejectsSome run rej ↔ ∃ o ∈ run a, o ∈ rej := Iff.rfl
@[simp] theorem mem_neverRejects : a ∈ neverRejects run rej ↔ ∀ o ∈ run a, o ∉ rej := Iff.rfl

/-- Existential and universal verdicts are the same quantifier pair on outcomes: some-rejection
and never-rejection are complements. -/
theorem compl_rejectsSome : (rejectsSome run rej)ᶜ = neverRejects run rej := by
  ext a; simp

theorem compl_neverRejects : (neverRejects run rej)ᶜ = rejectsSome run rej := by
  rw [← compl_rejectsSome, compl_compl]

/-- The complement of existential acceptance is universal acceptance of the complement. -/
theorem compl_acceptsSome : (acceptsSome run acc)ᶜ = acceptsAll run accᶜ := by
  ext a; simp

theorem neverRejects_eq_acceptsAll_compl : neverRejects run rej = acceptsAll run rejᶜ := rfl

theorem rejectsSome_eq_acceptsSome : rejectsSome run rej = acceptsSome run rej := rfl

/-- With disjoint verdicts, universal acceptance implies never-rejection. -/
theorem acceptsAll_subset_neverRejects (h : Disjoint acc rej) :
    acceptsAll run acc ⊆ neverRejects run rej :=
  fun _ ha o ho hr => Set.disjoint_left.1 h (ha o ho) hr

/-- If every input has an outcome, universal acceptance implies existential acceptance. -/
theorem acceptsAll_subset_acceptsSome (htot : ∀ a, (run a).Nonempty) :
    acceptsAll run acc ⊆ acceptsSome run acc :=
  fun a ha => let ⟨o, ho⟩ := htot a; ⟨o, ho, ha o ho⟩

/-- Without outcomes both universal verdicts hold vacuously and existential ones fail. -/
theorem mem_neverRejects_of_eq_empty (h : run a = ∅) : a ∈ neverRejects run rej := by
  simp [h]

theorem not_mem_acceptsSome_of_eq_empty (h : run a = ∅) : a ∉ acceptsSome run acc := by
  simp [h]

/-- A single input that has no outcome separates never-rejection from existential
acceptance: `neverRejects` is strictly weaker in general. -/
theorem neverRejects_not_subset_acceptsSome (h : run a = ∅) :
    ¬ neverRejects run rej ⊆ acceptsSome run acc :=
  fun hs => not_mem_acceptsSome_of_eq_empty h (hs (mem_neverRejects_of_eq_empty h))

theorem acceptsSome_mono (h : acc ⊆ acc') : acceptsSome run acc ⊆ acceptsSome run acc' :=
  fun _ ⟨o, ho, ha⟩ => ⟨o, ho, h ha⟩

theorem acceptsAll_mono (h : acc ⊆ acc') : acceptsAll run acc ⊆ acceptsAll run acc' :=
  fun _ ha o ho => h (ha o ho)

theorem neverRejects_anti (h : rej ⊆ rej') : neverRejects run rej' ⊆ neverRejects run rej :=
  fun _ ha o ho hr => ha o ho (h hr)

theorem acceptsSome_union :
    acceptsSome run (acc ∪ acc') = acceptsSome run acc ∪ acceptsSome run acc' := by
  ext a; simp only [mem_acceptsSome, Set.mem_union]; grind

theorem acceptsAll_inter :
    acceptsAll run (acc ∩ acc') = acceptsAll run acc ∩ acceptsAll run acc' := by
  ext a; simp only [mem_acceptsAll, Set.mem_inter_iff]; grind

theorem neverRejects_union :
    neverRejects run (rej ∪ rej') = neverRejects run rej ∩ neverRejects run rej' := by
  ext a; simp only [mem_neverRejects, Set.mem_union, Set.mem_inter_iff]; grind

/-- Fewer outcomes (a refinement of the runner) preserve universal verdicts. -/
theorem acceptsAll_of_le {run' : α → Set ω} (h : ∀ a, run' a ⊆ run a) :
    acceptsAll run acc ⊆ acceptsAll run' acc :=
  fun a ha o ho => ha o (h a ho)

/-- More outcomes preserve existential verdicts. -/
theorem acceptsSome_of_le {run' : α → Set ω} (h : ∀ a, run a ⊆ run' a) :
    acceptsSome run acc ⊆ acceptsSome run' acc :=
  fun _ ⟨o, ho, ha⟩ => ⟨o, h _ ho, ha⟩

end Outcomes

section Deterministic

variable {f : α → ω} {acc rej : Set ω}

@[simp] theorem mem_detRun {a : α} {o : ω} : o ∈ detRun f a ↔ o = f a := Iff.rfl

theorem acceptsSome_detRun : acceptsSome (detRun f) acc = f ⁻¹' acc := by ext a; simp

theorem acceptsAll_detRun : acceptsAll (detRun f) acc = f ⁻¹' acc := by ext a; simp

theorem neverRejects_detRun : neverRejects (detRun f) rej = f ⁻¹' rejᶜ := by ext a; simp

/-- For a total deterministic runner, never-rejecting with the complementary verdict is
acceptance. -/
theorem neverRejects_detRun_compl : neverRejects (detRun f) accᶜ = acceptsSome (detRun f) acc := by
  rw [neverRejects_detRun, compl_compl, acceptsSome_detRun]

end Deterministic

/-! ## Size filters -/

section Size

variable {size : α → ℕ} {m n : ℕ} {L M : Set α} {a : α}

@[simp] theorem mem_upTo : a ∈ upTo size n L ↔ a ∈ L ∧ size a ≤ n := Iff.rfl

theorem upTo_subset : upTo size n L ⊆ L := fun _ h => h.1

theorem upTo_mono_size (h : m ≤ n) : upTo size m L ⊆ upTo size n L :=
  fun _ ha => ⟨ha.1, ha.2.trans h⟩

theorem upTo_mono (h : L ⊆ M) : upTo size n L ⊆ upTo size n M := fun _ ha => ⟨h ha.1, ha.2⟩

theorem upTo_inter : upTo size n (L ∩ M) = upTo size n L ∩ upTo size n M := by
  ext a; simp only [mem_upTo, Set.mem_inter_iff]; tauto

theorem upTo_union : upTo size n (L ∪ M) = upTo size n L ∪ upTo size n M := by
  ext a; simp only [mem_upTo, Set.mem_union]; tauto

/-- Every member of a language appears in some size slice. -/
theorem iUnion_upTo : ⋃ n, upTo size n L = L := by
  ext a; simp only [Set.mem_iUnion, mem_upTo]; exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, le_rfl⟩⟩

/-- Two languages are equal iff all their size slices are. -/
theorem eq_iff_upTo_eq : L = M ↔ ∀ n, upTo size n L = upTo size n M :=
  ⟨fun h _ => h ▸ rfl, fun h => by
    rw [← iUnion_upTo (size := size) (L := L), ← iUnion_upTo (size := size) (L := M)]
    simp only [h]⟩

/-- A checker restricted by a size bound decides the size slice. -/
theorem Decides.upTo {c : α → Bool} (hc : Decides c L) (size : α → ℕ) (n : ℕ) :
    Decides (fun a => c a && decide (size a ≤ n)) (Accept.upTo size n L) := fun a => by
  simp only [Bool.and_eq_true, hc a, decide_eq_true_eq, mem_upTo]

end Size

end Silmaril.Accept

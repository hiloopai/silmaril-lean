module

public import Silmaril.Semantics.Accept.Verdict.Defs
public import Silmaril.Semantics.Accept.Thms

/-!
# Combined verdicts: laws

* membership and the two inclusions (`acceptsSafely_subset_acceptsSome`,
  `acceptsSafely_subset_neverRejects`), the complement;
* no outcome, no acceptance (`not_mem_acceptsSafely_of_eq_empty`);
* conflicts: a conflicting outcome excludes the input (`not_mem_acceptsSafely_of_conflict`),
  acceptance is witnessed outside `rej` (`exists_accept_not_reject`), conflicting accepting
  outcomes are irrelevant (`acceptsSafely_diff`), `acc ⊆ rej` empties the language,
  `acceptsSafely ∩ conflictInputs = ∅`, and with disjoint verdicts universal acceptance with
  some outcome suffices (`acceptsAll_inter_subset_acceptsSafely`);
* deterministic runners: `acceptsSafely (detRun f) acc rej = f ⁻¹' (acc \ rej)` and a Bool
  checker for it;
* monotonicity: monotone in `acc`, antitone in `rej`; under inclusion of runners, preserved
  only when an accepting outcome survives (`acceptsSafely_of_le`), with counterexamples in
  both directions (`not_mono_runner`, `not_anti_runner`);
* environment classes: membership in `acceptsSafely (envRun r E)` is "some environment in `E`
  accepts and none in `E` rejects" (`mem_acceptsSafely_envRun`).
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w

variable {α : Type u} {ω : Type v} {run run' : α → Set ω} {acc acc' rej rej' : Set ω} {a : α}

@[simp] theorem mem_acceptsSafely :
    a ∈ acceptsSafely run acc rej ↔ (∃ o ∈ run a, o ∈ acc) ∧ ∀ o ∈ run a, o ∉ rej := Iff.rfl

@[simp] theorem mem_conflicts {o : ω} : o ∈ conflicts acc rej ↔ o ∈ acc ∧ o ∈ rej := Iff.rfl

@[simp] theorem mem_conflictInputs :
    a ∈ conflictInputs run acc rej ↔ ∃ o ∈ run a, o ∈ acc ∧ o ∈ rej := Iff.rfl

theorem acceptsSafely_subset_acceptsSome : acceptsSafely run acc rej ⊆ acceptsSome run acc :=
  fun _ h => h.1

theorem acceptsSafely_subset_neverRejects :
    acceptsSafely run acc rej ⊆ neverRejects run rej := fun _ h => h.2

/-- Not combined-accepted: every execution fails to accept, or some execution rejects. -/
theorem compl_acceptsSafely :
    (acceptsSafely run acc rej)ᶜ = acceptsAll run accᶜ ∪ rejectsSome run rej := by
  rw [acceptsSafely, Set.compl_inter, compl_acceptsSome, compl_neverRejects]

/-- An input without outcomes is not combined-accepted, though it never rejects. -/
theorem not_mem_acceptsSafely_of_eq_empty (h : run a = ∅) : a ∉ acceptsSafely run acc rej :=
  fun hm => not_mem_acceptsSome_of_eq_empty h hm.1

/-! ## Conflicts -/

/-- An input with an outcome that both accepts and rejects is excluded. -/
theorem not_mem_acceptsSafely_of_conflict {o : ω} (ho : o ∈ run a) (hc : o ∈ conflicts acc rej) :
    a ∉ acceptsSafely run acc rej := fun hm => hm.2 o ho hc.2

theorem acceptsSafely_inter_conflictInputs :
    acceptsSafely run acc rej ∩ conflictInputs run acc rej = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨hm, _, ho, hc⟩ => not_mem_acceptsSafely_of_conflict ho hc hm

/-- Combined acceptance is witnessed by an accepting outcome that does not reject. -/
theorem exists_accept_not_reject (hm : a ∈ acceptsSafely run acc rej) :
    ∃ o ∈ run a, o ∈ acc \ rej :=
  let ⟨o, ho, hacc⟩ := hm.1; ⟨o, ho, hacc, hm.2 o ho⟩

/-- Accepting outcomes that also reject never contribute. -/
theorem acceptsSafely_diff : acceptsSafely run (acc \ rej) rej = acceptsSafely run acc rej :=
  Set.Subset.antisymm (fun _ hm => ⟨acceptsSome_mono Set.sdiff_subset hm.1, hm.2⟩)
    fun _ hm => ⟨exists_accept_not_reject hm, hm.2⟩

/-- If every accepting outcome also rejects, nothing is combined-accepted. -/
theorem acceptsSafely_eq_empty_of_subset (h : acc ⊆ rej) : acceptsSafely run acc rej = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hm =>
    let ⟨_, _, hacc, hrej⟩ := exists_accept_not_reject hm; hrej (h hacc)

/-- With disjoint verdicts, accepting on every execution, and having one, suffices. -/
theorem acceptsAll_inter_subset_acceptsSafely (h : Disjoint acc rej) :
    acceptsAll run acc ∩ {a | (run a).Nonempty} ⊆ acceptsSafely run acc rej :=
  fun _ ⟨hall, o, ho⟩ => ⟨⟨o, ho, hall o ho⟩, acceptsAll_subset_neverRejects h hall⟩

/-! ## Deterministic runners -/

theorem acceptsSafely_detRun {β : Type w} {f : α → β} {acc rej : Set β} :
    acceptsSafely (detRun f) acc rej = f ⁻¹' (acc \ rej) := by
  ext a; simp [acceptsSafely]

/-- Bool checkers for the two verdicts give a checker for a deterministic component. -/
theorem Decides.acceptsSafely_detRun {β : Type w} {f : α → β} {acc rej : Set β}
    {ca cr : β → Bool} (ha : Decides ca acc) (hr : Decides cr rej) :
    Decides (fun a => ca (f a) && !cr (f a)) (acceptsSafely (detRun f) acc rej) := by
  rw [Accept.acceptsSafely_detRun, Set.sdiff_eq]; exact (ha.and hr.not).comp f

/-! ## Monotonicity -/

theorem acceptsSafely_mono_acc (h : acc ⊆ acc') :
    acceptsSafely run acc rej ⊆ acceptsSafely run acc' rej :=
  fun _ hm => ⟨acceptsSome_mono h hm.1, hm.2⟩

theorem acceptsSafely_anti_rej (h : rej ⊆ rej') :
    acceptsSafely run acc rej' ⊆ acceptsSafely run acc rej :=
  fun _ hm => ⟨hm.1, neverRejects_anti h hm.2⟩

/-- Restricting executions preserves combined acceptance of `a` exactly when some accepting
outcome survives: never-rejection always survives restriction. -/
theorem acceptsSafely_of_le (hle : ∀ a, run' a ⊆ run a) (hm : a ∈ acceptsSafely run acc rej)
    (hsurv : ∃ o ∈ run' a, o ∈ acc) : a ∈ acceptsSafely run' acc rej :=
  ⟨hsurv, fun o ho => hm.2 o (hle a ho)⟩

/-- Enlarging executions preserves combined acceptance of `a` exactly when no new outcome
rejects: acceptance always survives enlargement. -/
theorem acceptsSafely_of_ge (hle : ∀ a, run a ⊆ run' a) (hm : a ∈ acceptsSafely run acc rej)
    (hnew : ∀ o ∈ run' a, o ∉ rej) : a ∈ acceptsSafely run' acc rej :=
  ⟨acceptsSome_of_le hle hm.1, hnew⟩

/-- Not monotone: restricting executions can lose the only accepting run. -/
theorem not_mono_runner : ¬ ∀ (run run' : Unit → Set Bool), (∀ a, run' a ⊆ run a) →
    acceptsSafely run {true} {false} ⊆ acceptsSafely run' {true} {false} := fun h =>
  not_mem_acceptsSafely_of_eq_empty (run := fun _ => ∅) (a := ()) rfl
    (h (fun _ => {true}) (fun _ => ∅) (fun _ => Set.empty_subset _)
      (show () ∈ acceptsSafely (fun _ => {true}) {true} {false} by simp))

/-- Not antitone: enlarging executions can add a rejecting run. -/
theorem not_anti_runner : ¬ ∀ (run run' : Unit → Set Bool), (∀ a, run a ⊆ run' a) →
    acceptsSafely run {true} {false} ⊆ acceptsSafely run' {true} {false} := fun h =>
  (h (fun _ => {true}) (fun _ => Set.univ) (fun _ => Set.subset_univ _)
    (show () ∈ acceptsSafely (fun _ => {true}) {true} {false} by simp)).2 false trivial rfl

/-! ## Environment classes -/

/-- Over one environment class, combined acceptance is: some environment has an accepting
execution, and no environment has a rejecting one. -/
theorem mem_acceptsSafely_envRun {ε : Type w} {r : ε → α → Set ω} {E : Set ε} :
    a ∈ acceptsSafely (envRun r E) acc rej ↔
      (∃ e ∈ E, ∃ o ∈ r e a, o ∈ acc) ∧ ∀ e ∈ E, ∀ o ∈ r e a, o ∉ rej := by
  simp only [mem_acceptsSafely, envRun, Set.mem_ofPred_eq]; grind

theorem envRun_mono {ε : Type w} {r : ε → α → Set ω} {E E' : Set ε} (h : E ⊆ E') (a : α) :
    envRun r E a ⊆ envRun r E' a := fun _ ⟨e, he, ho⟩ => ⟨e, h he, ho⟩

end Silmaril.Accept

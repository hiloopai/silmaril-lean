module

public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Foundations.Semantics.LTS.Relation
public import Silmaril.Foundations.InfiniteTrace

/-!
# Executable exploration of operational semantics

An execution layer using CSLib's labelled transition systems and finite
executions, together with Silmaril's infinite traces. A finite successor enumerator has an explicit correctness contract;
neither finiteness nor decidability is assumed for arbitrary SOS rule systems.
-/

@[expose] public section

namespace Silmaril.Semantics.Operational

universe u v

variable {State : Type u} {Label : Type v}

/-- A complete, executable list of outgoing transitions. Duplicate successors
are harmless. An instance is an obligation of a concrete interpreter. -/
structure Enumerator (lts : Cslib.LTS State Label) where
  next : State → List (Label × State)
  correct : ∀ s a t, (a, t) ∈ next s ↔ lts.Tr s a t

/-- All executions of exactly `fuel` transitions, recording labels and endpoints.
Fuel exhaustion is a bound on exploration, not a claim about termination. -/
def explore (next : State → List (Label × State)) : Nat → State → List (List Label × State)
  | 0, s => [([], s)]
  | n + 1, s => (next s).flatMap fun (a, t) =>
      (explore next n t).map fun (labels, result) => (a :: labels, result)

/-- Exploration is sound and complete at each finite depth. -/
theorem Enumerator.mem_explore_iff {lts : Cslib.LTS State Label} (enumerator : Enumerator lts)
    (n : Nat) (s : State) (labels : List Label) (t : State) :
    (labels, t) ∈ explore enumerator.next n s ↔
      labels.length = n ∧ lts.MTr s labels t := by
  induction n generalizing s labels t with
  | zero =>
    cases labels <;> simp [explore, Cslib.LTS.MTr.nil_iff, eq_comm]
  | succ n ih =>
    constructor
    · intro h
      simp only [explore, List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨a, next⟩, first, ⟨⟨rest, last⟩, tail, equal⟩⟩ := h
      cases equal
      obtain ⟨length, path⟩ := (ih next rest last).mp tail
      exact ⟨congrArg Nat.succ length, .stepL (enumerator.correct _ _ _ |>.mp first) path⟩
    · rintro ⟨length, path⟩
      cases path with
      | refl => simp at length
      | @stepL s a next rest t first tail =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at length
        simp only [explore, List.mem_flatMap, List.mem_map]
        exact ⟨(a, next), (enumerator.correct _ _ _).mpr first,
          (rest, t), (ih next rest t).mpr ⟨length, tail⟩, rfl⟩

/-- Successful exploration also supplies all the intermediate states through
CSLib's execution representation. -/
theorem Enumerator.execution_of_mem {lts : Cslib.LTS State Label} (enumerator : Enumerator lts)
    {n : Nat} {s t : State} {labels : List Label}
    (h : (labels, t) ∈ explore enumerator.next n s) :
    ∃ states, lts.Execution s labels t states :=
  Cslib.LTS.Execution.of_mTr ((enumerator.mem_explore_iff n s labels t).mp h).2

/-- An empty successor list really means stuckness only for a complete enumerator. -/
theorem Enumerator.next_eq_nil_iff {lts : Cslib.LTS State Label} (enumerator : Enumerator lts)
    (s : State) : enumerator.next s = [] ↔ ∀ a t, ¬ lts.Tr s a t := by
  constructor
  · intro empty a t step
    have := (enumerator.correct s a t).mpr step
    simp [empty] at this
  · intro stuck
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨a, t⟩ member
    exact stuck a t ((enumerator.correct s a t).mp member)

/-- Divergence uses actual transitions, including their labels. -/
def Diverges (lts : Cslib.LTS State Label) (s : State) : Prop :=
  InfiniteTrace lts.UnlabelledTr s

/-- A finite execution followed by divergence is divergent. -/
theorem Diverges.prefix {lts : Cslib.LTS State Label} {s t : State} {labels : List Label}
    (path : lts.MTr s labels t) (tail : Diverges lts t) : Diverges lts s :=
  InfiniteTrace.of_steps (path.toReflTransGen lts) tail

/-- A stuck state cannot be mistaken for a divergent one. -/
theorem not_diverges_of_stuck {lts : Cslib.LTS State Label} {s : State}
    (stuck : ∀ a t, ¬ lts.Tr s a t) : ¬ Diverges lts s := by
  intro diverges
  obtain ⟨t, ⟨a, step⟩, _⟩ := diverges.unfold
  exact stuck a t step

/-- Divergence is failure of CSLib strong normalization for the unlabelled transitions. -/
theorem Diverges.iff_not_sn {lts : Cslib.LTS State Label} {s : State} :
    Diverges lts s ↔ ¬ Relation.SN lts.UnlabelledTr s :=
  InfiniteTrace.iff_not_sn

/-- No state of a terminating CSLib LTS diverges. -/
theorem not_diverges_of_terminating (lts : Cslib.LTS State Label) [lts.Terminating]
    (s : State) : ¬ Diverges lts s :=
  InfiniteTrace.not_of_terminating Cslib.LTS.Terminating.terminating s

end Silmaril.Semantics.Operational

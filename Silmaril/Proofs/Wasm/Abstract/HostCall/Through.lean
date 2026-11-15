module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.NoRedex

/-!
# Runs pass through host-free steps (proofs)

In the deterministic profile, host-free steps are joinable within at most one
step on each side (`Det.DStep.join'`), and a configuration with a host-free step
is not at a host call (`Step.noRedex`), so every step from it is host-free
(`Step.split_host`). Hence **a Core run with any host from a configuration `K` to
a stuck end also reaches that end from any host-free successor `d` of `K`**, in
no more steps (`stepsN_through`). This is how the backward simulation follows a
native step: the native run predicts a host-free Core step, and the actual run,
whatever its host answers later, goes through it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {o : GrowOracle} {host : HostSemantics H}

/-- At a configuration with a host-free step, every step is host-free. -/
theorem dstep_of_step {K d c₁ : Config H} (hd : Det.DStep o K d) (h : Step (profile o) host K c₁) :
    Det.DStep o K c₁ := by
  have hn := decompose?_none_of_noRedex (Step.noRedex hd)
  rcases Step.split_host h with h | ⟨E, a, hh, args, hdc, -⟩
  · exact h
  · rw [hn] at hdc
    cases hdc

/-- **A run to a stuck end passes through every host-free step.** -/
theorem stepsN_through {n : Nat} {K c : Config H} (hrun : StepsN (profile o) host n K c)
    (hend : ∀ c', ¬ Step (profile o) host c c') {d : Config H} (hd : Det.DStep o K d) :
    ∃ m ≤ n, StepsN (profile o) host m d c := by
  induction hrun generalizing d with
  | refl => exact (hend d (Step.of_noHost host hd)).elim
  | @head n K c₁ c h₁ hrest ih =>
    have h₁' := dstep_of_step hd h₁
    obtain ⟨z, hz₁, hz₂⟩ := Det.DStep.join' h₁' hd
    rcases hz₁ with _ | hz₁
    · rcases hz₂ with _ | hz₂
      · exact ⟨n, Nat.le_succ n, hrest⟩
      · exact ⟨n + 1, le_refl _, .head (Step.of_noHost host hz₂) hrest⟩
    · obtain ⟨m', hm', hz⟩ := ih hend hz₁
      rcases hz₂ with _ | hz₂
      · exact ⟨m', by omega, hz⟩
      · exact ⟨m' + 1, by omega, .head (Step.of_noHost host hz₂) hz⟩

/-- **A run to a stuck end passes through every host-free run**: from the end of
a host-free run of `k` steps from `K`, the stuck end is reached in at most `n`
steps. -/
theorem stepsN_through_steps {n : Nat} {K T c : Config H}
    (hpred : Relation.ReflTransGen (Det.DStep o) K T) (hrun : StepsN (profile o) host n K c)
    (hend : ∀ c', ¬ Step (profile o) host c c') :
    ∃ m ≤ n, StepsN (profile o) host m T c := by
  induction hpred generalizing n with
  | refl => exact ⟨n, le_refl _, hrun⟩
  | tail _ hstep ih =>
    obtain ⟨m, hm, h⟩ := ih hrun
    obtain ⟨m', hm', h'⟩ := stepsN_through h hend hstep
    exact ⟨m', by omega, h'⟩

end Silmaril.Proofs.Wasm.Abstract.HostCall

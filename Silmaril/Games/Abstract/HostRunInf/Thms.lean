module

public import Silmaril.Games.Abstract.HostRunInf.Defs

/-!
# Productive runs against a relational host: theorems

* `hostObsInf_consistent`: every finite prefix of an observed productive run is a consistent
  answer log;
* `hostObsInf_prefix`: with `InfCoherent`, every finite prefix of an observed productive run
  is a consistent pending prefix, at the run's next call. So the productive observation
  projects to the finite pending prefixes; it adds the single coherent run joining them;
* `hostObsInf_mono`: more permissive hosts observe more productive runs;
* `hostObsInf_ofHost`: against a host function, a productive run's answers are the host's.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A : Type u}

theorem streamTake_mem {α : Type u} {ω : Nat → α} {n : Nat} {y : α}
    (h : y ∈ streamTake ω n) : ∃ i < n, ω i = y := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  exact ⟨i, i.2, rfl⟩

/-- Every finite prefix of an observed productive run is a consistent answer log. -/
theorem hostObsInf_consistent {R : HostRel E} {q : PInf E S A} {s : S} {a : A}
    {ω : Nat → Call E} (h : ω ∈ hostObsInf R q s a) (n : Nat) :
    R.Consistent (streamTake ω n) := fun _ hx =>
  let ⟨i, _, hi⟩ := streamTake_mem hx; hi ▸ h.2 i

/-- **Projection to pending prefixes.** -/
theorem hostObsInf_prefix {R : HostRel E} {p : Pending E S A} {q : PInf E S A}
    (hc : InfCoherent p q) {s : S} {a : A} {ω : Nat → Call E} (h : ω ∈ hostObsInf R q s a)
    (n : Nat) : (streamTake ω n, (ω n).1) ∈ p s a ∧ R.Consistent (streamTake ω n) :=
  ⟨hc s a ω h.1 n, hostObsInf_consistent h n⟩

/-- More permissive hosts observe more productive runs. -/
theorem hostObsInf_mono {R R' : HostRel E} (hR : ∀ m o, R m o → R' m o) {q : PInf E S A}
    {s : S} {a : A} : hostObsInf R q s a ⊆ hostObsInf R' q s a :=
  fun _ h => ⟨h.1, fun n => hR _ _ (h.2 n)⟩

/-- Against a host function, the answers of a productive run are the host's. -/
theorem hostObsInf_ofHost {h : Host E} {q : PInf E S A} {s : S} {a : A} {ω : Nat → Call E} :
    ω ∈ hostObsInf (HostRel.ofHost h) q s a ↔ ω ∈ q s a ∧ ∀ n, (ω n).2 = h (ω n).1 := by
  simp only [hostObsInf, HostRel.ofHost, Set.mem_ofPred_eq, HostAns.answer.injEq]

end Silmaril.Games.Abstract

module

public import Silmaril.Servers.Reuse.Defs
import Silmaril.Proofs.Servers.Reuse.Basic

/-!
# Instance reuse: theorems

PROVED (standard axioms):

* `seq_hostRuns`, `fresh_hostRuns`: one reused instance, and a fresh instance per request, are
  pooling policies.
* **`hostRuns_of_inv`**: if an invariant holds initially, is kept by every step, and every step
  from a state satisfying it answers within `H`, then every exchange of every pooling policy is
  in `H`. A handler correct for every reachable instance state is correct for every host.
* `counter_seq_iff`, `counter_fresh_iff`, **`counter_policy_matters`**: the counter answers
  `0, 1` to two requests on one reused instance and `0, 0` with fresh instances; so a client
  cannot rely on instance state under a host that may or may not reuse instances.
-/

@[expose] public section

namespace Silmaril.Servers.Reuse

open Silmaril.Net.Http

variable {σ : Type} {O : Origin σ} {s₀ : σ}

theorem seq_hostRuns {l : Log} (h : Seq O s₀ l) : HostRuns O s₀ l :=
  Proofs.Servers.Reuse.seq_hostRuns h

theorem fresh_hostRuns {l : Log} (h : Fresh O s₀ l) : HostRuns O s₀ l :=
  Proofs.Servers.Reuse.fresh_pooled [] h

/-- **Correctness for every reachable state is correctness for every host.** -/
theorem hostRuns_of_inv (Inv : σ → Prop) (H : Request → Response → Prop) (h0 : Inv s₀)
    (hstep : ∀ s r resp s', Inv s → O s r resp s' → Inv s')
    (hH : ∀ s r resp s', Inv s → O s r resp s' → H r resp)
    {l : Log} (hl : HostRuns O s₀ l) : ∀ p ∈ l, H p.1 p.2 :=
  Proofs.Servers.Reuse.hostRuns_of_inv Inv H h0 hstep hH hl

/-- A stateless reading: if every step answers within `H`, so does every host. -/
theorem hostRuns_of_forall (H : Request → Response → Prop)
    (hH : ∀ s r resp s', O s r resp s' → H r resp)
    {l : Log} (hl : HostRuns O s₀ l) : ∀ p ∈ l, H p.1 p.2 :=
  hostRuns_of_inv (fun _ => True) H trivial (fun _ _ _ _ _ _ => trivial)
    (fun s r resp s' _ h => hH s r resp s' h) hl

theorem counter_seq_iff {n : Nat} {r₁ r₂ : Request} {a b : Response} :
    Seq counter n [(r₁, a), (r₂, b)] ↔ a = countResponse n ∧ b = countResponse (n + 1) :=
  Proofs.Servers.Reuse.counter_seq_iff

theorem counter_fresh_iff {r₁ r₂ : Request} {a b : Response} :
    Fresh counter 0 [(r₁, a), (r₂, b)] ↔ a = countResponse 0 ∧ b = countResponse 0 :=
  Proofs.Servers.Reuse.counter_fresh_iff

/-- **The reuse policy is observable for a stateful handler**: the log of two requests on one
instance is not a log of fresh instances, and conversely; both are host runs. -/
theorem counter_policy_matters (r₁ r₂ : Request) :
    Seq counter 0 [(r₁, countResponse 0), (r₂, countResponse 1)] ∧
      ¬ Fresh counter 0 [(r₁, countResponse 0), (r₂, countResponse 1)] ∧
      Fresh counter 0 [(r₁, countResponse 0), (r₂, countResponse 0)] ∧
      ¬ Seq counter 0 [(r₁, countResponse 0), (r₂, countResponse 0)] :=
  ⟨counter_seq_iff.mpr ⟨rfl, rfl⟩,
    fun h => Proofs.Servers.Reuse.countResponse_one_ne_zero (counter_fresh_iff.mp h).2,
    counter_fresh_iff.mpr ⟨rfl, rfl⟩,
    fun h => Proofs.Servers.Reuse.countResponse_one_ne_zero (counter_seq_iff.mp h).2.symm⟩

end Silmaril.Servers.Reuse

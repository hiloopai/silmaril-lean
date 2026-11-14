module

public import Silmaril.Servers.State.Defs
import Silmaril.Proofs.Servers.State.Lin

@[expose] public section

/-!
# HTTP servers with state: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Servers.State`. Proofs in
`Silmaril.Proofs.Servers.State.Lin`.

* **`Abstraction.sat_linearizable`**: a server with an abstraction onto the atomic
  specification `B` from `t₀` satisfies `Linearizable B t₀`: every history of its host is
  explained by a sequential run of `B` that respects real time, whatever order the host runs
  and answers pending requests in, and whatever the environment does (invisibly to the
  abstraction). The linearization is the order of the handler runs.
* **`Abstraction.refines`**: such a server **refines** the closed server of `B` from `t₀`:
  every history of its host is a history of the host of `B` (a forward simulation of hosts).
* `closed_linearizable`: a server with component state is linearizable with respect to its
  own handler.
* `Server.sat_wellFormed`: every history is well formed.
* `Abstraction.reach_inv`: the abstraction's invariant holds in every reachable state.
* `Linearizable.serializable`, `Linearizable.answer` (each response in a well-formed
  linearizable history is an answer of the specification to its request, from some state),
  `Linearizable.map` (linearizability is transported along a simulation of atomic handlers).
* `Abstraction.sat_answer`, **`perRequest_answer`**: with a fresh instance per request, each
  response is an answer of the handler from the initial state.
* `Refines.sat`: refinement (history inclusion) preserves satisfaction.
-/

namespace Silmaril.Servers.State

variable {σ τ Req Resp : Type}

theorem Abstraction.sat_linearizable {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) : M.Sat (Linearizable B t₀) :=
  Proofs.Servers.State.sat_linearizable F

theorem Abstraction.refines {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) : M.Refines (Server.closed B t₀) :=
  Proofs.Servers.State.refines_closed F

theorem closed_linearizable (A : Atomic σ Req Resp) (s₀ : σ) :
    (Server.closed A s₀).Sat (Linearizable A s₀) :=
  (Abstraction.closed A s₀).sat_linearizable

theorem Server.sat_wellFormed (M : Server Req Resp) : M.Sat WellFormed :=
  Proofs.Servers.State.sat_wellFormed M

theorem Abstraction.reach_inv {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) {c : Conf M.σ Req Resp} (hc : M.Reach c) : F.inv c.st :=
  Proofs.Servers.State.reach_inv F hc

theorem Linearizable.serializable {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (h : Linearizable A s₀ H) : Serializable A s₀ H :=
  let ⟨L, hL, _⟩ := h; ⟨L, hL⟩

theorem Linearizable.answer {B : Atomic τ Req Resp} {t₀ : τ} {H : Hist Req Resp}
    (hw : WellFormed H) (h : Linearizable B t₀ H) {i : Nat} {r : Req} {s : Resp}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : ∃ t t', B t r s t' :=
  Proofs.Servers.State.linearizable_answer hw h hc hr

theorem Linearizable.map {A : Atomic σ Req Resp} {B : Atomic τ Req Resp} (α : σ → τ)
    (hsim : ∀ s r resp s', A s r resp s' → B (α s) r resp (α s')) {s₀ : σ} {H : Hist Req Resp}
    (h : Linearizable A s₀ H) : Linearizable B (α s₀) H :=
  Proofs.Servers.State.linearizable_map α hsim h

theorem Abstraction.sat_answer {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) {H : Hist Req Resp} (hH : M.Hists H) {i : Nat} {r : Req}
    {s : Resp} (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : ∃ t t', B t r s t' :=
  Proofs.Servers.State.sat_answer F hH hc hr

theorem perRequest_answer {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (hH : (Server.perRequest A s₀).Hists H) {i : Nat} {r : Req} {s : Resp}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : ∃ s', A s₀ r s s' :=
  Proofs.Servers.State.perRequest_answer hH hc hr

theorem Server.Refines.sat {M N : Server Req Resp} (h : M.Refines N) {φ : Sen Req Resp}
    (hN : N.Sat φ) : M.Sat φ :=
  fun H hH => hN H (h H hH)

end Silmaril.Servers.State

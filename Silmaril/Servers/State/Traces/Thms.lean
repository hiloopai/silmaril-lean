module

public import Silmaril.Servers.State.Traces.Defs
public import Silmaril.Servers.State.Thms
public import Silmaril.Servers.Core.Thms
public import Silmaril.Servers.Http.Defs
import Silmaril.Proofs.Servers.State.Traces.Basic
import Silmaril.Proofs.Servers.State.Traces.Wf

/-!
# State histories as core traces: theorems

PROVED (standard axioms), namespace `Silmaril.Servers.State`. Proofs in
`Silmaril.Proofs.Servers.State.Traces`.

* **One vocabulary**: an atomic handler is a core machine (`atomic_eq_machine`, by
  definition), and at HTTP an atomic handler is a machine of the core's HTTP interface
  (`atomic_eq_http`), which is also an origin of `Silmaril.Net.Http`.
* **Herlihy and Wing linearizability is the linearization-point sentence**
  (`linearizable_iff_lin`): a history whose core trace is well formed is linearizable for `A`
  from `s₀` exactly when its trace satisfies `Sen.lin` for the histories of `A` from `s₀`.
  The direction from the core to Herlihy and Wing needs no hypothesis
  (`linearizable_of_lin`).
* **The closed host is the atomic-handler server** (`closed_model_tr_iff`): the core traces of
  the histories of the host of `A` are the traces of the core's atomic-handler server of `A`
  with one connection per request.
* **Abstraction gives core refinement** (`Abstraction.model_refines`): a state server with an
  abstraction onto `B` from `t₀` refines the core's atomic-handler server of `B`, so it is
  linearizable in the core (`Abstraction.model_sat_lin`); at HTTP, it satisfies the trace
  sentence of the origin `B` (`Abstraction.model_sat_originSen`).
* Refinement of state servers is refinement of their core models (`Server.Refines.model`);
  the reading of histories as traces is injective and has one connection per request
  (`toTrace_injective`, `toTrace_onePerConn`); a history with a well-formed trace is orderly
  (`orderly_of_wf`).
-/

@[expose] public section

namespace Silmaril.Servers.State

open Silmaril.Net.Http

variable {σ τ Req Resp : Type}

/-- An atomic handler is a core machine, by definition. -/
theorem atomic_eq_machine : Atomic σ Req Resp = Machine (sig Req Resp) σ := rfl

/-- At HTTP, an atomic handler is a machine of the core's HTTP interface, and an origin. -/
theorem atomic_eq_http : Atomic σ Request Response = Machine Http.sig σ := rfl

theorem atomic_eq_origin : Atomic σ Request Response = Origin σ := rfl

theorem sig_http : sig Request Response = Http.sig := rfl

theorem toTrace_injective : Function.Injective (toTrace (Req := Req) (Resp := Resp)) :=
  Proofs.Servers.State.Traces.toTrace_injective

theorem toTrace_onePerConn (H : Hist Req Resp) : OnePerConn (toTrace H) :=
  Proofs.Servers.State.Traces.toTrace_onePerConn H

theorem orderly_of_wf {H : Hist Req Resp} (h : Sen.WF (toTrace H)) : Orderly [] H :=
  Proofs.Servers.State.Traces.orderly_of_wf h

/-- **The closed host is the core's atomic-handler server**, on traces with one connection per
request. -/
theorem closed_model_tr_iff (A : Atomic σ Req Resp) (s₀ : σ) (t : Trace (sig Req Resp)) :
    (Server.closed A s₀).model.Tr t ↔ (A.machine.server s₀).Tr t ∧ OnePerConn t :=
  Proofs.Servers.State.Traces.closed_model_tr_iff A s₀ t

theorem linearizable_of_lin {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (h : Sen.lin (A.machine.Hist s₀) (toTrace H)) : Linearizable A s₀ H :=
  Proofs.Servers.State.Traces.linearizable_of_lin h

/-- **Herlihy and Wing linearizability is the core's linearization-point sentence.** -/
theorem linearizable_iff_lin {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (hw : Sen.WF (toTrace H)) :
    Linearizable A s₀ H ↔ Sen.lin (A.machine.Hist s₀) (toTrace H) :=
  ⟨Proofs.Servers.State.Traces.lin_of_linearizable hw, linearizable_of_lin⟩

/-- **An abstraction gives refinement of the core's atomic-handler server.** -/
theorem Abstraction.model_refines {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) : M.model.Refines (B.machine.server t₀) :=
  Proofs.Servers.State.Traces.model_refines F

theorem Abstraction.model_sat_lin {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) : M.model.Sat (Sen.lin (B.machine.Hist t₀)) :=
  Model.sat_lin_of_refines_server F.model_refines

/-- At HTTP, a state server with an abstraction onto the origin `B` satisfies `B`'s trace
sentence. -/
theorem Abstraction.model_sat_originSen {M : Server Request Response} {B : Origin τ} {t₀ : τ}
    (F : Abstraction M B t₀) : M.model.Sat (Http.originSen B t₀) :=
  F.model_sat_lin

theorem Server.Refines.model {M N : Server Req Resp} (h : M.Refines N) :
    M.model.Refines N.model :=
  fun _ ⟨H, hH, he⟩ => ⟨H, h H hH, he⟩

end Silmaril.Servers.State

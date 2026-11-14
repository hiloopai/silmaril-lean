module

public import Silmaril.Servers.State.Thms
public import Silmaril.Servers.Core.Thms
public import Silmaril.Servers.State.Traces.Defs
import Silmaril.Proofs.Servers.State.Traces.Wf
import Silmaril.Proofs.Servers.State.Traces.Greedy
import Silmaril.Proofs.Servers.State.Traces.Sim

@[expose] public section

/-!
# Proofs: state histories and core traces

* `closed_model_tr_iff`: the core model of a closed server is its atomic-handler server,
  restricted to traces with one connection per request (by the two simulations of `Sim`);
* `lin_of_linearizable`, `linearizable_of_lin`: Herlihy and Wing linearizability of a history
  is the core's linearization-point sentence of its trace (through the closed host: `Greedy`
  for one direction, `Abstraction.sat_linearizable` for the other);
* `model_refines`: a server with an abstraction refines the atomic-handler server of the
  abstract handler.
-/

namespace Silmaril.Proofs.Servers.State.Traces

open Silmaril.Servers Silmaril.Servers.State

variable {σ τ Req Resp : Type}

theorem closed_model_tr_iff (A : Atomic σ Req Resp) (s₀ : σ) (t : Trace (sig Req Resp)) :
    (Server.closed A s₀).model.Tr t ↔ (A.machine.server s₀).Tr t ∧ OnePerConn t := by
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨t', m, hst, her, _⟩ := forward hc
    exact ⟨⟨t', (c.st, m), hst, her⟩, toTrace_onePerConn _⟩
  · rintro ⟨⟨t', fin, hst, rfl⟩, hone⟩
    obtain ⟨c', hc', ht⟩ := backward hst ⟨s₀, [], []⟩ .init rfl (bRel_init s₀) hone
    exact ⟨c'.hist, ⟨c', hc', rfl⟩, by simpa [toTrace] using ht⟩

theorem lin_of_linearizable {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (hw : Sen.WF (toTrace H)) (h : Linearizable A s₀ H) :
    Sen.lin (A.machine.Hist s₀) (toTrace H) :=
  (Machine.server_tr_iff _ _ _).1
    ((closed_model_tr_iff A s₀ _).1 ⟨H, hists_of_linearizable (orderly_of_wf hw) h, rfl⟩).1

theorem linearizable_of_lin {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (h : Sen.lin (A.machine.Hist s₀) (toTrace H)) : Linearizable A s₀ H := by
  obtain ⟨H', hH', he⟩ :=
    (closed_model_tr_iff A s₀ _).2 ⟨(Machine.server_tr_iff _ _ _).2 h, toTrace_onePerConn H⟩
  rw [← toTrace_injective he]
  exact closed_linearizable A s₀ H' hH'

theorem model_refines {M : Server Req Resp} {B : Atomic τ Req Resp} {t₀ : τ}
    (F : Abstraction M B t₀) : M.model.Refines (B.machine.server t₀) := by
  rintro _ ⟨H, hH, rfl⟩
  exact ((closed_model_tr_iff B t₀ _).1 ⟨H, F.refines H hH, rfl⟩).1

end Silmaril.Proofs.Servers.State.Traces

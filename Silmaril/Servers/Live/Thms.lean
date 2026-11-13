module

public import Silmaril.Servers.Live.Defs
public import Silmaril.Servers.Core.Thms
import Silmaril.Proofs.Servers.Live.Basic

/-!
# Liveness: theorems

PROVED (standard axioms).

* **`Machine.IRun.answered`**: in a weakly fair run of the atomic-handler server of a total
  machine, every request received is eventually answered (`Machine.fairObs_answered` for the
  fair observations);
* `Machine.IRun.prefix_tr`: every finite prefix of the observation of a run is a trace of the
  atomic-handler server, so the run satisfies every safety sentence of the server at every
  prefix (`Machine.IRun.always_of_sat`), in particular linearizability
  (`Machine.IRun.always_lin`);
* `Machine.ofRel_total`, `Machine.ofFun_total`: a relation that answers every request, and a
  function, are total machines.

Liveness is relative to the scheduler: the theorem assumes the host is weakly fair (a pending
handler run or a ready response is not postponed forever), and that the handler can always
answer. Whether a real host is fair is a property of the host, not of the server.
-/

@[expose] public section

namespace Silmaril.Servers

variable {A : Sig} {σ : Type} {M : Machine A σ} {q₀ : σ}

/-- **Fair runs of a total machine answer every request.** -/
theorem Machine.IRun.answered (hM : M.Total) (ρ : M.IRun q₀) (hF : ρ.Fair) :
    ISen.answered ρ.obs :=
  Proofs.Servers.Live.answered hM ρ hF

theorem Machine.fairObs_answered (hM : M.Total) {u : ITrace A} (hu : M.fairObs q₀ u) :
    ISen.answered u := by
  obtain ⟨ρ, hF, rfl⟩ := hu; exact ρ.answered hM hF

/-- Every prefix of a run is a trace of the atomic-handler server. -/
theorem Machine.IRun.prefix_tr (ρ : M.IRun q₀) (n : Nat) : (M.server q₀).Tr (ρ.obs.prefix n) :=
  ⟨_, _, (Proofs.Servers.Live.prefix_steps ρ n).1, (Proofs.Servers.Live.prefix_steps ρ n).2⟩

/-- A run satisfies, at every prefix, every sentence the server satisfies. -/
theorem Machine.IRun.always_of_sat (ρ : M.IRun q₀) {φ : Sen A} (h : (M.server q₀).Sat φ) :
    ISen.always φ ρ.obs :=
  fun n => h _ (ρ.prefix_tr n)

theorem Machine.IRun.always_lin (ρ : M.IRun q₀) : ISen.always (Sen.lin (M.Hist q₀)) ρ.obs :=
  ρ.always_of_sat (M.server_sat_lin q₀)

theorem Machine.ofRel_total {R : A.Req → A.Resp → Prop} (h : ∀ r, ∃ s, R r s) :
    (Machine.ofRel R).Total :=
  fun _ r => let ⟨s, hs⟩ := h r; ⟨s, (), hs⟩

theorem Machine.ofFun_total (f : A.Req → A.Resp) : (Machine.ofFun f).Total :=
  Machine.ofRel_total fun r => ⟨f r, rfl⟩

end Silmaril.Servers

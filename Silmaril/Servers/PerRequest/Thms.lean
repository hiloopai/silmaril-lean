module

public import Silmaril.Servers.PerRequest.Defs
public import Silmaril.Servers.Exchange.Thms
public import Silmaril.Servers.State.Traces.Thms
public import Silmaril.Servers.Reuse.Defs
import Silmaril.Proofs.Servers.PerRequest.Basic

/-!
# A fresh instance per request: theorems

PROVED (standard axioms).

**The model.**

* `Machine.perRequest_tr_iff`: the traces of a fresh instance per request are the well-formed
  traces in which every response is an answer of `M` from `q₀` to its request, however the
  requests overlap;
* `Machine.perRequest_sat_lin`: it is linearizable with respect to the histories of
  `M.fresh q₀` (`Machine.fresh_hist`: every exchange is an answer from `q₀`);
* `Machine.perRequest_seq_iff`: a sequential use is a trace exactly when every exchange is an
  answer from `q₀`;
* `Machine.perRequest_mono`: a machine with fewer answers from `q₀` has fewer traces;
* `Machine.perRequest_ofRel`: for a stateless machine, the host is the atomic-handler server.

**The instances.**

* **`Exchange.fresh_eq_perRequest`**: an exchange server with a fresh instance per request
  (the `wasi:http` reading) is the fresh-instance model of its machine;
* **`State.perRequest_model_tr_iff`**: the core traces of the state models' per-request host
  are the traces of the fresh-instance model with one connection per request
  (`State.perRequest_model_refines`);
* **`Reuse.fresh_eq_hist`**: the sequential logs of fresh instances in `Servers.Reuse` are the
  histories of `Machine.fresh`, so they are the sequential uses of the fresh-instance model
  (`Reuse.fresh_seq_iff`); the logs of one reused instance are the histories of the origin
  read as a machine (`Reuse.seq_iff`).
-/

@[expose] public section

namespace Silmaril.Servers

variable {A : Sig} {σ : Type}

/-! ## The model -/

theorem Machine.fresh_eq_ofRel (M : Machine A σ) (q₀ : σ) :
    M.fresh q₀ = Machine.ofRel fun r s => ∃ q', M q₀ r s q' := rfl

theorem Machine.fresh_hist (M : Machine A σ) (q₀ : σ) :
    (M.fresh q₀).Hist () = SeqSpec.pointwise fun r s => ∃ q', M q₀ r s q' :=
  Machine.hist_ofRel _

theorem Machine.perRequest_tr_iff (M : Machine A σ) (q₀ : σ) (t : Trace A) :
    (M.perRequest q₀).Tr t ↔ Sen.WF t ∧ Sen.atomic (fun r s => ∃ q', M q₀ r s q') t :=
  Machine.server_ofRel_tr_iff _ t

theorem Machine.perRequest_sat_lin (M : Machine A σ) (q₀ : σ) :
    (M.perRequest q₀).Sat (Sen.lin ((M.fresh q₀).Hist ())) :=
  Machine.server_sat_lin _ _

theorem Machine.perRequest_seq_iff (M : Machine A σ) (q₀ : σ)
    (h : List (ReqId × A.Req × A.Resp)) (hn : (h.map (·.1)).Nodup) :
    (M.perRequest q₀).Tr (Trace.seq h) ↔ ∀ p ∈ h.map (·.2), ∃ q', M q₀ p.1 p.2 q' := by
  rw [Machine.perRequest, Machine.server_tr_iff, Sen.lin_seq_iff h hn, Machine.fresh_hist]
  rfl

theorem Machine.perRequest_mono {τ : Type} {M : Machine A σ} {N : Machine A τ} {q₀ : σ} {p₀ : τ}
    (h : ∀ r s q', M q₀ r s q' → ∃ p', N p₀ r s p') :
    (M.perRequest q₀).Refines (N.perRequest p₀) :=
  Machine.server_mono (fun _ r s _ ⟨q', hq⟩ => h r s q' hq) ()

theorem Machine.perRequest_ofRel (R : A.Req → A.Resp → Prop) :
    (Machine.ofRel R).perRequest () = (Machine.ofRel R).server () := by
  apply Model.ext; funext t; apply propext
  rw [Machine.perRequest_tr_iff, Machine.server_ofRel_tr_iff]
  exact ⟨fun ⟨hw, h⟩ => ⟨hw, fun i r s a b => (h i r s a b).elim fun _ h' => h'⟩,
    fun ⟨hw, h⟩ => ⟨hw, fun i r s a b => ⟨(), h i r s a b⟩⟩⟩

/-! ## Exchange servers -/

/-- **The `wasi:http` reading is the fresh-instance model.** -/
theorem Exchange.fresh_eq_perRequest {I : Exchange.Iface} (M : Exchange.Model I) :
    Exchange.fresh M = (Exchange.machine M).perRequest () := by
  apply Model.ext; funext t; apply propext
  rw [Machine.perRequest_tr_iff]
  exact ⟨fun ⟨hw, h⟩ => ⟨hw, fun i r s a b => ⟨(), h i r s a b⟩⟩,
    fun ⟨hw, h⟩ => ⟨hw, fun i r s a b => (h i r s a b).elim fun _ h' => h'⟩⟩

/-! ## The state models' host -/

namespace State

variable {Req Resp : Type}

theorem Atomic.fresh_eq (A : Atomic σ Req Resp) (s₀ : σ) :
    A.fresh s₀ = Machine.fresh A.machine s₀ := rfl

/-- **The state models' per-request host is the fresh-instance model**, on traces with one
connection per request. -/
theorem perRequest_model_tr_iff (A : Atomic σ Req Resp) (s₀ : σ) (t : Trace (sig Req Resp)) :
    (Server.perRequest A s₀).model.Tr t ↔ (A.machine.perRequest s₀).Tr t ∧ OnePerConn t :=
  closed_model_tr_iff (A.fresh s₀) () t

theorem perRequest_model_refines (A : Atomic σ Req Resp) (s₀ : σ) :
    (Server.perRequest A s₀).model.Refines (A.machine.perRequest s₀) :=
  fun t ht => ((perRequest_model_tr_iff A s₀ t).1 ht).1

end State

/-! ## Instance reuse -/

namespace Reuse

open Silmaril.Net.Http

variable {O : Origin σ}

/-- **The logs of fresh instances are the histories of `Machine.fresh`.** -/
theorem fresh_eq_hist (O : Origin σ) (s₀ : σ) :
    Fresh O s₀ = ((Http.machine O).fresh s₀).Hist () := by
  rw [Machine.fresh_hist]; rfl

/-- A sequential use of the fresh-instance model is a trace exactly when its log is a log of
fresh instances. -/
theorem fresh_seq_iff (O : Origin σ) (s₀ : σ) (h : List (ReqId × Request × Response))
    (hn : (h.map (·.1)).Nodup) :
    ((Http.machine O).perRequest s₀).Tr (Trace.seq (A := Http.sig) h) ↔
      Fresh O s₀ (h.map (·.2)) :=
  Machine.perRequest_seq_iff (A := Http.sig) _ s₀ h hn

/-- The logs of one reused instance are the histories of the origin, read as a machine. -/
theorem seq_iff {s : σ} {l : Log} : Seq O s l ↔ (Http.machine O).Hist s l :=
  Proofs.Servers.PerRequest.seq_iff

end Reuse

end Silmaril.Servers

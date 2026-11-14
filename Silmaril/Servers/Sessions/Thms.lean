module

public import Silmaril.Servers.Sessions.Defs
import Silmaril.Proofs.Servers.Sessions.Basic

/-!
# Connection events: theorems

PROVED (standard axioms), namespace `Silmaril.Servers`.

* **`CSen.wf_erase`**, **`CSen.exists_of_wf`**: the core trace of a well-formed connection trace
  is well formed, and every well-formed core trace is the core trace of a well-formed
  connection trace (open every connection it uses first);
* so, for a model whose traces are well formed, **core sentences mean the same with
  connections** (`Model.withConns_sat_iff`), and **refinement is the same with connections**
  (`Model.withConns_refines_iff`); `Model.withConns_mono`: refinement is preserved;
* **`CSen.graceful_answered`**: in a well-formed trace that closes gracefully and closes every
  connection it opens, every request is answered; `Model.graceful_refines`: graceful traces
  are traces with connections, and `Model.graceful_sat`: they close gracefully.
-/

@[expose] public section

namespace Silmaril.Servers

variable {A : Sig}

theorem CSen.wf_erase {t : CTrace A} (h : CSen.WF t) : Sen.WF t.erase :=
  Proofs.Servers.Sessions.wf_erase h

theorem CSen.exists_of_wf {t : Trace A} (h : Sen.WF t) :
    ∃ ct : CTrace A, CSen.WF ct ∧ ct.erase = t :=
  Proofs.Servers.Sessions.exists_of_wf h

theorem Model.withConns_sat_wf (M : Model A) : M.withConns.Sat (CSen.lift Sen.WF) :=
  fun _ ht => CSen.wf_erase ht.1

theorem Model.withConns_sat {M : Model A} {φ : Sen A} (h : M.Sat φ) :
    M.withConns.Sat (CSen.lift φ) :=
  fun _ ht => h _ ht.2

/-- **Core sentences mean the same with connections.** -/
theorem Model.withConns_sat_iff {M : Model A} (hM : M.Sat Sen.WF) (φ : Sen A) :
    M.withConns.Sat (CSen.lift φ) ↔ M.Sat φ := by
  refine ⟨fun h t ht => ?_, Model.withConns_sat⟩
  obtain ⟨ct, hw, rfl⟩ := CSen.exists_of_wf (hM t ht)
  exact h ct ⟨hw, ht⟩

theorem Model.withConns_mono {M N : Model A} (h : M.Refines N) :
    M.withConns.Refines N.withConns :=
  fun _ ⟨hw, ht⟩ => ⟨hw, h _ ht⟩

/-- **Refinement is the same with connections.** -/
theorem Model.withConns_refines_iff {M N : Model A} (hM : M.Sat Sen.WF) :
    M.withConns.Refines N.withConns ↔ M.Refines N := by
  refine ⟨fun h t ht => ?_, Model.withConns_mono⟩
  obtain ⟨ct, hw, rfl⟩ := CSen.exists_of_wf (hM t ht)
  exact (h ct ⟨hw, ht⟩).2

/-- **A graceful trace that closes every connection answers every request.** -/
theorem CSen.graceful_answered {t : CTrace A} (hw : CSen.WF t) (hg : CSen.graceful t)
    (hc : CSen.allClosed t) {i : ReqId} {r : A.Req} (hr : Event.recv i r ∈ t.erase) :
    ∃ s, Event.send i s ∈ t.erase :=
  Proofs.Servers.Sessions.graceful_answered hw hg hc hr

theorem Model.graceful_refines (M : Model A) : M.graceful.Refines M.withConns :=
  fun _ ⟨hw, _, ht⟩ => ⟨hw, ht⟩

theorem Model.graceful_sat (M : Model A) : M.graceful.Sat CSen.graceful :=
  fun _ ht => ht.2.1

end Silmaril.Servers

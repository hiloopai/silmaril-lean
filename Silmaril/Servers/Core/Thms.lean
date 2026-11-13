module

public import Silmaril.Servers.Core.Defs
import Silmaril.Proofs.Servers.Core.Lin
import Silmaril.Proofs.Servers.Core.Seq
import Silmaril.Proofs.Servers.Core.Pipe
import Silmaril.Proofs.Servers.Core.Unmap

/-!
# The server institution: theorems

* **Refinement is trace inclusion** and transfers satisfaction (`Model.sat_of_refines`), and is a
  preorder (`Model.Refines.refl`, `Model.Refines.trans`).
* **The atomic-handler server is linearizable**, and its traces are exactly the linearizable
  ones (`Machine.server_tr_iff`, `Machine.server_sat_lin`): the linearization-point reading of
  a sequential specification is the operational one.
* **Linearizable traces are well formed** (`Sen.wf_of_lin`).
* **Functions and relations lift**: a stateless machine allows exactly the pointwise histories
  (`Machine.hist_ofRel`), and on well-formed traces linearizability with respect to a stateless
  specification is the atomic sentence (`Sen.lin_pointwise_iff`, `Sen.lin_ofRel_iff`). So the
  atomic-handler server of a relation has exactly the well-formed atomic traces
  (`Machine.server_ofRel_tr_iff`), and the function server is that of its function
  (`Model.ofFun_eq_server`).
* **Sequential use**: a trace that answers each request before the next arrives is
  linearizable exactly when its history is allowed (`Sen.lin_seq_iff`): the linearization points
  are forced. So for sequential clients the trace sentence is the sequential specification.
* **Pipelining**: the pipelining server of a machine (responses in request order on each
  connection) refines its atomic-handler server, so it is linearizable, and it answers in order
  (`Machine.pipeServer_refines`, `Machine.pipeServer_sat_lin`, `Machine.pipeServer_sat_inOrder`).
* **Linearizable implies sequentially consistent** (`Sen.sc_of_lin`).
* **Refinement is preserved by the lifts**: weaker relations, specifications and machines give
  weaker sentences and larger servers (`Sen.atomic_mono`, `Sen.lin_mono`, `Sen.sc_mono`,
  `Machine.server_mono`), and a model that refines the atomic-handler server of `M` satisfies
  `M`'s linearizability sentence (`Model.sat_lin_of_refines_server`).
* **Morphisms**: the atomic sentence translates to the atomic sentence of the projected relation
  (`Hom.sen_atomic`); a trace linearizable for the translated specification maps to a
  linearizable trace (`Hom.lin_trace`), so reducts of linearizable models are linearizable
  (`Hom.mod_sat_lin`).
-/

@[expose] public section

namespace Silmaril.Servers

variable {A : Sig}

/-! ## Refinement -/

theorem Model.Refines.refl (M : Model A) : M.Refines M := le_refl M

theorem Model.Refines.trans {M N P : Model A} (h₁ : M.Refines N) (h₂ : N.Refines P) :
    M.Refines P := le_trans h₁ h₂

/-- A refinement satisfies every sentence its abstraction satisfies. -/
theorem Model.sat_of_refines {M N : Model A} (h : M.Refines N) {φ : Sen A} (hN : N.Sat φ) :
    M.Sat φ := fun t ht => hN t (h t ht)

/-! ## The atomic-handler server -/

/-- **The traces of the atomic-handler server of a machine are exactly the traces linearizable
with respect to the machine.** -/
theorem Machine.server_tr_iff {σ : Type} (M : Machine A σ) (q₀ : σ) (t : Trace A) :
    (M.server q₀).Tr t ↔ Sen.lin (M.Hist q₀) t :=
  Proofs.Servers.Core.server_tr_iff M q₀ t

/-- **The atomic-handler server of a machine is linearizable.** -/
theorem Machine.server_sat_lin {σ : Type} (M : Machine A σ) (q₀ : σ) :
    (M.server q₀).Sat (Sen.lin (M.Hist q₀)) := fun t ht => (M.server_tr_iff q₀ t).1 ht

/-- Linearizable traces are well formed. -/
theorem Sen.wf_of_lin {S : SeqSpec A} {t : Trace A} (h : Sen.lin S t) : Sen.WF t :=
  Proofs.Servers.Core.wf_of_lin h

/-! ## Functions and relations -/

/-- A stateless machine allows exactly the histories whose every pair `R` allows. -/
theorem Machine.hist_ofRel (R : A.Req → A.Resp → Prop) :
    (Machine.ofRel R).Hist () = SeqSpec.pointwise R :=
  Proofs.Servers.Core.hist_ofRel R

/-- **For stateless specifications, linearizability is the atomic sentence** (on well-formed
traces). -/
theorem Sen.lin_pointwise_iff (R : A.Req → A.Resp → Prop) {t : Trace A} (hw : Sen.WF t) :
    Sen.lin (SeqSpec.pointwise R) t ↔ Sen.atomic R t :=
  ⟨Proofs.Servers.Core.atomic_of_lin, Proofs.Servers.Core.lin_of_atomic hw⟩

theorem Sen.lin_ofRel_iff (R : A.Req → A.Resp → Prop) {t : Trace A} (hw : Sen.WF t) :
    Sen.lin ((Machine.ofRel R).Hist ()) t ↔ Sen.atomic R t := by
  rw [Machine.hist_ofRel]; exact Sen.lin_pointwise_iff R hw

/-- The atomic-handler server of a relation has exactly the well-formed atomic traces. -/
theorem Machine.server_ofRel_tr_iff (R : A.Req → A.Resp → Prop) (t : Trace A) :
    ((Machine.ofRel R).server ()).Tr t ↔ Sen.WF t ∧ Sen.atomic R t := by
  rw [Machine.server_tr_iff]
  exact ⟨fun h => ⟨Sen.wf_of_lin h, (Sen.lin_ofRel_iff R (Sen.wf_of_lin h)).1 h⟩,
    fun ⟨hw, h⟩ => (Sen.lin_ofRel_iff R hw).2 h⟩

/-- **A function server is the atomic-handler server of its function.** -/
theorem Model.ofFun_eq_server (f : A.Req → A.Resp) :
    Model.ofFun f = (Machine.ofFun f).server () := by
  apply Model.ext; funext t; apply propext
  exact (Machine.server_ofRel_tr_iff _ t).symm

/-- A function server satisfies its functional sentence. -/
theorem Model.ofFun_sat (f : A.Req → A.Resp) : (Model.ofFun f).Sat (Sen.ofFun f) :=
  fun _ ht => ht.2

/-! ## Pipelining -/

/-- The pipelining server refines the atomic-handler server. -/
theorem Machine.pipeServer_refines {σ : Type} (M : Machine A σ) (q₀ : σ) :
    (M.pipeServer q₀).Refines (M.server q₀) :=
  Proofs.Servers.Core.pipeServer_le M q₀

/-- **The pipelining server answers each connection in request order.** -/
theorem Machine.pipeServer_sat_inOrder {σ : Type} (M : Machine A σ) (q₀ : σ) :
    (M.pipeServer q₀).Sat Sen.inOrder :=
  Proofs.Servers.Core.pipeServer_inOrder M q₀

theorem Machine.pipeServer_sat_lin {σ : Type} (M : Machine A σ) (q₀ : σ) :
    (M.pipeServer q₀).Sat (Sen.lin (M.Hist q₀)) :=
  fun t ht => (M.server_sat_lin q₀) t (M.pipeServer_refines q₀ t ht)

/-! ## Sequential use -/

/-- **A sequential use is linearizable exactly when its history is allowed.** -/
theorem Sen.lin_seq_iff {S : SeqSpec A} (h : List (ReqId × A.Req × A.Resp))
    (hn : (h.map (·.1)).Nodup) : Sen.lin S (Trace.seq h) ↔ S (h.map (·.2)) :=
  ⟨Proofs.Servers.Core.seq_of_lin h, Proofs.Servers.Core.lin_of_seq h hn⟩

/-! ## Sequential consistency -/

theorem Sen.sc_of_lin {S : SeqSpec A} {t : Trace A} (h : Sen.lin S t) : Sen.sc S t :=
  ⟨t, fun _ => rfl, h⟩

/-! ## Refinement and the lifts -/

theorem Sen.atomic_mono {R R' : A.Req → A.Resp → Prop} (hR : ∀ r s, R r s → R' r s) :
    Sen.atomic R ≤ Sen.atomic R' := fun _ H i r s hr hs => hR r s (H i r s hr hs)

theorem Sen.lin_mono {S S' : SeqSpec A} (hS : S ≤ S') : Sen.lin S ≤ Sen.lin S' :=
  Proofs.Servers.Core.lin_mono hS

theorem Sen.sc_mono {S S' : SeqSpec A} (hS : S ≤ S') : Sen.sc S ≤ Sen.sc S' :=
  fun _ ⟨t₂, hc, hl⟩ => ⟨t₂, hc, Sen.lin_mono hS t₂ hl⟩

/-- A machine with more steps has a larger atomic-handler server. -/
theorem Machine.server_mono {σ : Type} {M M' : Machine A σ}
    (hM : ∀ q r s q', M q r s q' → M' q r s q') (q₀ : σ) : M.server q₀ ≤ M'.server q₀ :=
  Proofs.Servers.Core.server_mono hM q₀

/-- **A model that refines the atomic-handler server of a machine is linearizable** with respect
to the machine. -/
theorem Model.sat_lin_of_refines_server {σ : Type} {N : Model A} {M : Machine A σ} {q₀ : σ}
    (h : N.Refines (M.server q₀)) : N.Sat (Sen.lin (M.Hist q₀)) :=
  Model.sat_of_refines h (M.server_sat_lin q₀)

/-! ## Morphisms -/

/-- The atomic sentence translates to the atomic sentence of the projected relation. -/
theorem Hom.sen_atomic {B : Sig} (h : Hom A B) (R : A.Req → A.Resp → Prop) :
    h.sen (Sen.atomic R) = Sen.atomic fun r s => R (h.req r) (h.resp s) :=
  Proofs.Servers.Core.sen_atomic h R

/-- A trace linearizable for the translated specification is seen as a linearizable trace. -/
theorem Hom.lin_trace {B : Sig} (h : Hom A B) {S : SeqSpec A} {t : Trace B}
    (hl : Sen.lin (h.seq S) t) : Sen.lin S (h.trace t) :=
  Proofs.Servers.Core.lin_trace h hl

/-- **Reducts of linearizable models are linearizable.** -/
theorem Hom.mod_sat_lin {B : Sig} (h : Hom A B) {M : Model B} {S : SeqSpec A}
    (hM : M.Sat (Sen.lin (h.seq S))) : (h.mod M).Sat (Sen.lin S) :=
  (h.sat_sen_iff M _).1 fun t ht => h.lin_trace (hM t ht)

/-- **The converse of `Hom.lin_trace`**, for a morphism that sees every response. -/
theorem Hom.lin_of_trace {B : Sig} (h : Hom A B) (hsur : Function.Surjective h.resp)
    {S : SeqSpec A} {t : Trace B} (hl : Sen.lin S (h.trace t)) : Sen.lin (h.seq S) t :=
  Proofs.Servers.Core.lin_of_trace h hsur hl

theorem Hom.lin_trace_iff {B : Sig} (h : Hom A B) (hsur : Function.Surjective h.resp)
    {S : SeqSpec A} {t : Trace B} : Sen.lin (h.seq S) t ↔ Sen.lin S (h.trace t) :=
  ⟨h.lin_trace, h.lin_of_trace hsur⟩

/-- **Linearizability translates along a morphism that sees every response.** -/
theorem Hom.sen_lin {B : Sig} (h : Hom A B) (hsur : Function.Surjective h.resp)
    (S : SeqSpec A) : h.sen (Sen.lin S) = Sen.lin (h.seq S) := by
  funext t; exact propext (h.lin_trace_iff hsur).symm

theorem Hom.sat_lin_iff {B : Sig} (h : Hom A B) (hsur : Function.Surjective h.resp)
    {M : Model B} {S : SeqSpec A} : M.Sat (Sen.lin (h.seq S)) ↔ (h.mod M).Sat (Sen.lin S) := by
  rw [← h.sen_lin hsur]; exact h.sat_sen_iff M _

end Silmaril.Servers

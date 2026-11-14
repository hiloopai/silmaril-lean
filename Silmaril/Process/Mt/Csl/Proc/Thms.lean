module

public import Silmaril.Process.Mt.Csl.Proc.Defs
public import Silmaril.Process.Mt.Csl.Thms
import Silmaril.Proofs.Process.Mt.Csl.Proc

/-!
# The decomposition on the multithreaded process model: what is proved

PROVED (standard axioms; proofs in `Silmaril/Proofs/Process/Mt/Csl/Proc.lean`), for every user
ISA `U` (the x86 one, `Mt.X86.mtX`, included), primitive table `P` and base relation:

* `step_reach`, `reach_reach`: every step (run) of the multithreaded process under SC is a run of
  the thread machine `procT U P base` from the encoded configuration;
* `fault_enc`: a process fault is a thread-machine fault;
* **`mt_adequacy`**: if the encoded start satisfies the decomposition's compatibility conditions
  (every thread safe on what it owns, under the invariant `I`), then every reachable process
  configuration has **no fault**, and its encoding is `Good` (no data race between plain steps,
  the invariant holds of the shared part, exited threads meet their postconditions);
* `mt_adequacy_init`: the same from a one-thread start (`MtCfg.init`), from that thread's
  single-threaded problem;
* `mt_adequacy_tso`: the same for the process under **x86-TSO** (`MtStep U tso`, byte store
  buffers), **conditional** on the open statement `Task.tsoSound` (DRF for the TSO process:
  certified programs have only SC behaviours) and on local plain steps (`LocalAcc`).

So a multithreaded process problem reduces to one single-threaded problem per thread
(`Csl.Safe` for `procT`: plain steps footprint-checked against ownership, primitives, system calls
and library steps as atomic steps with the invariant) plus compatibility. Under SC this is
unconditional; under TSO it rests on `Task.tsoSound`. XL is not covered here.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Csl.Proc

open Silmaril.Process.Mt

variable {γ : Type} {U : UIsa γ} {P : PrimTable γ} {base : Base γ}

/-- Every process step is a run of the thread machine. -/
theorem step_reach {C C' : MtCfg U.St γ sc.S} (h : MtStep U sc P base C C') :
    Reach (procT U P base) (enc P base C) (enc P base C') :=
  Silmaril.Proofs.Process.Mt.Csl.Proc.step_reach h

/-- Every process run is a run of the thread machine. -/
theorem reach_reach {C C' : MtCfg U.St γ sc.S} (h : MtReach U sc P base C C') :
    Reach (procT U P base) (enc P base C) (enc P base C') :=
  Silmaril.Proofs.Process.Mt.Csl.Proc.reach_reach h

/-- A process fault is a thread-machine fault. -/
theorem fault_enc {C : MtCfg U.St γ sc.S} (h : MtFault U sc P C) :
    Fault (procT U P base) (enc P base C) :=
  Silmaril.Proofs.Process.Mt.Csl.Proc.fault_enc h

/-- **Adequacy for the multithreaded process.** -/
theorem mt_adequacy {I : HProp Loc (Val γ)} {Q : Nat → TRec U.St → Heap Loc (Val γ) → Prop}
    {C₀ C : MtCfg U.St γ sc.S} {hs : Nat → Heap Loc (Val γ)} {hI : Heap Loc (Val γ)}
    (g : GInv (procT U P base) I Q (enc P base C₀) hs hI) (r : MtReach U sc P base C₀ C) :
    ¬ MtFault U sc P C ∧ Good (procT U P base) I Q (enc P base C) :=
  let gd := adequacy g (reach_reach r)
  ⟨fun f => gd.1 (fault_enc f), gd⟩

/-- **Adequacy from a one-thread start**: thread `tid` in state `s`, owning `h₀`, safe; the rest
of the shared state `hI ⊨ I`. -/
theorem mt_adequacy_init {I : HProp Loc (Val γ)} {Q : Nat → TRec U.St → Heap Loc (Val γ) → Prop}
    {tid : Nat} {s : U.St} {m : Memory} {g : γ} {h₀ hI : Heap Loc (Val γ)} {C : MtCfg U.St γ sc.S}
    (hs : Safe (procT U P base) I Q tid { st := .run s } h₀) (hIp : I hI)
    (d : Heap.Disjoint h₀ hI) (ag : (store γ).Agrees h₀ ⟨m, {}, g, false, none⟩)
    (agI : (store γ).Agrees hI ⟨m, {}, g, false, none⟩)
    (r : MtReach U sc P base (MtCfg.init tid s m g) C) :
    ¬ MtFault U sc P C ∧ Good (procT U P base) I Q (enc P base C) :=
  mt_adequacy (C₀ := MtCfg.init tid s m g) (ginv_single hs hIp d ag agI) r

/-- **Adequacy for the multithreaded process under x86-TSO**, conditional on the open DRF
statement `Task.tsoSound` and on local plain steps: no TSO fault, and every reachable TSO
configuration stands for a `Good` configuration. -/
theorem mt_adequacy_tso (hT : Task.tsoSound U P base) (hloc : LocalAcc U)
    {I : HProp Loc (Val γ)} {Q : Nat → TRec U.St → Heap Loc (Val γ) → Prop}
    {c₀ c : MtCfg U.St γ tso.S} {C₀ : Cfg (procT U P base)} {hs : Nat → Heap Loc (Val γ)}
    {hI : Heap Loc (Val γ)} (g : GInv (procT U P base) I Q C₀ hs hI) (ha : tsoAbs U P base c₀ C₀)
    (r : Star (MtStep U tso P base) c₀ c) :
    ¬ MtFault U tso P c ∧ ∃ C, tsoAbs U P base c C ∧ Good (procT U P base) I Q C :=
  adequacy_model (X := tsoModel U P base) (hT hloc I Q) g ha r

end Silmaril.Process.Mt.Csl.Proc

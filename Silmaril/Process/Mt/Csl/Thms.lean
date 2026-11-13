module

public import Silmaril.Process.Mt.Csl.Defs
import Silmaril.Proofs.Process.Mt.Csl.Adequacy

/-!
# Adequacy of the thread-modular decomposition: what is proved

All statements are PROVED with no axioms beyond Lean's core (proofs in
`Silmaril/Proofs/Process/Mt/Csl/Adequacy.lean`). `U` is any thread machine over any store,
`I` any resource invariant, `Q` any family of postconditions.

* `ginv_step`, `ginv_reach`: the compatibility conditions `GInv` (disjoint owned heaps, the
  invariant, every thread safe) are preserved by every step of the multi-threaded system, hence
  along every run;
* `no_fault`, `no_race`, `post`: under `GInv` no thread can fault, no two threads' next plain
  steps access a common address, and every finished thread meets its postcondition on what it
  owns;
* **`adequacy`**: if the start satisfies `GInv`, every reachable configuration is `Good` (no
  fault, no race, the invariant holds of the shared part, finished threads meet their
  postconditions);
* `ginv_single`: a process starting as one safe thread owning `h₀`, with the rest of memory
  `hI ⊨ I`, satisfies `GInv`; with `adequacy`, `adequacy_single`;
* `adequacy_model`: the same through any concrete model `X` (store buffers, primitives run by
  their code) that refines SC with atomic steps on certified programs (`Model.Sound`);
* `atomOk_prims`: the atomic obligations of a primitive call site follow from the obligations of
  each primitive it may call (`PrimOk`).

The memory model of `Step` is sequential consistency with atomic primitives. Weaker models enter
through `Model.Sound`, an explicit hypothesis of `adequacy_model`: for x86-TSO or the loose
model XL it is a DRF theorem (programs that are race-free modulo atomic steps, which `no_race`
gives, have only SC behaviours), and for a model running a primitive's implementation code it is
that primitive's correctness under the memory model. Neither is proved here.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Csl

variable {M A V : Type} {S : Store M A V} {U : TIsa S} {I : HProp A V}
  {Q : Nat → U.St → Heap A V → Prop}

/-- **Preservation**: one step keeps the compatibility conditions (for new heaps). -/
theorem ginv_step {C C' : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U I Q C hs hI) (st : Step U C C') : ∃ hs' hI', GInv U I Q C' hs' hI' :=
  Silmaril.Proofs.Process.Mt.Csl.ginv_step g st

/-- **Preservation along runs.** -/
theorem ginv_reach {C C' : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U I Q C hs hI) (r : Reach U C C') : ∃ hs' hI', GInv U I Q C' hs' hI' :=
  Silmaril.Proofs.Process.Mt.Csl.ginv_reach g r

/-- Under `GInv` no thread can fault. -/
theorem no_fault {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C hs hI) :
    ¬ Fault U C :=
  Silmaril.Proofs.Process.Mt.Csl.no_fault g

/-- Under `GInv` there is no data race. -/
theorem no_race {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C hs hI) :
    ¬ Race U C :=
  Silmaril.Proofs.Process.Mt.Csl.no_race g

/-- Under `GInv` a finished thread meets its postcondition on what it owns. -/
theorem post {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C hs hI)
    {t : Nat} {s : U.St} (ht : C.th t = some s) (hd : U.done s) : Q t s (hs t) :=
  Silmaril.Proofs.Process.Mt.Csl.post g ht hd

/-- **Adequacy**: from a start satisfying the compatibility conditions, every reachable
configuration of the multi-threaded system is `Good`. -/
theorem adequacy {C₀ C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U I Q C₀ hs hI) (r : Reach U C₀ C) : Good U I Q C :=
  Silmaril.Proofs.Process.Mt.Csl.adequacy g r

/-- One safe thread owning `h₀`, the rest of the memory `hI ⊨ I`: the compatibility
conditions hold. -/
theorem ginv_single {t₀ : Nat} {s₀ : U.St} {m₀ : M} {h₀ hI : Heap A V}
    (hs : Safe U I Q t₀ s₀ h₀) (hIp : I hI) (d : Heap.Disjoint h₀ hI) (ag : S.Agrees h₀ m₀)
    (agI : S.Agrees hI m₀) :
    GInv U I Q (Cfg.single U t₀ s₀ m₀) (fun t => if t = t₀ then h₀ else Heap.empty) hI :=
  Silmaril.Proofs.Process.Mt.Csl.ginv_single hs hIp d ag agI

/-- **Adequacy from one thread**: a process that starts as one thread, safe on what it owns,
with the rest of memory satisfying the invariant, is `Good` in every reachable configuration. -/
theorem adequacy_single {t₀ : Nat} {s₀ : U.St} {m₀ : M} {h₀ hI : Heap A V} {C : Cfg U}
    (hs : Safe U I Q t₀ s₀ h₀) (hIp : I hI) (d : Heap.Disjoint h₀ hI) (ag : S.Agrees h₀ m₀)
    (agI : S.Agrees hI m₀) (r : Reach U (Cfg.single U t₀ s₀ m₀) C) : Good U I Q C :=
  adequacy (ginv_single hs hIp d ag agI) r

/-- **Adequacy under a concrete model** (store buffers, primitive implementations) that refines
SC with atomic steps on certified programs (`Model.Sound`): no concrete fault, and every
reachable concrete configuration stands for a `Good` abstract one. -/
theorem adequacy_model {X : Model U} (hX : X.Sound I Q) {c₀ c : X.Conf} {C₀ : Cfg U}
    {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C₀ hs hI) (ha : X.abs c₀ C₀)
    (r : Star X.step c₀ c) : ¬ X.fault c ∧ ∃ C, X.abs c C ∧ Good U I Q C :=
  Silmaril.Proofs.Process.Mt.Csl.adequacy_model hX g ha r

/-- The atomic obligations of a primitive call site follow from those of each primitive it may
call. -/
theorem atomOk_prims {σ : Type} {P : Prims σ M} {K : σ → Heap A V → Prop} {t : Nat} {s : σ}
    {h : Heap A V}
    (hc : ∀ p args, P.call s = some (p, args) →
      PrimOk (S := S) I (P.spec p) (fun r h' => K (P.resume s r) h') t args h) :
    AtomicOk (S := S) I (P.afault t s) (fun m s' m' => P.atom t s m s' m') K h :=
  Silmaril.Proofs.Process.Mt.Csl.atomOk_prims hc

end Silmaril.Process.Mt.Csl

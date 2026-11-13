module

public import Silmaril.X86.Concurrency.Cir.Robust.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Robust.Witness

/-!
# The CIR explorer and TSO-robustness checker: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Robust/`). They are about the CIR-native machines:
`Csl.OStep .tso` (x86-TSO store buffers) and `Csl.ScStep` (SC interleaving), for a closed
program instance given as a concrete start configuration `c0` of `N` threads.

* `tsoCheck_sound`: if `tsoCheck` passes, `P` holds of (the concrete form of) every finished,
  drained configuration the TSO machine reaches.
* `robustB_sound`: if `robustB` passes, every finished, drained TSO configuration has the thread
  states and memory of a finished configuration the SC machine reaches. This is **TSO
  robustness** of the instance's final states.
* `scCheck_sound`: if `scCheck` passes, `P` holds of every finished SC configuration.
* `tsoStates_reach`, `witness_of_any`: every configuration the TSO exploration lists is
  TSO-reachable, so a listed finished configuration is a witness.

The checks are sound whatever the exploration returns: the TSO and SC checks verify that the
explored set is closed under the (fused) successors; only completeness depends on the fuel.
Silent thread steps are run eagerly; that this loses nothing is part of the proofs
(`Robust.fused_reach` in the proofs module: silent steps are deterministic, exclusive with
labelled steps, and commute with other threads' steps and with flushes).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir.Csl (OCfg Cfg OReach ScReach)

/-- **The TSO final-state check is sound.** -/
theorem tsoCheck_sound {N fuel : Nat} {c0 : CSt} {P : CSt → Bool} (h : tsoCheck N fuel c0 P = true)
    {C : OCfg} (hr : OReach .tso N c0.cfg.toO C) (hd : C.Drained)
    (hfin : ∀ t < N, (C.ts t).1 = .skip) : ∃ d, P d = true ∧ d.ocfg = C :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.tsoCheck_sound h hr hd hfin

/-- **The TSO-robustness check is sound**: every finished, drained TSO configuration is (in its
threads and memory) a finished SC configuration. -/
theorem robustB_sound {N fT fS : Nat} {c0 : CSt} (h : robustB N fT fS c0 = true) {C : OCfg}
    (hr : OReach .tso N c0.cfg.toO C) (hd : C.Drained) (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ C' : Cfg, ScReach N c0.cfg C' ∧ C'.ts = C.ts ∧ C'.mem = C.mem :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.robustB_sound h hr hd hfin

/-- **The SC final-state check is sound.** -/
theorem scCheck_sound {N fuel : Nat} {c0 : CSt} {P : CSt → Bool} (h : scCheck N fuel c0 P = true)
    {C : Cfg} (hr : ScReach N c0.cfg C) (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ d, P d = true ∧ d.cfg = C :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.scCheck_sound h hr hfin

/-- **Explored TSO configurations are TSO-reachable.** -/
theorem tsoStates_reach {N fuel : Nat} {c0 : CSt} (hb : c0.buf.length = N) {e : CSt}
    (he : e ∈ tsoStates N fuel c0) : OReach .tso N c0.ocfg e.ocfg :=
  (Silmaril.Proofs.X86.Concurrency.Cir.Robust.tsoStates_reach hb he).1

/-- **A TSO witness**: a finished, drained explored configuration satisfying `P` is
TSO-reachable. -/
theorem witness_of_any {N fuel : Nat} {c0 : CSt} (hb : c0.buf.length = N)
    (he : c0.buf.all List.isEmpty = true) {P : CSt → Bool}
    (h : ((tsoStates N fuel c0).any fun c => c.doneB N && c.drainedB && P c) = true) :
    ∃ d, OReach .tso N c0.cfg.toO d.ocfg ∧ d.ocfg.Drained ∧ (∀ t < N, (d.ocfg.ts t).1 = .skip) ∧
      P d = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.witness_of_any hb he h

/-- **Every enumerated TSO step of thread `t` is a TSO step** (re-exported for scheduled
witnesses). -/
theorem tsoStepT_sound {N : Nat} {c : CSt} {t : Nat} (ht : t < N) (hb : t < c.buf.length)
    {d : CSt} (h : d ∈ tsoStepT c t) : Csl.OStep .tso N c.ocfg d.ocfg :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.tsoStepT_sound ht hb h

/-- A start configuration with empty buffers is its own buffered form. -/
theorem start_toO {c0 : CSt} (h : c0.buf.all List.isEmpty = true) : c0.cfg.toO = c0.ocfg :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.toO_ocfg h

end Silmaril.X86.Concurrency.Cir.Robust

module

public import Silmaril.X86.Concurrency.Cir.Robust.Sym.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Robust.Sym

/-!
# Thread-symmetry reduction: what is proved

PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Robust/Sym.lean`), about the CIR-native TSO machine
`Csl.OStep .tso` and a closed program instance given as a start configuration `c0` of `N`
threads:

* `ostep_perm`, `oreach_perm`: renaming the threads by a permutation of `0 … N-1` (`TPerm N`)
  maps TSO steps and runs to TSO steps and runs;
* `symCheck_sound`: if `symCheck` passes, every finished, drained configuration the TSO machine
  reaches is a renaming of a configuration satisfying `P`;
* `symCheck_mem`: for a property of memory alone, it is the property of every finished,
  drained reachable configuration;
* `symWitness_of_any`: a finished, drained explored configuration satisfying `P` is, renamed,
  TSO-reachable (non-vacuity witnesses).

The search is untrusted (the closure check carries soundness), and the canonical form need not
be canonical (a collision only costs reduction).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir.Csl (OCfg OStep OReach Heap)

/-- **Renamed TSO steps are TSO steps.** -/
theorem ostep_perm {M : Csl.OModel} {N : Nat} (σ : TPerm N) {C C' : OCfg} (h : OStep M N C C') :
    OStep M N (permCfg C σ.f) (permCfg C' σ.f) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.ostep_perm σ h

/-- **Renamed TSO runs are TSO runs.** -/
theorem oreach_perm {M : Csl.OModel} {N : Nat} (σ : TPerm N) {C C' : OCfg} (h : OReach M N C C') :
    OReach M N (permCfg C σ.f) (permCfg C' σ.f) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.oreach_perm σ h

/-- **The symmetry-reduced TSO final-state check is sound.** -/
theorem symCheck_sound {N fuel : Nat} {c0 : CSt} {P : CSt → Bool}
    (h : symCheck N fuel c0 P = true) {C : OCfg} (hr : OReach .tso N c0.cfg.toO C)
    (hd : C.Drained) (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ d, P d = true ∧ ∃ σ : TPerm N, d.ocfg = permCfg C σ.f :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.symCheck_sound h hr hd hfin

/-- **The check for a property of memory.** -/
theorem symCheck_mem {N fuel : Nat} {c0 : CSt} {Q : Heap → Prop} {P : CSt → Bool}
    (hPQ : ∀ d, P d = true → Q d.ocfg.mem) (h : symCheck N fuel c0 P = true) {C : OCfg}
    (hr : OReach .tso N c0.cfg.toO C) (hd : C.Drained) (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    Q C.mem :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.symCheck_mem hPQ h hr hd hfin

/-- **Witnesses up to renaming.** -/
theorem symWitness_of_any {N fuel : Nat} {c0 : CSt} (he : c0.buf.all List.isEmpty = true)
    (hl : (normAll N tauFuel c0).ts.length = N) (hbl : (normAll N tauFuel c0).buf.length = N)
    {P : CSt → Bool}
    (h : ((symStates N fuel c0).any fun c => c.doneB N && c.drainedB && P c) = true) :
    ∃ d, P d = true ∧ ∃ σ : TPerm N, OReach .tso N c0.cfg.toO (permCfg d.ocfg σ.f) ∧
      (permCfg d.ocfg σ.f).Drained ∧ ∀ t < N, ((permCfg d.ocfg σ.f).ts t).1 = .skip :=
  Silmaril.Proofs.X86.Concurrency.Cir.Robust.symWitness_of_any he hl hbl h

end Silmaril.X86.Concurrency.Cir.Robust

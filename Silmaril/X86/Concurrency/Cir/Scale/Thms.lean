module

public import Silmaril.X86.Concurrency.Cir.Scale.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Sym.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Scale.Checks

/-!
# Mutual exclusion for three and four threads, on CIR's TSO machine

PROVED (standard axioms;
the Boolean checks by kernel `decide`), with the symmetry-reduced explorer
(`Robust.symCheck_sound`). Each statement is about every finished, drained configuration the
CIR-native TSO machine (`Csl.OStep .tso`) reaches from the client's start; the clients are the
translation-validated gcc `spin_lock`/`spin_unlock` and `ticket_lock`/`ticket_unlock` bodies,
inlined with a plain critical section `x = x + 1` (`Scale.Defs`):

* `spin3_mutex`: three spinlock threads, loop bound `2`, end with the counter `3`;
* `spin4_mutex`: four spinlock threads, loop bound `1`, end with the counter `4`;
* `tick3_mutex`: three ticket-lock threads, loop bound `2`, end with the counter `3`;
* `clients_finish`: each of the three clients has a finished, drained reachable configuration
  (so the statements are not vacuous within the bounds);
* `tts3_loses`: the test-then-set mutant with three threads has a finished, drained reachable
  configuration whose counter is not `3` (so the check can fail).

The statements cover the runs within the loop bound: a run that would need one more
spin iteration has no step there.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Scale

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Csl (OCfg OReach)
open Silmaril.Proofs.X86.Concurrency.Cir.Scale

/-- A finished, drained configuration of `N` threads. -/
def Final (N : Nat) (C : OCfg) : Prop := C.Drained ∧ ∀ t < N, (C.ts t).1 = .skip

theorem mem_of_count {n : Nat} {d : CSt} (h : countIs n d = true) : d.ocfg.mem 0x200 = some n := by
  simpa [countIs, CSt.ocfg] using h

/-- **Mutual exclusion under TSO, three spinlock threads.** -/
theorem spin3_mutex {C : OCfg} (hr : OReach .tso 3 (spinN 3 2).cfg.toO C) (hf : Final 3 C) :
    C.mem 0x200 = some 3 :=
  symCheck_mem (Q := fun m => m 0x200 = some 3) (fun _ => mem_of_count) spin3_check hr hf.1 hf.2

/-- **Mutual exclusion under TSO, four spinlock threads.** -/
theorem spin4_mutex {C : OCfg} (hr : OReach .tso 4 (spinN 4 1).cfg.toO C) (hf : Final 4 C) :
    C.mem 0x200 = some 4 :=
  symCheck_mem (Q := fun m => m 0x200 = some 4) (fun _ => mem_of_count) spin4_check hr hf.1 hf.2

/-- **Mutual exclusion under TSO, three ticket-lock threads.** -/
theorem tick3_mutex {C : OCfg} (hr : OReach .tso 3 (tickN 3 2).cfg.toO C) (hf : Final 3 C) :
    C.mem 0x200 = some 3 :=
  symCheck_mem (Q := fun m => m 0x200 = some 3) (fun _ => mem_of_count) tick3_check hr hf.1 hf.2

theorem fin_of_sym {N wf : Nat} {c0 : CSt} {P : CSt → Bool}
    (hs : c0.buf.all List.isEmpty = true ∧ (normAll N tauFuel c0).ts.length = N ∧
      (normAll N tauFuel c0).buf.length = N)
    (h : ((symStates N wf c0).any fun c => c.doneB N && c.drainedB && P c) = true) :
    ∃ C : OCfg, OReach .tso N c0.cfg.toO C ∧ Final N C ∧ ∃ d, P d = true ∧ C.mem = d.ocfg.mem := by
  obtain ⟨d, hP, σ, hr, hd, hfin⟩ := symWitness_of_any hs.1 hs.2.1 hs.2.2 h
  exact ⟨_, hr, ⟨hd, hfin⟩, d, hP, rfl⟩

/-- **The client statements are not vacuous.** -/
theorem clients_finish :
    (∃ C : OCfg, OReach .tso 3 (spinN 3 2).cfg.toO C ∧ Final 3 C) ∧
    (∃ C : OCfg, OReach .tso 4 (spinN 4 1).cfg.toO C ∧ Final 4 C) ∧
    (∃ C : OCfg, OReach .tso 3 (tickN 3 2).cfg.toO C ∧ Final 3 C) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hr, hf, -⟩ := fin_of_sym spin3_shape spin3_fin; exact ⟨C, hr, hf⟩
  · obtain ⟨C, hr, hf, -⟩ := fin_of_sym spin4_shape spin4_fin; exact ⟨C, hr, hf⟩
  · obtain ⟨C, hr, hf, -⟩ := fin_of_sym tick3_shape tick3_fin; exact ⟨C, hr, hf⟩

/-- **The test-then-set mutant loses an increment with three threads.** -/
theorem tts3_loses :
    ∃ C : OCfg, OReach .tso 3 (ttsN 3 2).cfg.toO C ∧ Final 3 C ∧ C.mem 0x200 ≠ some 3 := by
  obtain ⟨C, hr, hf, d, hP, hm⟩ := fin_of_sym tts3_shape tts3_lost
  refine ⟨C, hr, hf, fun h => ?_⟩
  simp only [Bool.not_eq_true'] at hP
  have : countIs 3 d = true := by simpa [countIs, CSt.ocfg, hm] using h
  rw [this] at hP; cases hP

end Silmaril.X86.Concurrency.Cir.Scale

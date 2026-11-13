module

public import Silmaril.X86.Concurrency.Cir.Scale.Defs

/-!
# The symmetry-reduced checks on the `N`-thread clients, by kernel evaluation

One `decide +kernel` per fact.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Scale

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Scale

set_option maxRecDepth 1000000

/-! ## Mutual exclusion (closure checks) -/

theorem spin3_check : symCheck 3 fuel (spinN 3 2) (countIs 3) = true := by decide +kernel
theorem spin4_check : symCheck 4 fuel (spinN 4 1) (countIs 4) = true := by decide +kernel
theorem tick3_check : symCheck 3 fuel (tickN 3 2) (countIs 3) = true := by decide +kernel

/-! ## Non-vacuity

A witness needs only a partial exploration (`Robust.symWitness_of_any` holds for every fuel):
the depth-first search reaches a finished configuration after a few dozen expansions. -/

theorem spin3_fin :
    ((symStates 3 30 (spinN 3 2)).any fun c => c.doneB 3 && c.drainedB && true) = true := by
  decide +kernel
theorem spin4_fin :
    ((symStates 4 150 (spinN 4 1)).any fun c => c.doneB 4 && c.drainedB && true) = true := by
  decide +kernel
theorem tick3_fin :
    ((symStates 3 40 (tickN 3 2)).any fun c => c.doneB 3 && c.drainedB && true) = true := by
  decide +kernel
theorem tts3_lost :
    ((symStates 3 30 (ttsN 3 2)).any fun c => c.doneB 3 && c.drainedB && !countIs 3 c) =
      true := by
  decide +kernel

/-! ## Shapes of the starts -/

theorem spin3_shape : (spinN 3 2).buf.all List.isEmpty = true ∧
    (normAll 3 tauFuel (spinN 3 2)).ts.length = 3 ∧
    (normAll 3 tauFuel (spinN 3 2)).buf.length = 3 := by decide +kernel
theorem spin4_shape : (spinN 4 1).buf.all List.isEmpty = true ∧
    (normAll 4 tauFuel (spinN 4 1)).ts.length = 4 ∧
    (normAll 4 tauFuel (spinN 4 1)).buf.length = 4 := by decide +kernel
theorem tick3_shape : (tickN 3 2).buf.all List.isEmpty = true ∧
    (normAll 3 tauFuel (tickN 3 2)).ts.length = 3 ∧
    (normAll 3 tauFuel (tickN 3 2)).buf.length = 3 := by decide +kernel
theorem tts3_shape : (ttsN 3 2).buf.all List.isEmpty = true ∧
    (normAll 3 tauFuel (ttsN 3 2)).ts.length = 3 ∧
    (normAll 3 tauFuel (ttsN 3 2)).buf.length = 3 := by decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.Scale

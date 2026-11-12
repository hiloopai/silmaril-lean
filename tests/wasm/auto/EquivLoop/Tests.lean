module

public import Silmaril.Wasm.Auto.EquivLoop.Thms
public import tests.wasm.auto.Equiv.CtlTests

/-!
# Loop equivalence: tests

The loop of `Silmaril.Wasm.Auto.Equiv.Tests` (`do { x := x + 1 + 1 } while (x < 10)` against
`do { x := x + 2 } while (10 > x)`), now in both readings of the every-run logic.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivLoop.Tests

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv (segEquiv_of_check)
open Silmaril.Wasm.Auto.Equiv

/-- **Under `loop`, total correctness included.** -/
theorem loop_cequiv : CEquiv [.i32] [.i64] [.loop .empty (CtlTests.bodyA ++ [.brIf ⟨0⟩])]
    [.loop .empty (CtlTests.bodyB ++ [.brIf ⟨0⟩])] :=
  CEquiv.loopT noParams_empty
    (CEquiv.append (SegEquiv.cequiv (segEquiv_of_check (by decide))) _)
    (KeepsBr0.of_check ⟨0⟩ (by decide))

/-- info: 'Silmaril.Wasm.Auto.EquivLoop.Tests.loop_cequiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_cequiv

end Silmaril.Wasm.Auto.EquivLoop.Tests

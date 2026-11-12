module

public import Silmaril.X86.Bir9.X.Defs
import Silmaril.Raw.X86.Bir9.X.Sound

/-! # Bir9X: the block simulation theorem

PROVED (standard axioms; proof in `Silmaril.Raw.X86.Bir9.X.Sound`):

* **`liftBlockX_sound`**: `liftBlockX L = some b` (closed by `decide +kernel`) gives
  `execBlockX L s mem = b.run s mem` for every state and memory;
* `symExecX_sound`: the same before simplification.

Per form (in the proof module): the `Ext8` ALU/TEST forms agree with Bir9's `XInstr.alu8` /
`XInstr.test8` on low-byte and memory operands (`execNew_alu_eq`, …), `op r8, r/m8`
(`sAluR8_sound`), the byte shifts by a constant (`sShift8_sound`), ADC/SBB (`sCarry_sound`).
-/

@[expose] public section

namespace Silmaril.X86.Bir9X

open Silmaril.X86.Bir9 (Block XState)
open Silmaril.Process (Memory)

theorem symExecX_sound {instrs : List (XL × Nat)} {b : Block} (h : symExecX instrs = some b)
    (s : XState) (mem : Memory) : execBlockX instrs s mem = b.run s mem :=
  Silmaril.Raw.X86.Bir9X.symExecX_sound h s mem

/-- **The extended lifter's certificate.** A listing whose lift the kernel computes to `b`
runs as `b` on every entry state and memory. -/
theorem liftBlockX_sound {instrs : List (XL × Nat)} {b : Block} (h : liftBlockX instrs = some b)
    (s : XState) (mem : Memory) : execBlockX instrs s mem = b.run s mem :=
  Silmaril.Raw.X86.Bir9X.liftBlockX_sound h s mem

end Silmaril.X86.Bir9X

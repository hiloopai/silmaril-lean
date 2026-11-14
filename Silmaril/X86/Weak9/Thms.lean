module

public import Silmaril.X86.Weak9.Defs
public import Silmaril.X86.Atomic9.Thms
public import Silmaril.X86.Str9.Thms
import Silmaril.Proofs.X86.Weak9.Step

/-!
# `Weak9`: what is proved

PROVED (standard axioms; proofs in `Silmaril/Proofs/X86/Weak9/Step.lean`):

* `step_of_atomic9`: **conservative extension** — every `Atomic9.step` is a `Weak9.step`, so
  every `Atomic9` (hence `Open9`) result carries over.
* `step_of_listed`: **the listing law** — an instruction that `decode` reads on exactly its
  own slice of loaded code at the program counter, and that `exec` runs, is one step. This
  covers the `Atomic9` listings, the `Weak` forms (`movnti`, `rep stosb`) and `Str9`'s forms.
* `decodeWeak_append`: a decoded `Weak` form keeps its reading whatever bytes follow.

Decoder facts (`decide`, on the encodings of the litmus corpus, GNU as 2.42):
`decode_movnti32`, `decode_movnti64`, `decode_repStosb`, `decode_repStosq`, and the regression
`decode_movnti_reg_none` (the register form of `movnti` is rejected).

Not claimed: that the forms' semantics matches hardware (handwritten from the SDM).
-/

@[expose] public section

namespace Silmaril.X86.Weak9

open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)

/-- **Every `Atomic9` step is a `Weak9` step.** -/
theorem step_of_atomic9 {m m' : MState} (h : Atomic9.step m = some m') : step m = some m' :=
  Silmaril.Proofs.X86.Weak9.step_of_atomic9 h

/-- **The listing law of `Weak9`.** -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Weak9.step_of_listed hl hrip hfit hdec hx

/-- A decoded `Weak` form keeps its reading whatever bytes follow. -/
theorem decodeWeak_append {bytes : List Byte} {i : Weak} {n : Nat}
    (h : decodeWeak bytes = some (i, n)) (more : List Byte) :
    decodeWeak (bytes ++ more) = some (i, n) :=
  Silmaril.Proofs.X86.Weak9.decodeWeak_append h more

/-- The absolute memory operand `[disp32]`. -/
def absMem (d : BitVec 32) : Silmaril.X86.Ext.Mem := ⟨.none, none, d, by simp⟩

/-- `movnti dword ptr [0x10000], eax` (`0f c3 04 25 00 00 01 00`). -/
theorem decode_movnti32 :
    decode [0x0f, 0xc3, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00] =
      some (.weak (.movnti .d (absMem 0x10000) .rax), 8) := by decide

/-- `movnti qword ptr [0x10000], rax` (`48 0f c3 04 25 00 00 01 00`). -/
theorem decode_movnti64 :
    decode [0x48, 0x0f, 0xc3, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00] =
      some (.weak (.movnti .q (absMem 0x10000) .rax), 9) := by decide

/-- `rep stosb` (`f3 aa`). -/
theorem decode_repStosb : decode [0xf3, 0xaa] = some (.weak .repStosb, 2) := by decide

/-- `rep stosq` (`f3 48 ab`), `Str9`'s form. -/
theorem decode_repStosq : decode [0xf3, 0x48, 0xab] = some (.str .repStosq, 3) := by decide

/-- The register form `movnti eax, eax` (`0f c3 c0`) is rejected (`#UD`). -/
theorem decode_movnti_reg_none : decode [0x0f, 0xc3, 0xc0] = none := by decide

end Silmaril.X86.Weak9

module

public import Silmaril.X86.Ext9.Defs
import Silmaril.Proofs.X86.Ext9.Decode
import Silmaril.Proofs.X86.Ext9.Step
import Silmaril.Proofs.X86.Ext9.Semantics

/-!
# `Ext9`: conservativity over `Ext8`

Every `Ext8` (hence every `X86.Ext`) decode, execution, step and returning run is unchanged
in the variant, so every proof about `Ext8` or `Ext` transfers:

* `decode_of_ext8`, `decode_ext8_iff`, `decode_new_iff`: the decoder;
* `exec_ext8`: execution (`rfl`);
* `step_eq_of_ne_undecodable`, `stepOpt_of_ext8`, `run_of_ext8`: the machine step;
* `returns_of_ext8`, `returns_of_ext`: returning runs.

And the new forms' decoder has the prefix laws: `good_pNew`, `decodeNew_append`,
`decodeNew_le`. Semantics: `bsrIndex_eq_log2` (BSR on a nonzero source is `⌊log2⌋`).

The decoding and semantic vectors at the end are kernel-checked (`decide`).
-/

@[expose] public section

namespace Silmaril.X86.Ext9

open Silmaril.X86 (Byte Word MState State)
open Silmaril.Process (Memory)

/-- **Decoder agreement**: wherever `Ext8` decodes, so does the variant. -/
theorem decode_of_ext8 {bytes : List Byte} {i : Silmaril.X86.Ext8.Instr} {n : Nat}
    (h : Silmaril.X86.Ext8.decode bytes = some (i, n)) : decode bytes = some (.ext8 i, n) :=
  Silmaril.Proofs.X86.Ext9.decode_of_ext8 h

/-- Wherever `X86.Ext` decodes, so does the variant. -/
theorem decode_of_ext {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (h : Silmaril.X86.Ext.decode bytes = some (i, n)) : decode bytes = some (.ext8 (.base i), n) :=
  decode_of_ext8 (Silmaril.X86.Ext8.decode_of_ext h)

theorem decode_ext8_iff {bytes : List Byte} {i : Silmaril.X86.Ext8.Instr} {n : Nat} :
    decode bytes = some (.ext8 i, n) ↔ Silmaril.X86.Ext8.decode bytes = some (i, n) :=
  Silmaril.Proofs.X86.Ext9.decode_ext8_iff

theorem decode_new_iff {bytes : List Byte} {i : New} {n : Nat} :
    decode bytes = some (.new i, n) ↔
      Silmaril.X86.Ext8.decode bytes = none ∧ decodeNew bytes = some (i, n) :=
  Silmaril.Proofs.X86.Ext9.decode_new_iff

/-- **Execution agreement**: on `Ext8` instructions the variant is `Ext8.exec`. -/
@[simp] theorem exec_ext8 (i : Silmaril.X86.Ext8.Instr) (s : State) (memory : Memory)
    (length : Nat) : exec (.ext8 i) s memory length = Silmaril.X86.Ext8.exec i s memory length :=
  rfl

theorem good_pNew : Silmaril.X86.Ext.ByteParser.Good pNew :=
  Silmaril.Proofs.X86.Ext9.good_pNew

theorem decodeNew_append {bytes : List Byte} {i : New} {n : Nat}
    (h : decodeNew bytes = some (i, n)) (more : List Byte) :
    decodeNew (bytes ++ more) = some (i, n) :=
  Silmaril.Proofs.X86.Ext9.decodeNew_append h more

theorem decodeNew_le {bytes : List Byte} {i : New} {n : Nat}
    (h : decodeNew bytes = some (i, n)) : n ≤ bytes.length :=
  Silmaril.Proofs.X86.Ext9.decodeNew_le h

/-- **Step agreement**: whenever `Ext8.step` does anything but report undecodable bytes,
the variant's step is that outcome. -/
theorem step_eq_of_ne_undecodable {exit : Word} {m : MState}
    (h : Silmaril.X86.Ext8.step exit m ≠ .ext .undecodable) :
    step exit m = .ext8 (Silmaril.X86.Ext8.step exit m) :=
  Silmaril.Proofs.X86.Ext9.step_eq_of_ne_undecodable h

theorem stepOpt_of_ext8 {exit : Word} {m next : MState}
    (h : Silmaril.X86.Ext8.stepOpt exit m = some next) : stepOpt exit m = some next :=
  Silmaril.Proofs.X86.Ext9.stepOpt_of_ext8 h

theorem run_of_ext8 {exit : Word} (n : Nat) {initial mid : MState}
    (h : Silmaril.Machine.Execution.run (Silmaril.X86.Ext8.stepOpt exit) n initial = some mid) :
    Silmaril.Machine.Execution.run (stepOpt exit) n initial = some mid :=
  Silmaril.Proofs.X86.Ext9.run_of_ext8 n h

/-- **Run agreement**: every `Ext8.Returns` run is an `Ext9.Returns` run. -/
theorem returns_of_ext8 {exit : Word} {initial final : MState}
    (h : Silmaril.X86.Ext8.Returns exit initial final) : Returns exit initial final :=
  Silmaril.Proofs.X86.Ext9.returns_of_ext8 h

/-- Every `X86.Ext.Returns` run is an `Ext9.Returns` run. -/
theorem returns_of_ext {exit : Word} {initial final : MState}
    (h : Silmaril.X86.Ext.Returns exit initial final) : Returns exit initial final :=
  returns_of_ext8 (Silmaril.X86.Ext8.returns_of_ext h)

/-- On a nonzero source the BSR index is `⌊log2⌋` of the source. -/
theorem bsrIndex_eq_log2 {n : Nat} (x : BitVec n) (hx : x ≠ 0#n) :
    bsrIndex x = Nat.log2 x.toNat :=
  Silmaril.Proofs.X86.Ext9.bsrIndex_eq_log2 x hx

/-! ## Decoding vectors (bytes emitted by gcc 13.3 at `-O2`) -/

/-- `imul $0x1010101,%eax,%eax` (a `popcount32`). -/
example : decode [0x69, 0xc0, 0x01, 0x01, 0x01, 0x01] =
    some (.new (.imulI .d .rax (.reg .rax) 0x01010101), 6) := by decide
/-- `bsr %edi,%eax` (an `ilog2_u32`). -/
example : decode [0x0f, 0xbd, 0xc7] = some (.new (.bsr .d .rax (.reg .rdi)), 3) := by decide
/-- `call *%r13`. -/
example : decode [0x41, 0xff, 0xd5] = some (.new (.callInd (.reg .r13)), 3) := by decide
/-- `push $0x70`. -/
example : decode [0x6a, 0x70] = some (.new (.pushI 0x70), 2) := by decide
/-- `test %dx,%dx`. -/
example : decode [0x66, 0x85, 0xd2] = some (.new (.test16 (.reg .rdx) .rdx), 3) := by decide
/-- `sbb %eax,%eax`. -/
example : decode [0x19, 0xc0] = some (.new (.adc .d true (.reg .rax) .rax), 2) := by decide
/-- `test r12d, 0xfffffffb` (`F7 /0 id`; `Ext`'s length decoder counts no immediate here). -/
example : decode [0x41, 0xf7, 0xc4, 0xfb, 0xff, 0xff, 0xff] =
    some (.new (.testI .d (.reg .r12) 0xfffffffb), 7) := by decide
/-- `test ah, 1` (`F6 /0 ib` on a legacy high byte, which `Ext` does not model). -/
example : decode [0xf6, 0xc4, 0x01] = some (.new (.testI8 (.reg (.high .rax)) 0x01), 3) := by
  decide
/-- `bt rdx, rax`. -/
example : decode [0x48, 0x0f, 0xa3, 0xc2] = some (.new (.bt .q .rdx .rax), 4) := by decide
/-- `cmp word [rsp+0x4e8], 0`. -/
example : decode [0x66, 0x83, 0xbc, 0x24, 0xe8, 0x04, 0x00, 0x00, 0x00] =
    some (.new (.alu16I .cmp (.mem (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x4e8)) 0), 9) := by
  decide
/-- `tzcnt`/`lzcnt` (`F3 0F BC/BD`) stay `Ext` forms; REX.W on a 16-bit form is rejected;
`F2` is rejected. -/
example : (decode [0xf3, 0x0f, 0xbd, 0xc7]).map (·.2) = some 4 ∧
    decode [0x66, 0x48, 0x83, 0x04, 0x4a, 0x01] = none ∧
    decode [0xf2, 0x0f, 0xbd, 0xc7] = none := by decide

/-- `rep ret` (`F3 C3`), and `notrack jmp *%rax` (`3E FF E0`). -/
example : decode [0xf3, 0xc3] = some (.new .repRet, 2) ∧
    decode [0x3e, 0xff, 0xe0] = some (.new (.jmpInd (.reg .rax)), 3) := by decide
/-- `notrack call` (`3E FF /2`) and `F3` before an opcode other than `C3` are rejected. -/
example : decode [0x3e, 0xff, 0xd0] = none ∧ decode [0xf3, 0x69, 0xc0, 1, 0, 0, 0] = none := by
  decide

/-! ## Semantic vectors -/

/-- BSR and BSF of `0x10000` are both 16. -/
example : bsrIndex (0x00010000#32) = 16 ∧ bsfIndex (0x00010000#32) = 16 := by decide
/-- `adc` of `0xffffffff + 0 + CF=1` wraps to `0` and sets CF and ZF, not OF. -/
example : carryResult false (0xffffffff#32) 0 true = 0 ∧
    carryFlags false (0xffffffff#32) 0 true =
      ⟨some true, some true, some true, some true, some false, some false⟩ := by decide
/-- `sbb %eax,%eax` with CF = 1 is `-1` (all ones) and sets CF. -/
example : carryResult true (0x5#32) 0x5 true = 0xffffffff ∧
    (carryFlags true (0x5#32) 0x5 true).carry = some true := by decide
/-- One-operand `imul`: `-1 * 2 = -2`, whose high half is the sign extension (CF = OF = 0). -/
example : imulWide (0xffffffff#32) 2 = (0xfffffffe, 0xffffffff) ∧
    (imul1Flags (0xffffffff#32) 2).carry = some false := by decide
/-- One-operand `imul`: `0x10000 * 0x10000` overflows 32 bits (CF = OF = 1). -/
example : imulWide (0x00010000#32) 0x00010000 = (0, 1) ∧
    (imul1Flags (0x00010000#32) 0x00010000).overflow = some true := by decide

end Silmaril.X86.Ext9

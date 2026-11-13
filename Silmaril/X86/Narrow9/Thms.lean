module

public import Silmaril.Raw.X86.Narrow9

/-!
# `Narrow9`: decoder laws and kernel-checked vectors

* `good_pNew`, `pNew_bad_append`, `decodeNew_append`, `decodeNew_le`: the parser's prefix
  laws (proofs in `Silmaril.Raw.X86.Narrow9`, re-exported here).
* Decoding vectors: the six encodings of the gzip API binaries that need `Narrow9`
  (`shr r16, imm8` on `ax`, `bp`, `r12w`, `shr m16, imm8` at `[rax+0x1730]` and
  `[rdi+0x1730]`, `sbb cl, 0xff`) and the rejections.
* Semantic vectors: 16-bit shifts keep bits 63:16, counts are masked to five bits, a zero
  count changes nothing, `sbb cl, 0xff` with CF set is `cl - 0`.
-/

@[expose] public section

namespace Silmaril.X86.Narrow9

open Silmaril.X86 (State Flags)
open Silmaril.X86.Ext (Result)
open Silmaril.Process (Memory)

/-! ## Decoding vectors -/

/-- `shr ax, 0xf` (`__signbitl`). -/
example : decodeNew [0x66, 0xC1, 0xE8, 0x0F] = some (.shift16 .shr (.reg .rax) (.imm 0x0F), 4) := by
  decide

/-- `shr bp, 7` (`deflate_fast`). -/
example : decodeNew [0x66, 0xC1, 0xED, 0x07] = some (.shift16 .shr (.reg .rbp) (.imm 7), 4) := by
  decide

/-- `shr r12w, 7` (`deflate_slow`). -/
example : decodeNew [0x66, 0x41, 0xC1, 0xEC, 0x07] =
    some (.shift16 .shr (.reg .r12) (.imm 7), 5) := by decide

/-- `shr word [rax+0x1730], 8` and `shr word [rdi+0x1730], 8` (`_tr_align`,
`_tr_flush_bits`): eight bytes each. -/
example : (decodeNew [0x66, 0xC1, 0xA8, 0x30, 0x17, 0x00, 0x00, 0x08]).map (·.2) = some 8 ∧
    (decodeNew [0x66, 0xC1, 0xAF, 0x30, 0x17, 0x00, 0x00, 0x08]).map (·.2) = some 8 := by decide

/-- `sbb cl, 0xff` (`deflate`). -/
example : decodeNew [0x80, 0xD9, 0xFF] = some (.adc8I true (.reg (.low .rcx)) 0xFF, 3) := by decide

/-- `rol ah, 1`, `ror sil, cl`, `adc al, 1`, `sbb ax, 0x1234`, `adc word [rbx], 1`. -/
example : decodeNew [0xD0, 0xC4] = some (.rot8 .rol (.reg (.high .rax)) .one, 2) ∧
    decodeNew [0x40, 0xD2, 0xCE] = some (.rot8 .ror (.reg (.low .rsi)) .cl, 3) ∧
    decodeNew [0x14, 0x01] = some (.adc8A false 1, 2) ∧
    decodeNew [0x66, 0x1D, 0x34, 0x12] = some (.adc16A true 0x1234, 4) ∧
    (decodeNew [0x66, 0x83, 0x13, 0x01]).map (·.2) = some 4 := by decide

/-- Rejected: REX.W (`66 48 C1 E8 07`), `F3`/`F2`, the FS override, `66` on an 8-bit form,
`rcl`/`rcr` (`/2`, `/3`), the `/6` alias of `shl`, a REX on `adc al, imm8`, and the 8-bit
shifts and 16-bit ALU forms that `Ext8` and `Ext9` already read. -/
example : decodeNew [0x66, 0x48, 0xC1, 0xE8, 0x07] = none ∧
    decodeNew [0xF3, 0x66, 0xC1, 0xE8, 0x07] = none ∧ decodeNew [0xF2, 0x80, 0xD9, 0xFF] = none ∧
    decodeNew [0x64, 0x80, 0x18, 0x01] = none ∧ decodeNew [0x66, 0x80, 0xD9, 0xFF] = none ∧
    decodeNew [0x66, 0xC1, 0xD0, 0x01] = none ∧ decodeNew [0xC0, 0xD8, 0x01] = none ∧
    decodeNew [0x66, 0xC1, 0xF0, 0x01] = none ∧ decodeNew [0x40, 0x14, 0x01] = none ∧
    decodeNew [0xC0, 0xE8, 0x01] = none ∧ decodeNew [0x66, 0x01, 0xC0] = none := by decide

/-! ## Semantic vectors -/

/-- A core with `rax = 0x1111_2222_3333_8001`, `rcx = 0x7f`, the given carry, RIP `0x1000`. -/
private def vcore (cf : Option Bool) : State :=
  ((({ regs := fun _ => 0, rip := 0x1000, flags := ⟨cf, none, none, none, none, none⟩ } :
    State).write .rax 0x1111222233338001).write .rcx 0x7f)

private def noMem : Memory := ⟨[], ∅⟩

/-- `shr ax, 0xf` keeps bits 63:16 and leaves `1`; CF is bit 14, OF undefined. -/
example : (match execNew (.shift16 .shr (.reg .rax) (.imm 0x0F)) (vcore none) noMem 0x1004 with
    | .ok c _ => c.read .rax == 0x1111222233330001 && c.rip == 0x1004 &&
        c.flags.carry == some false && c.flags.overflow == none && c.flags.zero == some false
    | _ => false) = true := by decide

/-- The count is masked to five bits: `shr ax, 0x21` is `shr ax, 1`, with OF the old top bit. -/
example : (match execNew (.shift16 .shr (.reg .rax) (.imm 0x21)) (vcore none) noMem 0x1004 with
    | .ok c _ => c.read .rax == 0x1111222233334000 && c.flags.carry == some true &&
        c.flags.overflow == some true
    | _ => false) = true := by decide

/-- `shl ax, 16` clears the word, leaves CF undefined, and keeps bits 63:16. -/
example : (match execNew (.shift16 .shl (.reg .rax) (.imm 16)) (vcore none) noMem 0x1004 with
    | .ok c _ => c.read .rax == 0x1111222233330000 && c.flags.carry == none &&
        c.flags.zero == some true
    | _ => false) = true := by decide

/-- A masked count of zero (`shr ax, 0x20`) only moves RIP. -/
example : (match execNew (.shift16 .shr (.reg .rax) (.imm 0x20)) (vcore none) noMem 0x1004 with
    | .ok c _ => c.read .rax == 0x1111222233338001 && c.rip == 0x1004 &&
        c.flags.carry == none && c.flags.zero == none
    | _ => false) = true := by decide

/-- `sbb cl, 0xff` with CF set: `0x7f - 0xff - 1 = 0x7f`, a borrow. With CF undefined the step
does not retire. -/
example : (match execNew (.adc8I true (.reg (.low .rcx)) 0xFF) (vcore (some true)) noMem 0x1003 with
    | .ok c _ => c.read .rcx == 0x7f && c.flags.carry == some true
    | _ => false) = true ∧
    (match execNew (.adc8I true (.reg (.low .rcx)) 0xFF) (vcore none) noMem 0x1003 with
    | .undefinedCondition _ => true
    | _ => false) = true := by decide

/-- A memory operand with no memory mapped faults. -/
example : (match decodeNew [0x66, 0xC1, 0x28, 0x08] with
    | some (i, _) => match execNew i (vcore none) noMem 0x1004 with
      | .dataFault => true
      | _ => false
    | none => false) = true := by decide

end Silmaril.X86.Narrow9

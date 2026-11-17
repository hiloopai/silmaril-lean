module

public import Silmaril.Machine.Abi.Conformance.Zlib.Api.Defs

/-! # The rest of zlib's checksum API: sanity theorems

Kernel computations that the specs mean what they say:

* `combine_example`: for one-byte strings the operator `x^8` (bit-reflected: `0x00800000`)
  combines `crc32(0, "a")` and `crc32(0, "b")` into `crc32(0, "ab")`, so `crc32CombineGenS`'s
  condition is met by zlib's operator, not vacuous;
* `multmodp_one`: `0x80000000` (the polynomial `1`, reflected) is `multmodp`'s identity on an
  example;
* `crcTableBytes_length`, `crcTable_first`: 1024 bytes, beginning with entries 0 and 1
  (`0x00000000`, `0x77073096`);
* `flagsLow_lp64`, `flagsLow_ilp32`, `flagsLowOff_ilp32_lfs`: `zlibCompileFlags`' low byte is
  `0xa9` under the x86-64 System V data model, `0x55` under i386's with `z_off_t` = `long`, and
  `0x95` under i386's with a large-file 8-byte `z_off_t`: the spec follows the data model and its
  `z_off_t` assumption;
* `op_pre_zero_low`, `op_pre_gen_one`, `op_pre_iff`: **the `crc32_combine_op` domain**: an
  operator whose low 32 bits are 0 (`0`, `0x100000000`) is outside the precondition (zlib's
  `multmodp` does not return on it); the operator `crc32_combine_gen(1)` returns (`0x00800000`)
  and the identity `0x80000000` are inside, so the precondition is satisfiable.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Zlib.Api

open Silmaril.X86.Ladder.ZlibChecksums (crc32 crcEntry)

theorem combine_example :
    multmodp 0x00800000#32 (crc32 0 [0x61]) ^^^ crc32 0 [0x62] = crc32 0 [0x61, 0x62] := by
  decide +kernel

theorem multmodp_one : multmodp 0x80000000#32 0x12345678#32 = 0x12345678#32 := by decide +kernel

theorem crcTableBytes_length : crcTableBytes.length = 1024 := by decide +kernel

theorem crcTable_first : crcTableBytes.take 8 = [0x00, 0x00, 0x00, 0x00, 0x96, 0x30, 0x07, 0x77] := by
  decide +kernel

theorem flagsLow_lp64 : flagsLow Silmaril.Data.Layout.sysvX86_64 = 0xa9 := by decide +kernel

/-- i386 with `z_off_t` = `long` (4 bytes). -/
theorem flagsLow_ilp32 : flagsLow Silmaril.Data.Layout.i386Ilp32 = 0x55 := by decide +kernel

/-- i386 with a large-file `z_off_t` (an 8-byte `off_t`). -/
theorem flagsLowOff_ilp32_lfs : flagsLowOff Silmaril.Data.Layout.i386Ilp32 (some ⟨8, 4⟩) = 0x95 := by
  decide +kernel

/-- An operator whose low 32 bits are 0 is outside `crc32_combine_op`'s precondition, for any
other arguments and memory: `0` and `0x100000000` among them. -/
theorem op_pre_zero_low (c1 c2 o : Silmaril.X86.Word) (mem : Silmaril.Process.Memory)
    (h : lo32 o = 0) : ¬ crc32CombineOpS.pre (.cons c1 (.cons c2 (.cons o .nil))) mem :=
  fun hp => hp h

theorem op_pre_examples (c1 c2 : Silmaril.X86.Word) (mem : Silmaril.Process.Memory) :
    ¬ crc32CombineOpS.pre (.cons c1 (.cons c2 (.cons (0 : Silmaril.X86.Word) .nil))) mem ∧
    ¬ crc32CombineOpS.pre (.cons c1 (.cons c2 (.cons (0x100000000 : Silmaril.X86.Word) .nil))) mem :=
  ⟨op_pre_zero_low _ _ _ _ (by decide), op_pre_zero_low _ _ _ _ (by decide)⟩

/-- The precondition is satisfiable: `crc32_combine_gen(1)`'s operator `0x00800000` and the
identity `0x80000000` are admitted. -/
theorem op_pre_gen_one (c1 c2 : Silmaril.X86.Word) (mem : Silmaril.Process.Memory) :
    crc32CombineOpS.pre (.cons c1 (.cons c2 (.cons (0x00800000 : Silmaril.X86.Word) .nil))) mem ∧
    crc32CombineOpS.pre (.cons c1 (.cons c2 (.cons (0x80000000 : Silmaril.X86.Word) .nil))) mem :=
  ⟨show lo32 (0x00800000 : Silmaril.X86.Word) ≠ 0 by decide,
    show lo32 (0x80000000 : Silmaril.X86.Word) ≠ 0 by decide⟩

theorem op_pre_iff (a : Silmaril.Machine.Abi.Conformance.sysvInt.V.Args opProto)
    (mem : Silmaril.Process.Memory) : crc32CombineOpS.pre a mem ↔ lo32 (opOp a) ≠ 0 := Iff.rfl

end Silmaril.Machine.Abi.Conformance.Zlib.Api

end

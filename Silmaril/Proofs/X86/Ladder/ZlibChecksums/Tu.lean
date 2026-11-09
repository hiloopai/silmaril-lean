module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Crc32z
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Wrapper

/-!
# The rung-03 checksum TU: wrappers and witnesses
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86 Silmaril.X86.BlockCert8
open Silmaril.X86.Stencils.ByteLoop (arg1 arg2)
open Silmaril.X86.Ladder.ZlibChecksums

theorem after_arg1 (rel : BitVec 32) (m : MState) : arg1 (after rel m) = arg1 m := by
  simp only [arg1, after_read rel m (r := .rsi) (by decide)]

theorem after_arg2 (rel : BitVec 32) (m : MState) : arg2 (after rel m) = arg2 m % 2 ^ 32 := by
  have h : (after rel m).core.read .rdx = ((m.core.read .rdx).setWidth 32).setWidth 64 :=
    Silmaril.X86.State.read_write_same m.core .rdx _
  unfold arg2
  rw [h, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  omega

theorem crc32Wrap_listing : listing8 crc32WrapCode 0 (wrapL 0xfffffec9#32) = true := by decide +kernel

theorem adler32Wrap_listing : listing8 adler32WrapCode 0 (wrapL 0xfffffb89#32) = true := by
  decide +kernel

theorem crc32_target (entry : Word) :
    entry + 7#64 + (0xfffffec9#32 : BitVec 32).signExtend 64 = entry - 0x130#64 := by
  have : (0xfffffec9#32 : BitVec 32).signExtend 64 = 0xfffffffffffffec9#64 := by decide +kernel
  have h2 : (7#64 + 0xfffffffffffffec9#64 : BitVec 64) = -0x130#64 := by decide +kernel
  rw [this, BitVec.add_assoc, h2, BitVec.sub_eq_add_neg]

theorem adler32_target (entry : Word) :
    entry + 7#64 + (0xfffffb89#32 : BitVec 32).signExtend 64 = entry - 0x470#64 := by
  have : (0xfffffb89#32 : BitVec 32).signExtend 64 = 0xfffffffffffffb89#64 := by decide +kernel
  have h2 : (7#64 + 0xfffffffffffffb89#64 : BitVec 64) = -0x470#64 := by decide +kernel
  rw [this, BitVec.add_assoc, h2, BitVec.sub_eq_add_neg]

/-- **`crc32` is totally correct** (from `crc32z_total` through the tail call). -/
theorem crc32_total (entry : Word) : (crc32Contract entry).Total Open.isa := by
  refine wrap_total crc32Wrap_listing (crc32zContract (entry - 0x130#64)) _
    (crc32z_total _) (fun m he => ⟨by rw [he.1]; exact he.2.1, ?_⟩) (fun _ _ _ h => h)
    (fun m t he h => ?_)
  · refine ⟨?_, he.2.2.1, he.2.2.2.1, ?_⟩
    · show m.core.rip + 7#64 + _ = _; rw [he.1, crc32_target]
    · rw [after_arg1, after_arg2]; exact he.2.2.2.2
  · show t.core.read .rax = _
    rw [h, after_arg1, Ladder.ZlibChecksums.buf, after_arg1, after_arg2,
      after_read _ m (r := .rdi) (by decide)]
    rfl

/-- **`adler32` is totally correct on `Open9` if `adler32_z` is.** -/
theorem adler32_total9_of (h : ∀ entry, (adler32zContract entry).Total Open9.isa) (entry : Word) :
    (adler32Contract entry).Total Open9.isa := by
  refine wrap_total9 adler32Wrap_listing (adler32zContract (entry - 0x470#64)) _
    (h _) (fun m he => ⟨by rw [he.1]; exact he.2.1, ?_⟩) (fun m a he ha => ?_)
    (fun m t he h' => ?_)
  · refine ⟨?_, he.2.2.1, ?_⟩
    · show m.core.rip + 7#64 + _ = _; rw [he.1, adler32_target]
    · rw [show ((after 0xfffffb89#32 m).core.read .rsp) = m.core.read .rsp from
        after_read _ m (by decide), after_arg1, after_arg2]
      refine ⟨he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.1, ?_⟩
      have hok := he.2.2.2.2.2.2.2.2
      simp only [AdlerOk, after_read _ m (r := .rdi) (by decide), after_arg1] at hok ⊢
      exact hok
  · simp only [adler32zContract, adlerFrame] at ha
    rw [after_read _ m (r := .rsp) (by decide)] at ha
    exact ha
  · show t.core.read .rax = _
    rw [h', after_arg1, Ladder.ZlibChecksums.buf, after_arg1, after_arg2,
      after_read _ m (r := .rdi) (by decide)]
    rfl

/-- `adler32_z`'s first `imul $0xfff1, %rdx, %rax` (offset `0x183`) is not decoded. -/
theorem adler32z_imul_undecoded : Open.decode ((adler32zCode.drop 0x183).take 7) = none := by
  decide +kernel

end Silmaril.Proofs.X86.Ladder.ZlibChecksums

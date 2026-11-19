module

public import Silmaril.X86.Sep.Plan.Defs
public import Silmaril.X86.Features.State
public import Silmaril.Machine.SystemV.Abi.Ffi.Thms

/-!
# Bit-level facts for `Mach.str9L`

The splits `Conformance.Sse.Defs` needs to rebuild an FFI vector or x87 field from the tower's
registers and the hidden parts (`vec_split`, `x87_split`), the register numbering of
`Sep.Plan.xregOfIdx`, and the eight-byte read-back of a vector register (`bytes8_inj`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.Sse

open Silmaril.X86 (XReg)
open Silmaril.X86.Sep.Plan (xregOfIdx)
open Silmaril.Machine.SystemV.Abi

theorem xregOfIdx_toNat {i : Nat} (h : i < 16) : (xregOfIdx i).toBitVec.toNat = i := by
  simp only [xregOfIdx, XReg.toBitVec_ofBitVec, BitVec.toNat_ofNat]
  omega

theorem xregOfIdx_toBitVec (r : XReg) : xregOfIdx r.toBitVec.toNat = r := by cases r <;> rfl

/-- A 512-bit register is its bits 511:256 over 255:128 over 127:0. -/
theorem split512 (x : BitVec 512) :
    (x.extractLsb' 256 256 ++ (x.extractLsb' 128 128 ++ x.setWidth 128) : BitVec 512) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h1 : j < 128
  · simp [h1, show j < 256 by omega]
  · by_cases h2 : j < 256
    · simp only [h2, ite_true, h1, ite_false, BitVec.getLsbD_extractLsb',
        show j - 128 < 128 by omega, decide_true, Bool.true_and]
      rw [show 128 + (j - 128) = j by omega]
    · simp only [h2, ite_false, BitVec.getLsbD_extractLsb', show j - 256 < 256 by omega,
        decide_true, Bool.true_and]
      rw [show 256 + (j - 256) = j by omega]

/-- The vector field rebuilt from the low 128 bits (`Sep.Plan.ffiXState`), bits 255:128 and the
rest. -/
theorem vec_split (v : Nat → BitVec 512) (i : Nat) :
    (if i < 16 then ((v i).extractLsb' 256 256 ++
        ((v (xregOfIdx i).toBitVec.toNat).extractLsb' 128 128 ++
          (v (xregOfIdx i).toBitVec.toNat).setWidth 128) : BitVec 512) else v i) = v i := by
  split
  · rename_i h; rw [xregOfIdx_toNat h]; exact split512 _
  · rfl

/-- The x87 field rebuilt from a register file with TOP = 0 (ST(i) is register `i`) and the
rest. -/
theorem x87_split (g : Nat → BitVec 80) (c : BitVec 16) (i : Nat) :
    (if h : i < 8 then
        (⟨fun j => g j.val, 0, c, 0⟩ : Silmaril.X86.Features.X87).st ⟨i, h⟩ else g i) = g i := by
  split
  · rename_i h
    simp only [Silmaril.X86.Features.X87.st, Silmaril.X86.Features.X87.phys,
      Silmaril.X86.Features.X87.top]
    congr 1
    simp only [show (0 : BitVec 16).extractLsb' 11 3 = 0 from rfl]
    simp [Nat.mod_eq_of_lt h]
  · rfl

/-- Eight little-endian bytes determine a 64-bit word. -/
theorem bytes8_inj {x y : BitVec 64}
    (h : Ffi.bytesOfNat x.toNat 0 8 = Ffi.bytesOfNat y.toNat 0 8) : x = y := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [Ffi.bytesOfNat, List.range_succ, List.range_zero, List.nil_append,
     List.map_cons, List.map_nil, List.cons_append,
    List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [UInt8.ofNat, UInt8.ofBitVec.injEq] at h0 h1 h2 h3 h4 h5 h6 h7
  have t := fun {a b : Nat} (e : BitVec.ofNat 8 a = BitVec.ofNat 8 b) =>
    congrArg BitVec.toNat e
  have e0 := t h0; have e1 := t h1; have e2 := t h2; have e3 := t h3
  have e4 := t h4; have e5 := t h5; have e6 := t h6; have e7 := t h7
  simp only [BitVec.toNat_ofNat] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [Nat.zero_add, Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one]
    at e0 e1 e2 e3 e4 e5 e6 e7
  apply BitVec.eq_of_toNat_eq
  omega

end Silmaril.Proofs.Machine.Abi.Conformance.Sse

end

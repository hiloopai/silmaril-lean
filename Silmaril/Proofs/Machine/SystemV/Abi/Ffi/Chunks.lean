module

public import Silmaril.Machine.SystemV.Abi.Ffi.Defs

/-! # 32-bit scalars in registers: proofs

The one copy of the read-back lemmas that `Machine.Abi.OpenMachine` and
`Machine.Abi.Conformance` (`sysvInt`) both use. -/

@[expose] public section

namespace Silmaril.Proofs.Machine.SystemV.Abi.Ffi

open Silmaril.Machine.SystemV.Abi

theorem bytes4_inj {x y : BitVec 32}
    (h : Ffi.bytesOfNat x.toNat 0 4 = Ffi.bytesOfNat y.toNat 0 4) : x = y := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [Ffi.bytesOfNat, List.range_succ, List.range_zero, List.nil_append,
     List.map_cons, List.map_nil, List.cons_append,
    List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [UInt8.ofNat, UInt8.ofBitVec.injEq] at h0 h1 h2 h3
  have t := fun {a b : Nat} (e : BitVec.ofNat 8 a = BitVec.ofNat 8 b) =>
    congrArg BitVec.toNat e
  have e0 := t h0; have e1 := t h1; have e2 := t h2; have e3 := t h3
  simp only [BitVec.toNat_ofNat] at e0 e1 e2 e3
  simp only [Nat.zero_add, Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one] at e0 e1 e2 e3
  apply BitVec.eq_of_toNat_eq
  omega

theorem chunk32_iff (s : Ffi.State) (r : Silmaril.X86.Reg) (v : BitVec 32) :
    Ffi.ChunksAt s (Ffi.bytesOfNat (v.setWidth 64).toNat 0 4) [⟨0, 4, .gp r⟩] ↔
      (s.machine.core.read r).setWidth 32 = v := by
  have wide : (v.setWidth 64).toNat = v.toNat := by
    have := v.isLt
    simp only [BitVec.toNat_setWidth]
    omega
  have len : ∀ n, (Ffi.bytesOfNat n 0 4).length = 4 := by simp [Ffi.bytesOfNat]
  rw [wide]
  simp only [Ffi.ChunksAt, List.mem_singleton, forall_eq, Ffi.locationBytes, len,
    Nat.zero_add, le_refl, true_and, List.drop_zero, List.take_of_length_le (le_of_eq (len _)),
    show (4 : Nat) ≤ 8 from by decide, ite_true, Option.some.injEq]
  exact ⟨bytes4_inj, fun h => h ▸ rfl⟩

end Silmaril.Proofs.Machine.SystemV.Abi.Ffi

end

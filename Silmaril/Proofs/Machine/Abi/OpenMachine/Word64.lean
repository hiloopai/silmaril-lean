module

public import Silmaril.Proofs.Machine.Abi.OpenMachine.Sat
public import Silmaril.Machine.Abi.Win64.Thms
/-!
# 64-bit scalars in registers

The 64-bit case of track C's pending "decoding functionality" lemma (track C, next slice 5),
moved from `tests/machine/Abi.lean` into the library:

* `bytes8_inj`: eight little-endian bytes determine a 64-bit word;
* `chunk64_iff`: a 64-bit value encoded in eight bytes is read back exactly from a register;
* `resultAt_word64`: the System V read-back of a `long`, `unsigned long` or pointer result
  is exactly `rax`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.OpenMachine

open Silmaril.X86 (Reg)
open Silmaril.C.Api (Scalar)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options)

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

/-- A 64-bit value encoded in eight bytes, read from register `r`. -/
theorem chunk64_iff (s : Ffi.State) (r : Reg) (v : BitVec 64) :
    Ffi.ChunksAt s (Ffi.bytesOfNat v.toNat 0 8) [⟨0, 8, .gp r⟩] ↔
      s.machine.core.read r = v := by
  have len : ∀ n, (Ffi.bytesOfNat n 0 8).length = 8 := by simp [Ffi.bytesOfNat]
  simp only [Ffi.ChunksAt, List.mem_singleton, forall_eq, Ffi.locationBytes, len,
    Nat.zero_add, le_refl, true_and, List.drop_zero, List.take_of_length_le (le_of_eq (len _)),
    ite_true, Option.some.injEq]
  rw [show (8 * 8 : Nat) = 64 from rfl, BitVec.setWidth_eq]
  exact ⟨bytes8_inj, fun h => h ▸ rfl⟩

/-- The System V read-back of a 64-bit (`long`, `unsigned long`, pointer) result is `rax`. -/
theorem resultAt_word64 {o : Options} (args : List Scalar) (k : Scalar)
    (hk : k = .uint64 ∨ k = .int64 ∨ k = .pointer) (h : args.length ≤ SystemV.maxArity)
    (s s' : Ffi.State) (r : vocab.Ret ⟨⟨args, some k⟩, h⟩) :
    (sysv o).ResultAt ⟨⟨args, some k⟩, h⟩ s s' r ↔
      s'.machine.core.read .rax = SystemV.Kind.word k r := by
  refine (Win64.sysv_resultAt_iff _ _ _ _ _).trans ?_
  rcases hk with rfl | rfl | rfl <;>
  · constructor
    · rintro ⟨w, enc, ch⟩
      change w = _ at enc
      subst enc
      exact (chunk64_iff s' .rax r).1 ch
    · exact fun e => ⟨_, rfl, (chunk64_iff s' .rax r).2 e⟩

end Silmaril.Proofs.Machine.Abi.OpenMachine

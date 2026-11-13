module

public import Silmaril.Compiler.Native.Varargs.SaveArea.Defs
public import Silmaril.Compiler.Native.Varargs.Reconstruction.Thms
public import Silmaril.Machine.SystemV.Abi.Ffi.Bytes.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Varargs.SaveArea
open Silmaril.Cerberus.NativeTypes (Bytes)
open Silmaril.Machine.SystemV.Abi
open Reconstruction

theorem SlotsAt.gp_prefix {entry saved : Ffi.State} {base : Nat}
    (slots : SlotsAt entry saved base) (register : Silmaril.X86.Reg)
    (member : register ∈ gpArguments) (count : Nat) (fits : count ≤ 8) :
    memoryBytes saved (base + 8 * gpArguments.idxOf register) count =
      Ffi.locationBytes entry (.gp register) count := by
  have rank : gpArguments.idxOf register < 6 := by
    exact List.idxOf_lt_length_iff.mpr member
  have slice := (slots.gp register member).slice 0 count (by simpa only [Ffi.bytesOfNat_length, Nat.zero_add] using fits)
    (by have endpoint := slots.endpoint; change base + 176 < 2 ^ 64 at endpoint; omega)
  have bytes : ((Ffi.bytesOfNat (entry.machine.core.read register).toNat 0 8).drop 0).take count =
      Ffi.bytesOfNat (entry.machine.core.read register).toNat 0 count :=
    Ffi.bytesOfNat_slice _ 0 count 8 (by omega)
  rw [bytes, Nat.add_zero] at slice
  have observed := memoryBytes_of_storedAt slice
  rw [Ffi.bytesOfNat_length] at observed
  rw [Ffi.locationBytes_gp _ _ _ fits, BitVec.toNat_setWidth, Ffi.bytesOfNat_mod]
  exact observed

theorem SlotsAt.fp_slice {entry saved : Ffi.State} {base : Nat}
    (slots : SlotsAt entry saved base) (index offset count : Nat)
    (indexFits : index < 8) (fits : offset + count ≤ 16) :
    memoryBytes saved (base + 48 + 16 * index + offset) count =
      Ffi.locationBytes entry (.vector index offset) count := by
  have valid : base + 48 + 16 * index + offset < 2 ^ 64 := by
    have endpoint := slots.endpoint
    change base + 176 < 2 ^ 64 at endpoint
    omega
  have slice := (slots.fp index indexFits).slice offset count
    (by simpa only [Ffi.bytesOfNat_length] using fits) valid
  rw [Ffi.bytesOfNat_slice _ _ _ 16 fits] at slice
  have observed := memoryBytes_of_storedAt slice
  rw [Ffi.bytesOfNat_length] at observed
  have vectorFits : index < 32 ∧ offset + count ≤ 64 := by omega
  simpa only [Ffi.locationBytes, Bool.and_eq_true, decide_eq_true_eq, vectorFits.1, vectorFits.2,
    Bool.true_and, and_self, ↓reduceIte] using observed

/-- Fourteen full actual GP/XMM observations derive every physical saved
subread required by the executable reconstruction theorem. -/
theorem SlotsAt.physical {entry saved : Ffi.State} {base : Nat}
    (slots : SlotsAt entry saved base) : physicalSaveAreaAt entry saved base := by
  intro location count address selected
  cases location with
  | gp register =>
      by_cases allowed : register ∈ gpArguments ∧ count ≤ 8
      · have addressEq : base + 8 * gpArguments.idxOf register = address := by
          simpa only [savedAddress, ite_eq_left allowed, Option.some.injEq] using selected
        rw [← addressEq]
        exact slots.gp_prefix register allowed.1 count allowed.2
      · simp only [savedAddress, ite_eq_right allowed, reduceCtorEq] at selected
  | vector index offset =>
      by_cases allowed : index < 8 ∧ offset + count ≤ 16
      · have addressEq : base + 48 + 16 * index + offset = address := by
          simpa only [savedAddress, ite_eq_left allowed, Option.some.injEq] using selected
        rw [← addressEq]
        exact slots.fp_slice index offset count allowed.1 allowed.2
      · simp only [savedAddress, ite_eq_right allowed, reduceCtorEq] at selected
  | x87 index => simp only [savedAddress, reduceCtorEq] at selected

end Silmaril.Compiler.Native.Varargs.SaveArea

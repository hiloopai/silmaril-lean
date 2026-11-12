module

public import Silmaril.Machine.SystemV.Abi.Ffi.Thms

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Ffi
open Silmaril.Cerberus.NativeTypes (Bytes)

theorem bytesOfNat_slice (value offset count size : Nat) (fits : offset + count ≤ size) :
    ((bytesOfNat value 0 size).drop offset).take count = bytesOfNat value offset count := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, bytesOfNat_length]
    omega
  · intro index firstBound secondBound
    simp only [List.getElem_take, List.getElem_drop, bytesOfNat, List.getElem_map,
      List.getElem_range, Nat.zero_add]

/-- Truncating to the value width leaves every requested low byte unchanged. -/
theorem bytesOfNat_mod (value count : Nat) :
    bytesOfNat (value % 2 ^ (8 * count)) 0 count = bytesOfNat value 0 count := by
  apply List.ext_getElem
  · simp only [bytesOfNat_length]
  · intro index firstBound secondBound
    have bound : index < count := by simpa only [bytesOfNat_length] using firstBound
    have splitWidth : 8 * count = 8 * index + 8 * (count - index) := by omega
    have byteDivides : 2 ^ 8 ∣ 2 ^ (8 * (count - index)) := Nat.pow_dvd_pow 2 (by omega)
    simp only [bytesOfNat, List.getElem_map, List.getElem_range, Nat.zero_add]
    rw [splitWidth, Nat.pow_add, Nat.mod_mul_right_div_self]
    apply UInt8.toNat.inj
    simp only [UInt8.toNat_ofNat']
    exact Nat.mod_mod_of_dvd _ byteDivides

theorem readBytes_empty (memory : Silmaril.Process.Memory) (address : Nat)
    (valid : address < 2 ^ 64) : memory.readBytes address 0 = some [] := by
  have span : memory.checkSpan .read address 0 = true := by
    apply (Silmaril.Process.Memory.checkSpan_iff memory .read address 0).mpr
    exact ⟨valid, by change address + 0 ≤ 2 ^ 64; omega, by intro offset bound; omega⟩
  simp only [Silmaril.Process.Memory.readBytes, Silmaril.Process.Memory.readWith, span,
    ↓reduceIte, Silmaril.Process.Memory.readBacking]

/-- Full reads imply permission-checked subreads, including an empty slice at
the endpoint only when that endpoint is itself a valid native address. -/
theorem StoredAt.slice {state : State} {address : Nat} {bytes : Bytes}
    (stored : StoredAt state address bytes) (offset count : Nat)
    (fits : offset + count ≤ bytes.length) (valid : address + offset < 2 ^ 64) :
    StoredAt state (address + offset) ((bytes.drop offset).take count) := by
  have size : ((bytes.drop offset).take count).length = count := by
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨by rw [size]; have limit := stored.1; omega, ?_⟩
  rw [size]
  by_cases starts : offset < bytes.length
  · have observed := Silmaril.Process.Memory.readBytes_sub_range stored.2 starts fits
    simpa only [← List.map_drop, ← List.map_take] using observed
  · have empty : count = 0 := by omega
    subst count
    simpa only [List.take_zero, List.map_nil] using readBytes_empty state.machine.memory (address + offset) valid

end Silmaril.Machine.SystemV.Abi.Ffi

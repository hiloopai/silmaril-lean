module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Store
public import Silmaril.Wasm.Logic.Memory.Thms

@[expose] public section

/-!
# The Farkas checker: accumulator slots

The memory is read as `nVars` 8-byte slots: `slot B k` and `setSlot B k w`. In a page of
memory, the loads and stores of slot `k < nVars` succeed (`load_slot`, `store_slot`), a write
is read back (`slot_setSlot_same`) and leaves the other slots alone (`slot_setSlot_ne`).
`addr_mask`: the masked address of `entry`.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Logic.Core

/-- Slot `k` of the accumulators. -/
def slot (B : ByteArray) (k : Nat) : BitVec 64 := (Memory.load B (8 * k) 8).getD 0

/-- Write slot `k`. -/
def setSlot (B : ByteArray) (k : Nat) (w : BitVec 64) : ByteArray :=
  (Memory.store B (8 * k) (count := 8) w).getD B

variable {B : ByteArray} {k : Nat}

theorem load_slot (hB : B.size = 65536) (hk : k < nVars) :
    Memory.load B (8 * k) 8 = some (slot B k) := by
  have h : 8 * k + 8 ≤ B.size := by simp only [nVars] at hk; omega
  simp only [slot, load_eq h, Option.getD_some]

theorem store_slot (hB : B.size = 65536) (hk : k < nVars) (w : BitVec 64) :
    Memory.store B (8 * k) (count := 8) w = some (setSlot B k w) := by
  have h : 8 * k + 8 ≤ B.size := by simp only [nVars] at hk; omega
  simp only [setSlot, store_eq w h, Option.getD_some]

theorem size_setSlot (hB : B.size = 65536) (hk : k < nVars) (w : BitVec 64) :
    (setSlot B k w).size = 65536 :=
  (size_store (store_slot hB hk w)).trans hB

theorem slot_setSlot_same (hB : B.size = 65536) (hk : k < nVars) (w : BitVec 64) :
    slot (setSlot B k w) k = w := by
  simp only [slot, load_store_same (store_slot hB hk w), Option.getD_some]

theorem slot_setSlot_ne {k' : Nat} (hB : B.size = 65536) (hk : k < nVars) (hne : k ≠ k')
    (w : BitVec 64) : slot (setSlot B k w) k' = slot B k' := by
  have hd : Region.Disjoint ⟨8 * k, 8⟩ ⟨8 * k', 8⟩ := by
    simp only [Region.Disjoint, Region.stop]
    omega
  simp only [slot, load_store_disjoint (store_slot hB hk w) hd]

/-- The address `entry` computes: slot `j mod nVars`. -/
theorem addr_mask (j : BitVec 32) :
    ((j &&& BitVec.ofNat 32 (nVars - 1)) <<< (3 : Nat)).toNat = 8 * (j.toNat % nVars) := by
  have h8191 : BitVec.ofNat 32 (nVars - 1) = 8191#32 := rfl
  have hand : (j &&& 8191#32).toNat = j.toNat % 8192 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod j.toNat 13
  have hlt : j.toNat % 8192 < 8192 := Nat.mod_lt _ (by decide)
  rw [h8191, BitVec.toNat_shiftLeft, hand, Nat.shiftLeft_eq, nVars]
  omega

theorem size_zeroBytes : zeroBytes.size = 65536 := by
  simp only [zeroBytes, ByteArray.size, Array.size_replicate]

/-- The zero memory reads zero in every slot. -/
theorem slot_zeroBytes (hk : k < nVars) : slot zeroBytes k = 0 := by
  have hk8 : k < 8192 := hk
  have hk' : 8 * k + 8 ≤ zeroBytes.size := by rw [size_zeroBytes]; omega
  have hb : bytesAt zeroBytes ⟨8 * k, 8⟩ = List.replicate 8 0 := by
    simp only [bytesAt, zeroBytes, Array.toList_replicate, List.drop_replicate, List.take_replicate]
    congr 1
    omega
  simp only [slot, load_eq hk', hb, Option.getD_some]
  rfl

end Silmaril.Wasm.Examples.Farkas

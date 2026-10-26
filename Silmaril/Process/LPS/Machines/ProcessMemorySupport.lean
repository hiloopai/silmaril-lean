module

public import Silmaril.Process.LPS.Machines.ProcessMemory

/-! # Symbolic lookup through loader installations

These rules reason about the loader's wrapping byte installation without
evaluating an image or the eager stack-zero map. Their non-wrapping forms
make the address-space obligation explicit.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines

open Silmaril.Process (ByteMemory)

private theorem foldl_insertWrapping_outside (memory : ByteMemory) (base : Nat)
    (pairs : List (Byte × Nat)) (address : Nat)
    (outside : ∀ pair ∈ pairs, (base + pair.2) % 2 ^ 64 ≠ address) :
    (pairs.foldl (fun acc pair => acc.insert ((base + pair.2) % 2 ^ 64) pair.1) memory).get?
      address = memory.get? address := by
  induction pairs generalizing memory with
  | nil => rfl
  | cons pair pairs ih =>
    rw [List.foldl_cons, ih _ (fun other member => outside other (List.mem_cons_of_mem _ member))]
    change (memory.insert ((base + pair.2) % 2 ^ 64) pair.1)[address]? = memory[address]?
    rw [Std.ExtHashMap.getElem?_insert]
    simp only [beq_iff_eq, outside pair (List.mem_cons_self), ↓reduceIte]

theorem installWrapping_outside_mod (memory : ByteMemory) (base : Nat) (bytes : List Byte)
    (address : Nat) (outside : ∀ index < bytes.length, (base + index) % 2 ^ 64 ≠ address) :
    (installWrapping memory base bytes).get? address = memory.get? address := by
  apply foldl_insertWrapping_outside
  intro pair member
  exact outside pair.2 (by simpa using List.snd_lt_add_of_mem_zipIdx member)

theorem installWrapping_outside (memory : ByteMemory) (base : Nat) (bytes : List Byte)
    (address : Nat) (nowrap : base + bytes.length ≤ 2 ^ 64)
    (outside : address < base ∨ base + bytes.length ≤ address) :
    (installWrapping memory base bytes).get? address = memory.get? address := by
  apply installWrapping_outside_mod
  intro index bound
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem foldl_zipIdx_get (bytes : List Byte) (memory : ByteMemory) (base start index : Nat)
    (bound : index < bytes.length) (nowrap : base + start + bytes.length ≤ 2 ^ 64) :
    ((bytes.zipIdx start).foldl
      (fun acc pair => acc.insert ((base + pair.2) % 2 ^ 64) pair.1) memory).get?
      (base + start + index) = some bytes[index] := by
  induction bytes generalizing memory start index with
  | nil => simp at bound
  | cons byte bytes ih =>
    rw [List.zipIdx_cons, List.foldl_cons]
    cases index with
    | zero =>
      rw [foldl_insertWrapping_outside]
      · simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [Nat.mod_eq_of_lt (show base + start < 2 ^ 64 by
          simp only [List.length_cons] at nowrap; omega)]
        exact Std.ExtHashMap.getElem?_insert_self
      · intro pair member
        have lower := List.le_snd_of_mem_zipIdx member
        have upper := List.snd_lt_add_of_mem_zipIdx member
        rw [Nat.mod_eq_of_lt (by simp only [List.length_cons] at nowrap; omega)]
        omega
    | succ index =>
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 index] using
        ih (memory.insert ((base + start) % 2 ^ 64) byte) (start + 1) index
          (by simpa using bound) (by simp only [List.length_cons] at nowrap; omega)

theorem installWrapping_get (memory : ByteMemory) (base : Nat) (bytes : List Byte)
    (index : Nat) (bound : index < bytes.length) (nowrap : base + bytes.length ≤ 2 ^ 64) :
    (installWrapping memory base bytes).get? (base + index) = some bytes[index] := by
  exact foldl_zipIdx_get bytes memory base 0 index bound (by simpa using nowrap)

/-- The byte that installing `segments` in order leaves at `address`, given the
byte already there: the last covering segment wins. This is an ordinary list
computation, so concrete images can be inspected by the kernel without
evaluating a hash map. -/
def segmentsView (segments : List Segment) (address : Nat) (prior : Option Byte) : Option Byte :=
  segments.foldl (fun acc segment =>
    if segment.base ≤ address ∧ address < segment.base + segment.bytes.length then
      segment.bytes[address - segment.base]? else acc) prior

theorem installWrapping_get_ite (memory : ByteMemory) (base : Nat) (bytes : List Byte)
    (address : Nat) (nowrap : base + bytes.length ≤ 2 ^ 64) :
    (installWrapping memory base bytes).get? address =
      if base ≤ address ∧ address < base + bytes.length then bytes[address - base]?
      else memory.get? address := by
  by_cases inside : base ≤ address ∧ address < base + bytes.length
  · simp only [inside, and_self, ↓reduceIte]
    obtain ⟨index, rfl⟩ : ∃ index, address = base + index := ⟨address - base, by omega⟩
    rw [Nat.add_sub_cancel_left, installWrapping_get memory base bytes index (by omega) nowrap,
      List.getElem?_eq_getElem (by omega)]
  · rw [ite_eq_right_iff.mpr (fun within => absurd within inside)]
    exact installWrapping_outside memory base bytes address nowrap (by omega)

theorem segments_foldl_get (segments : List Segment) (memory : ByteMemory) (address : Nat)
    (nowrap : ∀ segment ∈ segments, segment.base + segment.bytes.length ≤ 2 ^ 64) :
    (segments.foldl (fun acc segment => installWrapping acc segment.base segment.bytes) memory).get?
      address = segmentsView segments address (memory.get? address) := by
  induction segments generalizing memory with
  | nil => rfl
  | cons segment segments ih =>
    rw [List.foldl_cons, ih _ (fun other member => nowrap other (List.mem_cons_of_mem _ member)),
      installWrapping_get_ite _ _ _ _ (nowrap segment List.mem_cons_self)]
    rfl

/-- Image bytes of the segment-only memory used by ISA entry checks. -/
theorem initialMemory_segments_get (segments : List Segment) (address : Nat)
    (nowrap : ∀ segment ∈ segments, segment.base + segment.bytes.length ≤ 2 ^ 64) :
    (initialMemory segments 0 []).bytes.get? address = segmentsView segments address none := by
  have reduce : (initialMemory segments 0 []).bytes =
      segments.foldl (fun acc segment => installWrapping acc segment.base segment.bytes) ∅ := rfl
  rw [reduce, segments_foldl_get segments ∅ address nowrap, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.getElem?_empty]

end Silmaril.Process.LPS.Machines

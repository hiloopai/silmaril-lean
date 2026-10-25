module

public import Mathlib.Data.BitVec

@[expose] public section

/-! # Linear byte memory

Memory and byte sequences use Lean's native `ByteArray`, with `UInt8` elements.
Bounds are checked in natural numbers, before any address truncation. Writes
preserve memory size; copying reads the complete source before writing, so
overlapping ranges have `memmove` semantics. Growth can fail even when its bounds
permit success, as allowed by Wasm's resource-dependent allocation semantics.
-/

namespace Silmaril.Wasm.Execution.Memory

abbrev Byte := UInt8
abbrev Bytes := ByteArray

def readBytes (memory : Bytes) (start count : Nat) : Option Bytes :=
  if start + count ≤ memory.size then some (memory.extract start (start + count)) else none

def writeBytes (memory : Bytes) (start : Nat) (bytes : Bytes) : Option Bytes :=
  if start + bytes.size ≤ memory.size then
    some (bytes.copySlice 0 memory start bytes.size)
  else none

def decodeLE (bytes : Bytes) : Nat :=
  bytes.data.foldr (fun byte rest => byte.toNat + 256 * rest) 0

def encodeLE : Nat → Nat → Bytes
  | 0, _ => .empty
  | count + 1, n => ⟨#[UInt8.ofNat n]⟩ ++ encodeLE count (n / 256)

def load (memory : Bytes) (start count : Nat) : Option (BitVec (8 * count)) :=
  (readBytes memory start count).map fun bytes => BitVec.ofNat (8 * count) (decodeLE bytes)

def store (memory : Bytes) (start : Nat) {count : Nat}
    (word : BitVec (8 * count)) : Option Bytes :=
  writeBytes memory start (encodeLE count word.toNat)

def copy (memory : Bytes) (destination source count : Nat) : Option Bytes := do
  let bytes ← readBytes memory source count
  writeBytes memory destination bytes

def fill (memory : Bytes) (destination : Nat) (byte : Byte) (count : Nat) : Option Bytes :=
  writeBytes memory destination ⟨Array.replicate count byte⟩

def pageSize : Nat := 65536
def maxPages : Nat := 65536

def size (memory : Bytes) : Nat := memory.size / pageSize

def grow? (memory : Bytes) (maximum : Option Nat) (delta : Nat) : Option Bytes :=
  if memory.size % pageSize = 0 ∧ size memory + delta ≤ maxPages ∧
      (maximum.isNone ∨ size memory + delta ≤ maximum.getD 0) then
    some (memory ++ ⟨Array.replicate (delta * pageSize) 0⟩)
  else none

/-- Failure preserves memory and returns the all-ones sentinel. -/
inductive Grow (memory : Bytes) (maximum : Option Nat) (delta : Nat) :
    Bytes → BitVec 32 → Prop where
  | success (after : Bytes) (h : grow? memory maximum delta = some after) :
      Grow memory maximum delta after (BitVec.ofNat 32 (size memory))
  | failure : Grow memory maximum delta memory (-1)

theorem readBytes_eq_some_iff (memory bytes : Bytes) (start count : Nat) :
    readBytes memory start count = some bytes ↔
      start + count ≤ memory.size ∧ bytes = memory.extract start (start + count) := by
  simp [readBytes, eq_comm]

theorem readBytes_size (memory bytes : Bytes) (start count : Nat)
    (h : readBytes memory start count = some bytes) : bytes.size = count := by
  obtain ⟨bound, rfl⟩ := (readBytes_eq_some_iff memory bytes start count).mp h
  simp only [ByteArray.size_extract]
  omega

theorem writeBytes_eq_some_iff (memory bytes after : Bytes) (start : Nat) :
    writeBytes memory start bytes = some after ↔
      start + bytes.size ≤ memory.size ∧
      after = memory.extract 0 start ++ bytes ++
        memory.extract (start + bytes.size) memory.size := by
  simp [writeBytes, ByteArray.copySlice_eq_append, ByteArray.size_data, eq_comm]

theorem writeBytes_size (memory bytes after : Bytes) (start : Nat)
    (h : writeBytes memory start bytes = some after) : after.size = memory.size := by
  obtain ⟨bound, rfl⟩ := (writeBytes_eq_some_iff memory bytes after start).mp h
  simp only [ByteArray.size_append, ByteArray.size_extract]
  omega

theorem readBytes_writeBytes (memory bytes after : Bytes) (start : Nat)
    (h : writeBytes memory start bytes = some after) :
    readBytes after start bytes.size = some bytes := by
  have sizes := writeBytes_size memory bytes after start h
  obtain ⟨bound, rfl⟩ := (writeBytes_eq_some_iff memory bytes after start).mp h
  have prefixSize : (memory.extract 0 start).size = start := by
    simp only [ByteArray.size_extract]
    omega
  unfold readBytes
  rw [sizes, ite_eq_left bound, ByteArray.append_assoc]
  congr 1
  calc
    _ = (bytes ++ memory.extract (start + bytes.size) memory.size).extract 0 bytes.size := by
      simpa only [Nat.add_zero] using
        (ByteArray.extract_append_size_add' (a := memory.extract 0 start)
          (b := bytes ++ memory.extract (start + bytes.size) memory.size)
          (i := 0) (j := bytes.size) prefixSize.symm)
    _ = bytes := ByteArray.extract_append_eq_left rfl

@[simp] theorem encodeLE_size (count n : Nat) : (encodeLE count n).size = count := by
  induction count generalizing n with
  | zero => rfl
  | succ count ih =>
    simp only [encodeLE, ByteArray.size_append, ih]
    change 1 + count = count + 1
    omega

theorem decodeLE_encodeLE (count n : Nat) : decodeLE (encodeLE count n) = n % 256 ^ count := by
  induction count generalizing n with
  | zero => simp [encodeLE, decodeLE, Nat.mod_one]
  | succ count ih =>
      simp only [encodeLE, decodeLE, ByteArray.data_append, Array.foldr_append]
      change (UInt8.ofNat n).toNat + 256 * decodeLE (encodeLE count (n / 256)) = _
      rw [UInt8.toNat_ofNat', ih]
      change n % 256 + 256 * (n / 256 % 256 ^ count) = n % 256 ^ (count + 1)
      rw [show 256 ^ (count + 1) = 256 * 256 ^ count from Nat.pow_succ' ..]
      exact Nat.mod_mul.symm

theorem load_store (memory after : Bytes) (start count : Nat) (word : BitVec (8 * count))
    (h : store memory start word = some after) : load after start count = some word := by
  have read := readBytes_writeBytes memory (encodeLE count word.toNat) after start h
  rw [encodeLE_size] at read
  simp only [load, read, Option.map_some, decodeLE_encodeLE]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have power : 256 ^ count = 2 ^ (8 * count) := by rw [Nat.pow_mul]
  simp [power, Nat.mod_eq_of_lt word.isLt]

theorem copy_size (memory after : Bytes) (destination source count : Nat)
    (h : copy memory destination source count = some after) : after.size = memory.size := by
  unfold copy at h
  cases read : readBytes memory source count with
  | none => simp [read] at h
  | some bytes => exact writeBytes_size memory bytes after destination (by simpa [read] using h)

theorem fill_size (memory after : Bytes) (destination count : Nat) (byte : Byte)
    (h : fill memory destination byte count = some after) : after.size = memory.size :=
  writeBytes_size memory ⟨Array.replicate count byte⟩ after destination h

theorem grow_size (memory after : Bytes) (maximum : Option Nat) (delta : Nat)
    (h : grow? memory maximum delta = some after) :
    after.size = memory.size + delta * pageSize := by
  unfold grow? at h
  split at h
  · cases h
    simp only [ByteArray.size_append]
    change memory.size + (Array.replicate (delta * pageSize) (0 : UInt8)).size = _
    rw [Array.size_replicate]
  · contradiction

example : load ⟨#[0x78, 0x56, 0x34, 0x12]⟩ 0 4 = some 0x12345678#32 := rfl
example : copy ⟨#[1, 2, 3, 4]⟩ 1 0 3 = some ⟨#[1, 1, 2, 3]⟩ := rfl
example : copy ⟨#[1, 2, 3, 4]⟩ 0 1 3 = some ⟨#[2, 3, 4, 4]⟩ := rfl
example : readBytes ⟨#[1]⟩ 1 0 = some .empty := rfl
example : readBytes ⟨#[1]⟩ 2 0 = none := rfl
example : store ⟨#[1]⟩ 0 (count := 2) (0x1234#16) = none := rfl

end Silmaril.Wasm.Execution.Memory

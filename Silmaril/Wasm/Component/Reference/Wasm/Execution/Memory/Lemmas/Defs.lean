module

public import Silmaril.Wasm.Execution.Memory

/-!
# `Wasm.Execution.Memory.Lemmas`: the laws that definitions cite

The theorems of the component reference copy `Wasm.Execution.Memory.Lemmas` that definition parts
cite (engine records bundle such laws as fields). The other theorems stay in
`Silmaril.Raw.Wasm.Component.Wasm.Execution.Memory.Lemmas`, which imports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Memory

/-- The bytes preceding a successful write are unchanged. -/
theorem extract_before_writeBytes (memory bytes after : Bytes) (start : Nat)
    (h : writeBytes memory start bytes = some after) :
    after.extract 0 start = memory.extract 0 start := by
  obtain ⟨bound, rfl⟩ := (writeBytes_eq_some_iff memory bytes after start).mp h
  have prefixSize : (memory.extract 0 start).size = start := by
    simp only [ByteArray.size_extract]
    omega
  rw [ByteArray.append_assoc]
  exact ByteArray.extract_append_eq_left prefixSize.symm

/-- The bytes following a successful write are unchanged. -/
theorem extract_after_writeBytes (memory bytes after : Bytes) (start : Nat)
    (h : writeBytes memory start bytes = some after) :
    after.extract (start + bytes.size) after.size =
      memory.extract (start + bytes.size) memory.size := by
  obtain ⟨bound, rfl⟩ := (writeBytes_eq_some_iff memory bytes after start).mp h
  have prefixSize : (memory.extract 0 start ++ bytes).size = start + bytes.size := by
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  exact ByteArray.extract_append_eq_right prefixSize.symm ByteArray.size_append

/-- Reads on either side of a write retain their original result, including bounds failures. -/
theorem readBytes_writeBytes_disjoint (memory bytes after : Bytes) (start readStart count : Nat)
    (h : writeBytes memory start bytes = some after)
    (disjoint : readStart + count ≤ start ∨ start + bytes.size ≤ readStart) :
    readBytes after readStart count = readBytes memory readStart count := by
  have sizes := writeBytes_size memory bytes after start h
  unfold readBytes
  rw [sizes]
  split
  · rename_i bound
    congr 1
    rcases disjoint with before | afterRange
    · have prefixes := congrArg (fun xs : Bytes => xs.extract readStart (readStart + count))
        (extract_before_writeBytes memory bytes after start h)
      simpa only [ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left before] using prefixes
    · have suffixes := congrArg (fun xs : Bytes =>
          xs.extract (readStart - (start + bytes.size)) (readStart + count - (start + bytes.size)))
        (extract_after_writeBytes memory bytes after start h)
      have lower : start + bytes.size + (readStart - (start + bytes.size)) = readStart := by omega
      have upper : start + bytes.size + (readStart + count - (start + bytes.size)) =
          readStart + count := by omega
      simpa only [ByteArray.extract_extract, lower, upper, sizes, Nat.min_eq_left bound] using suffixes
  · rfl

end Silmaril.Wasm.Execution.Memory

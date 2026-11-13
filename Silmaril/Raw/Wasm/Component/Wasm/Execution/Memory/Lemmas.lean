module

public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs
public import Silmaril.Wasm.Execution.Memory

/-!
# Locality of linear-memory writes

A successful write preserves byte reads and typed word loads from any disjoint
range. Bounds failures are preserved too, because writes preserve memory size.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Memory

/-- The corresponding theorem for little-endian machine words needs no alignment premise. -/
theorem load_writeBytes_disjoint (memory bytes after : Bytes) (start readStart count : Nat)
    (h : writeBytes memory start bytes = some after)
    (disjoint : readStart + count ≤ start ∨ start + bytes.size ≤ readStart) :
    load after readStart count = load memory readStart count := by
  simp only [load, readBytes_writeBytes_disjoint memory bytes after start readStart count h disjoint]

/-- A typed store preserves all disjoint typed loads. -/
theorem load_store_disjoint (memory after : Bytes) (start readStart readCount writeCount : Nat)
    (word : BitVec (8 * writeCount)) (h : store memory start word = some after)
    (disjoint : readStart + readCount ≤ start ∨ start + writeCount ≤ readStart) :
    load after readStart readCount = load memory readStart readCount := by
  apply load_writeBytes_disjoint memory (encodeLE writeCount word.toNat) after start readStart readCount h
  simpa only [encodeLE_size] using disjoint

end Silmaril.Wasm.Execution.Memory

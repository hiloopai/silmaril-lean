module
public import Silmaril.Compiler.C.Sem.C1LirScalarStore.Defs
public import Silmaril.Compiler.C.Sem.C1LirScalarMemoryChecks.Defs
@[expose] public section
namespace Silmaril.Compile.C.Sem.C1LirScalarStoreChecks
open Silmaril.Machine
open C1LirMemory C1LirScalarStore C1LirScalarMemory.Checks

/-- Every 64-bit byte pattern can be written into an actual nine-byte source
allocation and transferred, with the ninth target byte framed. -/
theorem all_bytes (old : Fin 9 → UInt8) (new : Fin 8 → UInt8) :
    ∃ source target,
      (memory old).writeBytes C1.base (Array.ofFn new) = .ok source ∧
      Rel source target ∧ target.bytes (C1.base + 8) = (old ⟨8, by decide⟩).toBitVec := by
  let bytes := Array.ofFn new
  let target := (List.range bytes.size).foldl
    (fun memory i => stored memory (C1.base + (C1.base - C1.base + i)) bytes[i]!)
    (embed (memory old))
  have valid : (memory old).valid C1.base bytes.size = true := by
    simp [C1.Memory.valid, memory, bytes]
  have writable : (memory old).roTop ≤ C1.base := le_rfl
  have backed : C1.base - C1.base + bytes.size ≤ (memory old).bytes.size := by
    simp [bytes, memory, ByteArray.size]
  have writes := writeBytes_related (embed_related (memory old)) C1.base bytes valid writable backed
  refine ⟨written (memory old) C1.base bytes, target, writes.1, writes.2, ?_⟩
  have frame := stores_frame (embed (memory old)) (List.range bytes.size)
    (fun i => C1.base + (C1.base - C1.base + i)) (fun i => bytes[i]!) (C1.base + 8) (by
      intro i member
      have bound := List.mem_range.mp member
      have size : bytes.size = 8 := Array.size_ofFn
      omega)
  change target.bytes (C1.base + 8) = _
  rw [frame]
  exact (embed_related (memory old)).byte (cell old ⟨8, by decide⟩)

/-- Deliberately malformed metadata: the data span is physically backed while
the initialization array is empty. The raw-write theorem permits this shape;
it does not establish that subsequent source reads are initialized. -/
def missingInit : C1.Memory :=
  ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨#[]⟩, C1.base, C1.base + 8⟩

def replacement : Array UInt8 := #[1, 2, 3, 4, 5, 6, 7, 8]

/-- Actual logical write success and full byte relation do not reconstruct an
absent initialization array. This is a kernel-checked boundary witness, rather
than an execution test of malformed arrays. -/
theorem initialization_backing_not_reconstructed :
    ∃ source target,
      missingInit.writeBytes C1.base replacement = .ok source ∧
      Rel source target ∧ source.init.size = 0 := by
  have writes := writeBytes_related (embed_related missingInit) C1.base replacement
    (by decide) (by decide) (by decide)
  exact ⟨written missingInit C1.base replacement, _, writes.1, writes.2, by decide⟩

end Silmaril.Compile.C.Sem.C1LirScalarStoreChecks

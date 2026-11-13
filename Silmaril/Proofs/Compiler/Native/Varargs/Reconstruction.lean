module

public import Silmaril.Compiler.Native.Varargs.Reconstruction.Defs
public import Silmaril.Compiler.Native.Varargs.Thms
public import Silmaril.Machine.SystemV.Abi.Ffi.Thms
public import Silmaril.Machine.SystemV.Abi.Representation.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Varargs.Reconstruction

open Silmaril.Cerberus NativeTypes NativeValues
open Silmaril.Machine.SystemV.Abi

theorem memoryBytes_of_storedAt {saved : Ffi.State} {address : Nat} {bytes : Bytes}
    (stored : Ffi.StoredAt saved address bytes) :
    memoryBytes saved address bytes.length = some bytes := by
  unfold memoryBytes
  rw [stored.2]
  simp only [Option.map_some, List.map_map]
  congr 1
  calc
    _ = bytes.map id := List.map_congr_left (fun byte _ => by
      simp only [Function.comp_apply, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt byte.toNat_lt_size]
      exact UInt8.ofNat_toNat)
    _ = bytes := List.map_id bytes

private theorem option_mapM_eq_map (indices : List Nat) (read : Nat → Option UInt8)
    (value : Nat → UInt8) (observed : ∀ index ∈ indices, read index = some (value index)) :
    indices.mapM read = some (indices.map value) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.mapM_cons, observed index (by simp),
        ih (fun i member => observed i (by simp [member])), List.map_cons]
      rfl

private theorem map_getD_range (bytes : Bytes) :
    (List.range bytes.length).map (fun index => bytes[index]?.getD 0) = bytes := by
  apply List.ext_getElem
  · simp
  · intro index firstBound secondBound
    simp only [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem secondBound,
      Option.getD_some]

theorem pieceAssignment_member {state : VaList} {relative : List Piece} {assigned : List Chunk}
    (matched : pieceAssignment state relative assigned = true)
    (piece : Piece) (member : piece ∈ relative) :
    ∃ chunk ∈ assigned, chunk.offset = piece.objectOffset ∧ chunk.bytes = piece.bytes ∧
      savedAddress state.regSaveArea chunk.location chunk.bytes = some (pieceAddress state piece) := by
  simp only [pieceAssignment, List.all_eq_true, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at matched
  obtain ⟨chunk, included, ⟨offset, size⟩, address⟩ := matched piece member
  exact ⟨chunk, included, offset, size, address⟩

theorem piece_memory {entry saved : Ffi.State} {state : VaList} {relative : List Piece}
    {assigned : List Chunk} {bytes : Bytes}
    (snapshot : physicalSaveAreaAt entry saved state.regSaveArea)
    (matched : pieceAssignment state relative assigned = true)
    (arguments : Ffi.ChunksAt entry bytes assigned)
    (piece : Piece) (member : piece ∈ relative) :
    memoryBytes saved (pieceAddress state piece) piece.bytes =
      some ((bytes.drop piece.objectOffset).take piece.bytes) := by
  obtain ⟨chunk, included, offset, size, address⟩ := pieceAssignment_member matched piece member
  have observed := snapshot chunk.location chunk.bytes _ address
  rw [(arguments chunk included).2] at observed
  simpa only [offset, size] using observed

theorem pieceByte_eq {entry saved : Ffi.State} {state : VaList} {relative : List Piece}
    {assigned : List Chunk} {bytes : Bytes} {index : Nat}
    (snapshot : physicalSaveAreaAt entry saved state.regSaveArea)
    (matched : pieceAssignment state relative assigned = true)
    (covered : fullCoverage bytes.length relative = true)
    (arguments : Ffi.ChunksAt entry bytes assigned) (bound : index < bytes.length) :
    pieceByte saved state relative index = bytes[index]? := by
  have existsPiece : ∃ piece ∈ relative, covers piece index = true := by
    simpa only [fullCoverage, List.all_eq_true, List.mem_range, List.any_eq_true] using
      (show ∀ index ∈ List.range bytes.length, ∃ piece ∈ relative, covers piece index = true by
        simpa only [fullCoverage, List.all_eq_true, List.any_eq_true] using covered) index (by simp [bound])
  obtain ⟨piece, selected⟩ : ∃ piece, relative.find? (covers · index) = some piece := by
    exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr existsPiece)
  have member := List.mem_of_find?_eq_some selected
  have coversIndex := List.find?_some selected
  simp only [covers, decide_eq_true_eq] at coversIndex
  unfold pieceByte
  rw [selected]
  change (memoryBytes saved (pieceAddress state piece) piece.bytes >>= fun observed =>
    observed[index - piece.objectOffset]?) = bytes[index]?
  rw [piece_memory snapshot matched arguments piece member]
  change ((bytes.drop piece.objectOffset).take piece.bytes)[index - piece.objectOffset]? = bytes[index]?
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le coversIndex.1]

theorem reconstruct_eq {entry saved : Ffi.State} {state : VaList} {relative : List Piece}
    {assigned : List Chunk} {bytes : Bytes}
    (snapshot : physicalSaveAreaAt entry saved state.regSaveArea)
    (matched : pieceAssignment state relative assigned = true)
    (covered : fullCoverage bytes.length relative = true)
    (arguments : Ffi.ChunksAt entry bytes assigned) :
    reconstruct saved state relative bytes.length = some bytes := by
  unfold reconstruct
  rw [option_mapM_eq_map _ _ (fun index => bytes[index]?.getD 0)]
  · rw [map_getD_range]
  · intro index member
    have bound : index < bytes.length := List.mem_range.mp member
    rw [pieceByte_eq snapshot matched covered arguments bound,
      List.getElem?_eq_getElem bound]
    rfl

/-- The input is a genuine typed FFI argument at actual shifted chunk outputs.
The output encoding is derived from physical saved observations and finite
placement/coverage checks; no output value or successful read is a premise. -/
theorem read_registers_encodes {context : Representation.Context} {type : CType}
    (spec : Representation.Spec context type) (value : TypedValue context.values type)
    {entry saved : Ffi.State} {state : VaList}
    (placement : RegisterPlacement state spec.object)
    (argument : Ffi.ArgumentAt entry spec.toFfi value ⟨spec.object, placement.assigned, none⟩)
    (snapshot : physicalSaveAreaAt entry saved state.regSaveArea)
    (memory : memoryClass spec.object = false) (wide : needsWideVector spec.object = false)
    (gp : state.gpOffset + 8 * gpCount spec.object ≤ 48)
    (fp : state.fpOffset + 16 * vectorCount spec.object ≤ 176) :
    ∃ bytes, readArgument saved state spec.object = some (bytes, (state.next spec.object).2) ∧
      spec.toFfi.representation.encodes value bytes ∧
      Representation.Stores context type value.value bytes := by
  obtain ⟨_, bytes, size, stored, chunksAt⟩ := (spec.argumentAt_iff entry value _).mp argument
  have covered : fullCoverage bytes.length placement.relative = true := by
    rw [size]
    exact placement.covered
  have read := reconstruct_eq snapshot placement.matched covered chunksAt
  have next := next_registers state spec.object memory wide gp fp
  refine ⟨bytes, ?_, (spec.encodes_iff value bytes).mpr ⟨size, stored⟩, stored⟩
  rw [size] at read
  unfold readArgument
  rw [next]
  change (do
    let relative ← (pieces spec.object).toOption
    let output ← reconstruct saved state relative spec.object.size
    pure (output, _)) = some (bytes, _)
  rw [placement.piecesComputed]
  change (reconstruct saved state placement.relative spec.object.size >>= fun output =>
    some (output, _)) = some (bytes, _)
  rw [read]
  rfl

/-- A real stored stack argument is read from the actual aligned overflow
branch. Alignment identifies its source address; the original encoding then
supplies the derived output storage fact. -/
theorem read_stack_encodes {context : Representation.Context} {type : CType}
    (spec : Representation.Spec context type) (value : TypedValue context.values type)
    {entry saved : Ffi.State} {state : VaList} {offset address : Nat}
    (argument : Ffi.ArgumentAt entry spec.toFfi value ⟨spec.object, [], some offset⟩)
    (stack : (state.next spec.object).1 = .stack address)
    (aligned : address = (entry.machine.core.read .rsp).toNat + 8 + offset)
    (sameMemory : saved.machine.memory = entry.machine.memory) :
    ∃ bytes, readArgument saved state spec.object = some (bytes, (state.next spec.object).2) ∧
      spec.toFfi.representation.encodes value bytes ∧
      Representation.Stores context type value.value bytes := by
  obtain ⟨_, bytes, size, stored, atAddress⟩ := (spec.argumentAt_iff entry value _).mp argument
  have observed := memoryBytes_of_storedAt atAddress
  have source : memoryBytes saved address spec.object.size = some bytes := by
    unfold memoryBytes at observed ⊢
    simpa only [sameMemory, aligned, size] using observed
  refine ⟨bytes, ?_, (spec.encodes_iff value bytes).mpr ⟨size, stored⟩, stored⟩
  unfold readArgument
  rw [show state.next spec.object = (.stack address, (state.next spec.object).2) from
    Prod.ext stack rfl]
  change (memoryBytes saved address spec.object.size >>= fun output =>
    some (output, (state.next spec.object).2)) = some (bytes, _)
  rw [source]
  rfl

end Silmaril.Compiler.Native.Varargs.Reconstruction

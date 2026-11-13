module

public import Silmaril.Compiler.Native.Varargs.Placement.Defs
public import Silmaril.Compiler.Native.Varargs.Reconstruction.Thms
public import Silmaril.Machine.SystemV.Abi.Chunks.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Varargs.Placement
open Silmaril.Machine.SystemV.Abi
open Reconstruction

/-- The production monadic conversion is exposed without changing its errors. -/
theorem pieces_eq_mapM (object : Object) :
    pieces object = (do
      let relative ← chunks object gpArguments 0 0
      relative.mapM toPiece) := rfl

theorem pieceAssignment_iff (state : VaList) (relative : List Piece) (assigned : List Chunk) :
    pieceAssignment state relative assigned = true ↔
      ∀ piece ∈ relative, ∃ chunk ∈ assigned,
        chunk.offset = piece.objectOffset ∧ chunk.bytes = piece.bytes ∧
          savedAddress state.regSaveArea chunk.location chunk.bytes = some (pieceAddress state piece) := by
  simp only [pieceAssignment, List.all_eq_true, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq, and_assoc]

private theorem toPiece_shift_gp {state : VaList} {gp fp objectOffset count : Nat}
    (register : Silmaril.X86.Reg) (gpCursor : state.gpOffset = 8 * gp)
    (fits : RelativeSlotFits gp fp ⟨objectOffset, count, .gp register⟩) :
    ∃ piece, toPiece ⟨objectOffset, count, .gp register⟩ = .ok piece ∧
      (Chunks.shiftChunk gp fp ⟨objectOffset, count, .gp register⟩).offset = piece.objectOffset ∧
      (Chunks.shiftChunk gp fp ⟨objectOffset, count, .gp register⟩).bytes = piece.bytes ∧
      savedAddress state.regSaveArea (Chunks.shiftChunk gp fp ⟨objectOffset, count, .gp register⟩).location
        (Chunks.shiftChunk gp fp ⟨objectOffset, count, .gp register⟩).bytes = some (pieceAddress state piece) := by
  rcases fits with ⟨member, capacity, size⟩
  have rank : gpArguments.idxOf register < gpArguments.length := List.idxOf_lt_length_iff.mpr member
  have shiftedBound : gp + gpArguments.idxOf register < gpArguments.length := capacity
  have original : gpArguments[gpArguments.idxOf register] = register := List.getElem_idxOf rank
  have shifted : Chunks.shiftChunk gp fp ⟨objectOffset, count, .gp register⟩ =
      ⟨objectOffset, count, .gp gpArguments[gp + gpArguments.idxOf register]⟩ := by
    simpa only [original] using
      Chunks.shiftChunk_gp gp fp (gpArguments.idxOf register) objectOffset count rank shiftedBound
  have included : gpArguments[gp + gpArguments.idxOf register] ∈ gpArguments := List.getElem_mem _
  have shiftedRank : gpArguments.idxOf gpArguments[gp + gpArguments.idxOf register] =
      gp + gpArguments.idxOf register :=
    (by decide : gpArguments.Nodup).idxOf_getElem (gp + gpArguments.idxOf register) shiftedBound
  refine ⟨⟨objectOffset, count, .gp, 8 * gpArguments.idxOf register⟩, rfl, ?_⟩
  rw [shifted]
  refine ⟨rfl, rfl, ?_⟩
  simp only [savedAddress, included, size, and_self, ↓reduceIte, pieceAddress, gpCursor,
    shiftedRank]
  congr 1
  omega

/-- Physical location arithmetic for one actual relative chunk. -/
theorem toPiece_shift {state : VaList} {gp fp : Nat} {chunk : Chunk}
    (gpCursor : state.gpOffset = 8 * gp) (fpCursor : state.fpOffset = 48 + 16 * fp)
    (fits : RelativeSlotFits gp fp chunk) :
    ∃ piece, toPiece chunk = .ok piece ∧
      (Chunks.shiftChunk gp fp chunk).offset = piece.objectOffset ∧
      (Chunks.shiftChunk gp fp chunk).bytes = piece.bytes ∧
      savedAddress state.regSaveArea (Chunks.shiftChunk gp fp chunk).location
        (Chunks.shiftChunk gp fp chunk).bytes = some (pieceAddress state piece) := by
  rcases chunk with ⟨objectOffset, count, location⟩
  cases location with
  | gp register => exact toPiece_shift_gp register gpCursor fits
  | vector index offset =>
      rcases fits with ⟨capacity, size⟩
      refine ⟨⟨objectOffset, count, .fp, 16 * index + offset⟩, rfl, rfl, rfl, ?_⟩
      simp only [Chunks.shiftChunk, savedAddress, capacity, size, and_self, ↓reduceIte,
        pieceAddress, fpCursor]
      congr 1
      omega
  | x87 index => cases fits

private theorem mapM_matching {state : VaList} {gp fp : Nat} {relative : List Chunk}
    (gpCursor : state.gpOffset = 8 * gp) (fpCursor : state.fpOffset = 48 + 16 * fp)
    (fits : ∀ chunk ∈ relative, RelativeSlotFits gp fp chunk) :
    ∃ output, relative.mapM toPiece = .ok output ∧
      pieceAssignment state output (relative.map (Chunks.shiftChunk gp fp)) = true := by
  induction relative with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons head tail ih =>
      obtain ⟨piece, converted, headOffset, headSize, headAddress⟩ :=
        toPiece_shift gpCursor fpCursor (fits head (by simp))
      obtain ⟨output, restConverted, restMatched⟩ := ih (fun chunk member => fits chunk (by simp [member]))
      refine ⟨piece :: output, ?_, ?_⟩
      · simp only [List.mapM_cons, converted, restConverted]
        rfl
      · apply (pieceAssignment_iff _ _ _).mpr
        intro selected member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨Chunks.shiftChunk gp fp head, by simp, headOffset, headSize, headAddress⟩
        · obtain ⟨chunk, included, facts⟩ := (pieceAssignment_iff _ _ _).mp restMatched selected member
          exact ⟨chunk, by simp only [List.map_cons, List.mem_cons]; exact Or.inr included, facts⟩

/-- Actual production relative success determines actual pieces and every
matching shifted physical address, without an output/storage premise. -/
theorem pieces_matching {state : VaList} {object : Object} {relative : List Chunk}
    {gp fp : Nat} (gpCursor : state.gpOffset = 8 * gp)
    (fpCursor : state.fpOffset = 48 + 16 * fp)
    (computed : chunks object gpArguments 0 0 = .ok relative)
    (fits : ∀ chunk ∈ relative, RelativeSlotFits gp fp chunk) :
    ∃ output, pieces object = .ok output ∧
      pieceAssignment state output (relative.map (Chunks.shiftChunk gp fp)) = true := by
  obtain ⟨output, converted, matched⟩ := mapM_matching gpCursor fpCursor fits
  refine ⟨output, ?_, matched⟩
  rw [pieces_eq_mapM, computed]
  exact converted

/-- Construct the existing executable reconstruction placement. Whole-byte
coverage remains explicit, separately from physical address matching. -/
def registerPlacement {state : VaList} {object : Object} {relative : List Chunk}
    {output : List Piece} {gp fp : Nat}
    (gpCursor : state.gpOffset = 8 * gp) (fpCursor : state.fpOffset = 48 + 16 * fp)
    (capacity : gp + gpCount object ≤ 6)
    (computed : chunks object gpArguments 0 0 = .ok relative)
    (fits : ∀ chunk ∈ relative, RelativeSlotFits gp fp chunk)
    (converted : pieces object = .ok output) (covered : fullCoverage object.size output = true) :
    RegisterPlacement state object := by
  refine ⟨gp, fp, relative.map (Chunks.shiftChunk gp fp), output, gpCursor, fpCursor,
    Chunks.chunks_shift gp fp capacity computed, converted, ?_, covered⟩
  obtain ⟨actual, actualConverted, matched⟩ := pieces_matching gpCursor fpCursor computed fits
  have same : actual = output := Except.ok.inj (actualConverted.symm.trans converted)
  subst actual
  exact matched

end Silmaril.Compiler.Native.Varargs.Placement

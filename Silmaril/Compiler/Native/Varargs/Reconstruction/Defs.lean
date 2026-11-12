module

public import Silmaril.Compiler.Native.Varargs.Defs
public import Silmaril.Machine.SystemV.Abi.Representation.Defs
/-! Concrete observations for the native LP64 variadic save area. This reader
uses production `pieces` and `VaList.next`, but does not execute the emitted
MIR loads/stores or infer native address arithmetic from natural arithmetic. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Varargs.Reconstruction

open Silmaril.Cerberus.NativeTypes (Bytes)
open Silmaril.Machine.SystemV.Abi

/-- A permission-checked read from actual process memory. -/
def memoryBytes (state : Ffi.State) (address count : Nat) : Option Bytes :=
  (state.machine.memory.readBytes address count).map
    (List.map fun byte => UInt8.ofNat byte.toNat)

/-- Physical slots written by the entry emitter: six GP words, followed by
eight complete sixteen-byte XMM slots. Other vector registers and x87 have no
location in this save area. -/
def savedAddress (base : Nat) (location : Location) (count : Nat) : Option Nat :=
  match location with
  | .gp register =>
      if register ∈ gpArguments ∧ count ≤ 8 then
        some (base + 8 * gpArguments.idxOf register)
      else none
  | .vector index offset =>
      if index < 8 ∧ offset + count ≤ 16 then some (base + 48 + 16 * index + offset)
      else none
  | .x87 _ => none

/-- The actual saved memory observes the entry register bytes for every
permitted subread of a physical slot. Establishing this predicate from the
emitted prologue is a separate execution theorem. -/
def physicalSaveAreaAt (entry saved : Ffi.State) (base : Nat) : Prop :=
  ∀ location count address, savedAddress base location count = some address →
    memoryBytes saved address count = Ffi.locationBytes entry location count

/-- Exactly the source-address expression in native `va_arg`. -/
def pieceAddress (state : VaList) (piece : Piece) : Nat :=
  state.regSaveArea +
    (match piece.bank with | .gp => state.gpOffset | .fp => state.fpOffset) + piece.saveOffset

def covers (piece : Piece) (index : Nat) : Bool :=
  decide (piece.objectOffset ≤ index ∧ index < piece.objectOffset + piece.bytes)

/-- A finite placement check, containing no value or storage premise. Each
production relative piece must denote a genuine shifted ABI chunk at exactly
the physical save address used by the reader. -/
def pieceAssignment (state : VaList) (pieces : List Piece) (assigned : List Chunk) : Bool :=
  pieces.all fun piece => assigned.any fun chunk =>
    chunk.offset == piece.objectOffset && chunk.bytes == piece.bytes &&
      savedAddress state.regSaveArea chunk.location chunk.bytes == some (pieceAddress state piece)

/-- Full-byte coverage is sufficient for equality to the original encoding.
NO_CLASS holes need a weaker, compositional padding-preservation theorem. -/
def fullCoverage (size : Nat) (pieces : List Piece) : Bool :=
  (List.range size).all fun index => pieces.any (covers · index)

/-- An independently checkable bridge between actual production chunk outputs.
The general loop-equivariance theorem is deliberately not assumed here. -/
structure RegisterPlacement (state : VaList) (object : Object) where
  gp : Nat
  fp : Nat
  assigned : List Chunk
  relative : List Piece
  gpCursor : state.gpOffset = 8 * gp
  fpCursor : state.fpOffset = 48 + 16 * fp
  chunksComputed : chunks object gpArguments gp fp = .ok assigned
  piecesComputed : pieces object = .ok relative
  matched : pieceAssignment state relative assigned = true
  covered : fullCoverage object.size relative = true

/-- Select an actual piece and read its source bytes. Uncovered destination
bytes retain the zero initialization used by the native lowerer. -/
def pieceByte (saved : Ffi.State) (state : VaList) (pieces : List Piece)
    (index : Nat) : Option UInt8 := do
  match pieces.find? (covers · index) with
  | none => return 0
  | some piece =>
      let bytes ← memoryBytes saved (pieceAddress state piece) piece.bytes
      bytes[index - piece.objectOffset]?

def reconstruct (saved : Ffi.State) (state : VaList) (pieces : List Piece)
    (size : Nat) : Option Bytes :=
  (List.range size).mapM (pieceByte saved state pieces)

/-- Executable reads selected by the actual cursor operation, including whole
mixed-bank rollback and the aligned overflow branch. This is a byte-level
specification, not a claim that MIR or x86 execution implements it. -/
def readArgument (saved : Ffi.State) (state : VaList) (object : Object) :
    Option (Bytes × VaList) := do
  let (source, next) := state.next object
  let bytes ← match source with
    | .registers _ _ => do
        let relative ← (pieces object).toOption
        reconstruct saved state relative object.size
    | .stack address => memoryBytes saved address object.size
  return (bytes, next)

end Silmaril.Compiler.Native.Varargs.Reconstruction

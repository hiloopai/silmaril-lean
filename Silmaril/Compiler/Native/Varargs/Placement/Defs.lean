module

public import Silmaril.Compiler.Native.Varargs.Reconstruction.Defs
public import Silmaril.Machine.SystemV.Abi.Chunks.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Varargs.Placement
open Silmaril.Machine.SystemV.Abi

/-- Only physical slot bounds on actual relative output chunks. This contains
no pieces, shifted output list, reconstructed bytes, or memory observation. -/
def RelativeSlotFits (gp fp : Nat) (chunk : Chunk) : Prop :=
  match chunk.location with
  | .gp register => register ∈ gpArguments ∧
      gp + gpArguments.idxOf register < 6 ∧ chunk.bytes ≤ 8
  | .vector index offset => fp + index < 8 ∧ offset + chunk.bytes ≤ 16
  | .x87 _ => False

/-- The exact pointwise conversion used by production `pieces`. -/
def toPiece (chunk : Chunk) : Except String Piece :=
  match chunk.location with
  | .gp register => .ok ⟨chunk.offset, chunk.bytes, .gp, 8 * gpArguments.idxOf register⟩
  | .vector index offset => .ok ⟨chunk.offset, chunk.bytes, .fp, 16 * index + offset⟩
  | .x87 _ => .error "x87 variadic objects are passed in the overflow area"

end Silmaril.Compiler.Native.Varargs.Placement

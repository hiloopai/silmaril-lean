module

public import Silmaril.Wasm.Binary.Core.OpcodesProps
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Converses of the `0xFD` opcode lookups

`prefixFDOp?`, `vecMemOp?`, `vecMemLaneOp?` and `vecLaneOp?` (`OpcodesProps.lean`)
return only entries of their tables, so the vector reader can use them directly. -/

namespace Silmaril.Wasm.Binary.Core

set_option maxRecDepth 4096 in
/-- Every sub-opcode of the table is below `512`; the bound lets the proof enumerate
them (a `split` over the whole match is too slow). -/
theorem prefixFDOp?_spec {n : Nat} {i : Wasm.Instr} (hn : n < 512) (h : prefixFDOp? n = some i) :
    PrefixFDOp n i := by
  interval_cases n <;> first | (cases h; constructor) | cases h

theorem vecMemOp?_spec {n : Nat} {mk : MemIdx → MemArg → Wasm.Instr} (h : vecMemOp? n = some mk) :
    VecMemOp n mk := by
  unfold vecMemOp? at h
  split at h <;> first | (cases h; constructor) | cases h

theorem vecMemLaneOp?_spec {n : Nat} {mk : MemIdx → MemArg → LaneIdx → Wasm.Instr}
    (h : vecMemLaneOp? n = some mk) : VecMemLaneOp n mk := by
  unfold vecMemLaneOp? at h
  split at h <;> first | (cases h; constructor) | cases h

theorem vecLaneOp?_spec {n : Nat} {mk : LaneIdx → Wasm.Instr} (h : vecLaneOp? n = some mk) :
    VecLaneOp n mk := by
  unfold vecLaneOp? at h
  split at h <;> first | (cases h; constructor) | cases h

end Silmaril.Wasm.Binary.Core

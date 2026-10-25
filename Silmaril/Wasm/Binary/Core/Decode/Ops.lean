module

public import Silmaril.Wasm.Binary.Core.OpcodesProps
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Converses of the opcode lookups

`plainOp?`, `memOp?` and `prefixFCOp?` (`OpcodesProps.lean`) return only entries of
their tables, so the decoder can use them as readers: one lemma per table, by cases
over the opcode, instead of one proof case per opcode. -/

namespace Silmaril.Wasm.Binary.Core

set_option maxRecDepth 4096 in
theorem plainOp?_spec {op : UInt8} {i : Wasm.Instr} (h : plainOp? op = some i) :
    PlainOp op i := by
  have hlt := op.toNat_lt
  generalize hn : op.toNat = n at hlt
  obtain rfl : op = UInt8.ofNat n := UInt8.toNat_inj.mp (by simp [← hn])
  interval_cases n <;> first | (cases h; constructor) | cases h

set_option maxRecDepth 4096 in
theorem memOp?_spec {op : UInt8} {mk : MemIdx → MemArg → Wasm.Instr} (h : memOp? op = some mk) :
    MemOp op mk := by
  have hlt := op.toNat_lt
  generalize hn : op.toNat = n at hlt
  obtain rfl : op = UInt8.ofNat n := UInt8.toNat_inj.mp (by simp [← hn])
  interval_cases n <;> first | (cases h; constructor) | cases h

theorem prefixFCOp?_spec {n : Nat} {i : Wasm.Instr} (h : prefixFCOp? n = some i) :
    PrefixFCOp n i := by
  unfold prefixFCOp? at h
  split at h <;> first | (cases h; constructor) | cases h

theorem prefixFBOp?_spec {n : Nat} {i : Wasm.Instr} (h : prefixFBOp? n = some i) :
    PrefixFBOp n i := by
  unfold prefixFBOp? at h
  split at h <;> first | (cases h; constructor) | cases h

end Silmaril.Wasm.Binary.Core

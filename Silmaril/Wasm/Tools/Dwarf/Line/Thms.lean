module

public import Silmaril.Wasm.Tools.Dwarf.Line.Defs
import Silmaril.Proofs.Wasm.Tools.Dwarf.Line

/-!
# The line program reader and the lookup: theorems

* `specialRegs_spec`: **a special opcode (DWARF 5 §6.2.5.1) with one operation per
  instruction advances the address by `minimum_instruction_length × ((op − opcode_base) /
  line_range)` (modulo the address size, gimli's `add_sized`), resets `op_index`, and sets the
  line to `line + line_base + (op − opcode_base) % line_range`** (floored at 0, gimli's
  saturating decrement), leaving the other registers; `runProgram` applies it for every
  opcode at or above `opcode_base`.
* `binarySearch_spec`: **Rust's `binary_search_by` as `binarySearch` implements it (used by
  `findLocation` over sequences and rows, by the unit, function and inlined-frame lookups):
  on an array sorted for the comparison, `ok i` is an index of an equal element, and
  `error j` is the index where every element before is less and every element from it is
  greater.**

The header reader, the other opcodes and the sequence bookkeeping are tested against
addr2line 0.27.1 (`tools/wasm-tools/tests/addr2line/differential.sh`), not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Dwarf

/-- **A special opcode** (one operation per instruction, no overflow). -/
theorem specialRegs_spec (h : LineHeader) (r : Regs) (op : Nat) (hm : h.maxOps = 1)
    (ht : r.tombstone = false)
    (hadv : h.minInstLen * ((op - h.opcodeBase) / h.lineRange) < 2 ^ 64)
    (hov : r.address + h.minInstLen * ((op - h.opcodeBase) / h.lineRange) < 2 ^ 64)
    (hl : r.line + (h.lineBase + ((op - h.opcodeBase) % h.lineRange : Nat)) < 2 ^ 64) :
    ∃ r', specialRegs h r op = .ok r' ∧
      r'.address = (r.address + h.minInstLen * ((op - h.opcodeBase) / h.lineRange)) % 2 ^ (8 * h.addressSize) ∧
      r'.opIndex = 0 ∧
      r'.line = (r.line + (h.lineBase + ((op - h.opcodeBase) % h.lineRange : Nat))).toNat ∧
      r'.file = r.file ∧ r'.column = r.column ∧ r'.tombstone = r.tombstone ∧ r'.endSeq = r.endSeq :=
  Silmaril.Proofs.Wasm.Tools.Dwarf.specialRegs_spec h r op hm ht hadv hov hl

/-- **`binarySearch` is a binary search** on an array sorted for the comparison. -/
theorem binarySearch_spec {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering)
    (hs : ∀ i j, i ≤ j → j < xs.size → ordRank (cmp xs[i]!) ≤ ordRank (cmp xs[j]!)) (hn : xs.size ≤ 2 ^ 64) :
    match binarySearch xs cmp with
    | .ok i => i < xs.size ∧ cmp xs[i]! = .eq
    | .error j => j ≤ xs.size ∧ (∀ i, i < j → cmp xs[i]! = .lt) ∧
        (∀ i, j ≤ i → i < xs.size → cmp xs[i]! = .gt) :=
  Silmaril.Proofs.Wasm.Tools.Dwarf.binarySearch_spec xs cmp hs hn

end Silmaril.Wasm.Tools.Dwarf

end

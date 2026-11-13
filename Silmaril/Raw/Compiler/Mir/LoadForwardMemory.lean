module

public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
meta import Mathlib.Tactic.IntervalCases

/-! # Full-width read after write for Mir load forwarding

The full 64-bit stored value is read without truncation or extension. Both accesses
use Lir's natural-number address convention, without pointer wraparound. -/

@[expose] public section

namespace Silmaril.Compile.Mir.LoadForward

open Silmaril.Machine

theorem readLE_writeLE8 (bytes : Nat → Lir.Byte) (a : Nat) (v : Lir.Word) :
    Lir.readLE (Lir.writeLE bytes a 8 v) a 8 = v := by
  ext i hi
  interval_cases i <;>
    simp [Lir.readLE, Lir.writeLE, LittleEndian.wordByte, Nat.add_assoc,
      BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]

/-- A successful 64-bit store establishes a successful read of that exact value. -/
theorem load_store8 {m m' : Lir.Memory} {a : Nat} {v : Lir.Word}
    (h : m.store .b8 a v = some m') : m'.load .b8 .zero a = some v := by
  unfold Lir.Memory.store at h
  split at h
  · rename_i hb
    cases h
    simp only [Lir.Memory.load, Lir.Memory.InBounds, Lir.Width.bytes] at hb ⊢
    simp [hb, Lir.extend, readLE_writeLE8]
  · cases h

end Silmaril.Compile.Mir.LoadForward

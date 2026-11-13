module

public import Silmaril.Compiler.Mir.InterpMemUpdate.Defs
public import Init.Data.Range.Lemmas

@[expose] public section

/-! # Little-endian reads in the executable and semantic memories -/

namespace Silmaril.Compile.Mir.Interp.Mem

open Silmaril.Machine

private theorem readLE_eq_foldl (m : Mem) (a n : Nat) :
    m.readLE a n = (List.range n).foldl
      (fun v i => v ||| ((m.getByte (a+i)).toUInt64 <<< (8*i).toUInt64)) 0 := by
  simp [readLE, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range']

/-- All four access widths assemble the same little-endian word. -/
theorem readLE_toLir (m : Mem) (a : Nat) (w : Lir.Width) :
    (m.readLE a w.bytes).toBitVec = Lir.readLE m.toLir.bytes a w.bytes := by
  rw [readLE_eq_foldl]
  cases w <;>
    simp [Lir.Width.bytes, List.range_succ, Lir.readLE,
      toLir, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq',
      BitVec.shiftLeft_or_distrib, BitVec.or_assoc,
      Nat.add_assoc, ← UInt8.toBitVec_ofNat']

/-- A successful semantic load reads the interpreter's loaded value. -/
theorem load_toLir (m : Mem) (w : Lir.Width) (e : Lir.Ext) (a : Nat) :
    m.toLir.load w e a =
      if a + w.bytes ≤ m.size then some (m.load w e a).toBitVec else none := by
  simp only [Lir.Memory.load, Lir.Memory.InBounds, toLir]
  congr 1
  rw [load, extend_eq, readLE_toLir]
  rfl

end Silmaril.Compile.Mir.Interp.Mem

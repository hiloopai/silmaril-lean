module

public import Silmaril.X86.BlockCert.Ext8.Defs

/-!
# Table-fold stencil

A **table fold** consumes a byte buffer one byte at a time with a lookup table of 64-bit
entries: `c ← (c >> 8) ^ T[(c ^ b) & 0xff]`. This is the inner step of the byte-wise reflected
CRC (zlib `crc32_z` without braiding) and of every "shift and look up" checksum. A census of
the lifter's rejections calls the family `table-fold`.

* `TableAt mem tbl n T`: the `n` entries `T 0, …, T (n-1)` are loadable 8-byte words at
  `tbl, tbl + 8, …` (a read-only global table; nothing here writes it, so it is framed for free);
* `step T c b`, `fold T c bs`: the pure step and the fold;
* `stepL a d p k tbl` and `stepAddL a d p k j tbl`: **the machine stencil**, the five
  instructions gcc -O2 emits for one step with the running value in `a`, scratch `d` and the
  buffer pointer `p` (`mov a,d; xor k(p),a8; movzbl a8,a; shr $8,d; xor tbl(,a,8),d`; the result
  is in `d`), and the same with a pointer increment `add $j,p` after the byte load (gcc's
  unrolled loops place it there);
* `bytesAt mem a n`: the `n` bytes at `a` as a list (missing bytes read as `0`; a `Readable`
  precondition rules that out).

The run lemmas (`stepL_run`, `stepAddL_run`: one stencil instance computes `step`) are in
`Stencils/TableFold/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Stencils.TableFold

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.X86.Ext (Mem loadN)
open Silmaril.Process (Memory)
open Silmaril.X86.BlockCert8 (LI)

/-- A table of `n` eight-byte entries at `tbl`. -/
def TableAt (mem : Memory) (tbl n : Nat) (T : Nat → Word) : Prop :=
  ∀ i < n, loadN mem (BitVec.ofNat 64 (tbl + 8 * i)) 8 = some (T i)

/-- The table index of one step: the low byte of the running value xor the input byte. -/
def index (c : Word) (b : Byte) : Nat := (c.setWidth 8 ^^^ b).toNat

/-- **One table-fold step.** -/
def step (T : Nat → Word) (c : Word) (b : Byte) : Word := (c >>> 8) ^^^ T (index c b)

/-- The table fold of a byte list. -/
def fold (T : Nat → Word) (c : Word) (bs : List Byte) : Word := bs.foldl (step T) c

/-- The byte at `a + i` (absent bytes read as `0`). -/
def byteAt (mem : Memory) (a i : Nat) : Byte := (mem.bytes.get? (a + i)).getD 0

/-- The `n` bytes at `a` (absent bytes read as `0`). -/
def bytesAt (mem : Memory) (a n : Nat) : List Byte := (List.range n).map (byteAt mem a)

/-- The table operand `tbl(, a, 8)`. -/
def tblMem (a : Reg) (ha : a ≠ .rsp) (tbl : BitVec 32) : Mem := Mem.ofIndex (some ⟨a, 3#2, ha⟩) tbl

/-- **The step stencil**: `mov a,d; xor k(p),a8; movzbl a8,a; shr $8,d; xor tbl(,a,8),d`. -/
def stepL (a d p : Reg) (k tbl : BitVec 32) (ha : a ≠ .rsp := by decide) : List LI :=
  [(.base (.mov .q (.reg d) a), 3),
   (.new (.aluR .xor (.low a) (.mem (Mem.ofReg p none k))), if k = 0 then 2 else 3),
   (.base (.movx false .d .b a (.reg a)), 3),
   (.base (.shift .q .shr (.reg d) (.imm 8#8)), 4),
   (.base (.aluR .q .xor d (.mem (tblMem a ha tbl))), 8)]

/-- The step stencil with `add $j,p` after the byte load. -/
def stepAddL (a d p : Reg) (k tbl : BitVec 32) (j : BitVec 8) (ha : a ≠ .rsp := by decide) :
    List LI :=
  [(.base (.mov .q (.reg d) a), 3),
   (.new (.aluR .xor (.low a) (.mem (Mem.ofReg p none k))), if k = 0 then 2 else 3),
   (.base (.aluI8 .q .add (.reg p) j), 4),
   (.base (.movx false .d .b a (.reg a)), 3),
   (.base (.shift .q .shr (.reg d) (.imm 8#8)), 4),
   (.base (.aluR .q .xor d (.mem (tblMem a ha tbl))), 8)]

end Silmaril.X86.Stencils.TableFold

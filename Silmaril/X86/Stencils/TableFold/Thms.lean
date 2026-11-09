module

public import Silmaril.X86.Stencils.TableFold.Defs
public import Silmaril.X86.BlockCert.Ext8.Thms
public import Silmaril.X86.Stencils.ByteLoop.Thms
import Silmaril.Proofs.X86.Stencils.TableFold.Run

/-!
# Table-fold stencil: theorems

* `stepL_run`, `stepAddL_run`: **one instance of the machine stencil computes `step`**. From a
  state where the byte at `p + k` and the table are loadable, the instructions retire in
  sequence (so they can head any `Ext8` block listing, `run8 (stepL … ++ rest)`), keep the
  memory, leave `step T c b` in `d` and the table index in `a`, and keep every other register;
  `stepAddL` also advances `p` by `j`;
* `fold_append`, `fold_cons`, `fold_nil`: the fold over concatenations (an `n`-times unrolled
  loop body is `n` steps, so one lemma covers every unrolling factor).

The stencil is stated for any registers `a ≠ d`, `p ∉ {a, d}`, any displacement `k`, and any
table address below `2^31` (gcc's `disp32` table operand in non-PIC code).
-/

@[expose] public section

namespace Silmaril.X86.Stencils.TableFold

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Mem loadN)
open Silmaril.X86.BlockCert8

theorem stepL_run {a d p : Reg} {k tbl : BitVec 32} {ha : a ≠ .rsp}
    (had : a ≠ d) (hpd : p ≠ d) (htbl : tbl.toNat < 2 ^ 31)
    {T : Nat → Word} {b : Byte} (rest : List LI) (m : MState)
    (hb : loadN m.memory (m.core.read p + k.signExtend 64) 1 = some (BitVec.ofNat 64 b.toNat))
    (hT : TableAt m.memory tbl.toNat 256 T) :
    ∃ c, run8 (stepL a d p k tbl ha ++ rest) m = run8 rest ⟨c, m.memory⟩ ∧
      c.rip = m.core.rip + BitVec.ofNat 64 (if k = 0 then 20 else 21) ∧
      c.read d = step T (m.core.read a) b ∧
      c.read a = BitVec.ofNat 64 (index (m.core.read a) b) ∧
      ∀ r, r ≠ a → r ≠ d → c.read r = m.core.read r :=
  Silmaril.Proofs.X86.Stencils.TableFold.stepL_run had hpd htbl rest m hb hT

theorem stepAddL_run {a d p : Reg} {k tbl : BitVec 32} {j : BitVec 8} {ha : a ≠ .rsp}
    (had : a ≠ d) (hpa : p ≠ a) (hpd : p ≠ d) (htbl : tbl.toNat < 2 ^ 31)
    {T : Nat → Word} {b : Byte} (rest : List LI) (m : MState)
    (hb : loadN m.memory (m.core.read p + k.signExtend 64) 1 = some (BitVec.ofNat 64 b.toNat))
    (hT : TableAt m.memory tbl.toNat 256 T) :
    ∃ c, run8 (stepAddL a d p k tbl j ha ++ rest) m = run8 rest ⟨c, m.memory⟩ ∧
      c.rip = m.core.rip + BitVec.ofNat 64 (if k = 0 then 24 else 25) ∧
      c.read d = step T (m.core.read a) b ∧
      c.read a = BitVec.ofNat 64 (index (m.core.read a) b) ∧
      c.read p = m.core.read p + j.signExtend 64 ∧
      ∀ r, r ≠ a → r ≠ d → r ≠ p → c.read r = m.core.read r :=
  Silmaril.Proofs.X86.Stencils.TableFold.stepAddL_run had hpa hpd htbl rest m hb hT

@[simp] theorem fold_nil (T : Nat → Word) (c : Word) : fold T c [] = c := rfl

@[simp] theorem fold_cons (T : Nat → Word) (c : Word) (b : Byte) (bs : List Byte) :
    fold T c (b :: bs) = fold T (step T c b) bs := rfl

theorem fold_append (T : Nat → Word) (c : Word) (xs ys : List Byte) :
    fold T c (xs ++ ys) = fold T (fold T c xs) ys := List.foldl_append

theorem index_lt (c : Word) (b : Byte) : index c b < 256 := (c.setWidth 8 ^^^ b).isLt

/-- The table operand's address at index `i`. -/
theorem tbl_addr {a : Reg} {ha : a ≠ .rsp} {tbl : BitVec 32} (htbl : tbl.toNat < 2 ^ 31)
    (s : State) {i : Nat} (hi : i < 256) (hs : s.read a = BitVec.ofNat 64 i) :
    (tblMem a ha tbl).addr s 0#64 = BitVec.ofNat 64 (tbl.toNat + 8 * i) :=
  Silmaril.Proofs.X86.Stencils.TableFold.tbl_addr htbl s hi hs

/-- `movzbl` after the byte xor gives the table index. -/
theorem movzb_index {x c : Word} {b : Byte}
    (h : x.setWidth 8 = c.setWidth 8 ^^^ (BitVec.ofNat 64 b.toNat).setWidth 8) :
    (x.setWidth 8).setWidth 64 = BitVec.ofNat 64 (index c b) :=
  Silmaril.Proofs.X86.Stencils.TableFold.movzb_index h

/-- One more byte of `bytesAt`. -/
theorem bytesAt_succ (mem : Silmaril.Process.Memory) (a n : Nat) :
    bytesAt mem a (n + 1) = bytesAt mem a n ++ [byteAt mem a n] := by
  simp [bytesAt, List.range_succ]

/-- A readable buffer byte loads as `byteAt`. -/
theorem load_byte {mem : Silmaril.Process.Memory} {a n i : Nat}
    (hr : Silmaril.X86.Stencils.ByteLoop.Readable mem a n) (hi : i < n) {w : Word}
    (hw : w = BitVec.ofNat 64 a + BitVec.ofNat 64 i) :
    loadN mem w 1 = some (BitVec.ofNat 64 (byteAt mem a i).toNat) := by
  obtain ⟨hlt, hp, hs⟩ := hr i hi
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
  have hA : w.toNat = a + i := by
    subst hw
    simp only [Silmaril.Process.addressLimit] at hlt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt hlt]
  rw [Silmaril.X86.Stencils.ByteLoop.loadN_one (b := b) (by rw [hA]; exact hp)
    (by rw [hA]; exact hb), byteAt, hb]
  rfl

end Silmaril.X86.Stencils.TableFold

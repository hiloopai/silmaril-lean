module

public import Silmaril.X86.Stencils.TableFold.Defs
public import Silmaril.X86.BlockCert.Ext8.Thms

/-!
# The table-fold step stencil runs as `step`

`stepL_run`, `stepAddL_run`: from a state where the buffer byte at `p + k` and the table are
loadable, the five (six) stencil instructions retire in sequence, keep the memory, put
`step T c b` in `d` and the table index in `a`, and keep every other register (`p` advances by
`j` in the `add` variant).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Stencils.TableFold

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Mem loadN)
open Silmaril.Process (Memory)
open Silmaril.X86.BlockCert8
open Silmaril.X86.Stencils.TableFold

theorem tbl_addr {a : Reg} {ha : a ≠ .rsp} {tbl : BitVec 32} (htbl : tbl.toNat < 2 ^ 31)
    (s : State) {i : Nat} (_hi : i < 256) (hs : s.read a = BitVec.ofNat 64 i) :
    (tblMem a ha tbl).addr s 0#64 = BitVec.ofNat 64 (tbl.toNat + 8 * i) := by
  have hmsb : tbl.msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  apply BitVec.eq_of_toNat_eq
  simp only [tblMem, Mem.ofIndex, Mem.addr, Silmaril.X86.Ext.Base.value, Option.map_some,
    Option.getD_some, Silmaril.X86.Ext.Index.value, hs, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, BitVec.signExtend_eq_setWidth_of_msb_false hmsb, BitVec.toNat_setWidth]
  simp
  omega

theorem index_lt (c : Word) (b : Byte) : index c b < 256 := (c.setWidth 8 ^^^ b).isLt

theorem movzb_index {x : Word} {c : Word} {b : Byte}
    (h : x.setWidth 8 = c.setWidth 8 ^^^ (BitVec.ofNat 64 b.toNat).setWidth 8) :
    (x.setWidth 8).setWidth 64 = BitVec.ofNat 64 (index c b) := by
  rw [h, Silmaril.X86.Stencils.ByteLoop.byte_roundtrip]
  apply BitVec.eq_of_toNat_eq
  simp [index]

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
      ∀ r, r ≠ a → r ≠ d → r ≠ p → c.read r = m.core.read r := by
  obtain ⟨c1, h1, e1⟩ := mov_q m.core m.memory 3 d a
  obtain ⟨c2, h2, r2, l2, o2⟩ := xor8_mem c1 m.memory (if k = 0 then 2 else 3) a p k _
    (by simp only [e1.2, hpd, ite_false]; exact hb)
  obtain ⟨c3, h3, e3⟩ := add_q_i8 c2 m.memory 4 p j
  obtain ⟨c4, h4, e4⟩ := movzb c3 m.memory 3 a
  obtain ⟨c5, h5, e5⟩ := shr_q c4 m.memory 4 d 8#8 (by decide)
  have hidx : c4.read a = BitVec.ofNat 64 (index (m.core.read a) b) := by
    simp only [e4.2, e3.2, Ne.symm hpa, ite_true, ite_false]
    exact movzb_index (by rw [l2]; simp only [e1.2, had, ite_false])
  obtain ⟨c6, h6, e6⟩ := xor_q_mem c5 m.memory 8 d (tblMem a ha tbl) (T (index (m.core.read a) b))
    rfl (by
      rw [tbl_addr htbl c5 (index_lt _ _) (by simp only [e5.2, had, ite_false]; exact hidx)]
      exact hT _ (index_lt _ _))
  refine ⟨c6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stepAddL, List.cons_append]
    rw [run8_cons_of h1 e1.1, run8_cons_of h2 r2, run8_cons_of h3 e3.1, run8_cons_of h4 e4.1,
      run8_cons_of h5 e5.1, run8_cons_of h6 e6.1, List.nil_append]
  · rw [e6.1, e5.1, e4.1, e3.1, r2, e1.1]
    split <;> simp [BitVec.add_assoc]
  · simp only [e6.2, e5.2, e4.2, e3.2, ite_true, Ne.symm had, Ne.symm hpd, ite_false, o2 d (Ne.symm had)]
    simp only [e1.2, ite_true]
    rfl
  · simp only [e6.2, e5.2, had, ite_false]; exact hidx
  · simp only [e6.2, e5.2, e4.2, e3.2, hpd, hpa, ite_true, ite_false, o2 p hpa]
    simp only [e1.2, hpd, ite_false]
  · intro r hra hrd hrp
    simp only [e6.2, e5.2, e4.2, e3.2, hra, hrd, hrp, ite_false, o2 r hra]
    simp only [e1.2, hrd, ite_false]

theorem stepL_run {a d p : Reg} {k tbl : BitVec 32} {ha : a ≠ .rsp}
    (had : a ≠ d) (hpd : p ≠ d) (htbl : tbl.toNat < 2 ^ 31)
    {T : Nat → Word} {b : Byte} (rest : List LI) (m : MState)
    (hb : loadN m.memory (m.core.read p + k.signExtend 64) 1 = some (BitVec.ofNat 64 b.toNat))
    (hT : TableAt m.memory tbl.toNat 256 T) :
    ∃ c, run8 (stepL a d p k tbl ha ++ rest) m = run8 rest ⟨c, m.memory⟩ ∧
      c.rip = m.core.rip + BitVec.ofNat 64 (if k = 0 then 20 else 21) ∧
      c.read d = step T (m.core.read a) b ∧
      c.read a = BitVec.ofNat 64 (index (m.core.read a) b) ∧
      ∀ r, r ≠ a → r ≠ d → c.read r = m.core.read r := by
  obtain ⟨c1, h1, e1⟩ := mov_q m.core m.memory 3 d a
  obtain ⟨c2, h2, r2, l2, o2⟩ := xor8_mem c1 m.memory (if k = 0 then 2 else 3) a p k _
    (by simp only [e1.2, hpd, ite_false]; exact hb)
  obtain ⟨c4, h4, e4⟩ := movzb c2 m.memory 3 a
  obtain ⟨c5, h5, e5⟩ := shr_q c4 m.memory 4 d 8#8 (by decide)
  have hidx : c4.read a = BitVec.ofNat 64 (index (m.core.read a) b) := by
    simp only [e4.2, ite_true]
    exact movzb_index (by rw [l2]; simp only [e1.2, had, ite_false])
  obtain ⟨c6, h6, e6⟩ := xor_q_mem c5 m.memory 8 d (tblMem a ha tbl) (T (index (m.core.read a) b))
    rfl (by
      rw [tbl_addr htbl c5 (index_lt _ _) (by simp only [e5.2, had, ite_false]; exact hidx)]
      exact hT _ (index_lt _ _))
  refine ⟨c6, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stepL, List.cons_append]
    rw [run8_cons_of h1 e1.1, run8_cons_of h2 r2, run8_cons_of h4 e4.1,
      run8_cons_of h5 e5.1, run8_cons_of h6 e6.1, List.nil_append]
  · rw [e6.1, e5.1, e4.1, r2, e1.1]
    split <;> simp [BitVec.add_assoc]
  · simp only [e6.2, e5.2, e4.2, ite_true, Ne.symm had, ite_false, o2 d (Ne.symm had)]
    simp only [e1.2, ite_true]
    rfl
  · simp only [e6.2, e5.2, had, ite_false]; exact hidx
  · intro r hra hrd
    simp only [e6.2, e5.2, e4.2, hra, hrd, ite_false, o2 r hra]
    simp only [e1.2, hrd, ite_false]

end Silmaril.Proofs.X86.Stencils.TableFold

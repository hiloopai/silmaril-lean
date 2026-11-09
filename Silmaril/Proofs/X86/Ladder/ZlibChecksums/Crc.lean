module

public import Silmaril.X86.Ladder.ZlibChecksums.Spec.Defs
public import Silmaril.X86.Stencils.TableFold.Thms
public import Silmaril.X86.Stencils.AccumFold.Thms

/-!
# zlib checksums: proofs of the reference facts

* the CRC shift register is linear (`crcBit_xor`, `crcBits_xor`) and shifts out zero low
  bits (`crcBits_low_zero`), so one byte step is a shift and one table lookup
  (`crcByte_table`); on 64-bit words this is the table-fold stencil's `step` (`step_crcT`,
  `fold_crcT`);
* the transcribed table holds the polynomial entries (`crcTable_correct`, kernel `decide`) and
  a memory holding it satisfies the stencil's `TableAt` (`tableAt_of_readBytes`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Ext (loadN leValue)
open Silmaril.Process (Memory)
open Silmaril.X86.Stencils
open Silmaril.X86.Ladder.ZlibChecksums

theorem crcBit_xor (a b : BitVec 32) : crcBit (a ^^^ b) = crcBit a ^^^ crcBit b := by
  unfold crcBit
  rw [BitVec.getLsbD_xor, BitVec.ushiftRight_xor_distrib]
  cases a.getLsbD 0 <;> cases b.getLsbD 0 <;> simp only [Bool.xor_true, Bool.xor_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  · ac_rfl
  · ac_rfl
  · apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [BitVec.getLsbD_xor]
    cases (a >>> 1).getLsbD i <;> cases (b >>> 1).getLsbD i <;>
      cases (0xedb88320#32).getLsbD i <;> rfl

theorem crcBits_xor : ∀ k (a b : BitVec 32), crcBits k (a ^^^ b) = crcBits k a ^^^ crcBits k b
  | 0, _, _ => rfl
  | k + 1, a, b => by simp only [crcBits, crcBit_xor, crcBits_xor k]

theorem crcBits_low_zero : ∀ k (h : BitVec 32), (∀ j < k, h.getLsbD j = false) →
    crcBits k h = h >>> k
  | 0, h, _ => by simp [crcBits]
  | k + 1, h, hz => by
    have h0 : crcBit h = h >>> 1 := by
      have := hz 0 (by omega)
      simp only [crcBit, this, Bool.false_eq_true, ↓reduceIte]
    simp only [crcBits, h0]
    rw [crcBits_low_zero k (h >>> 1) (fun j hj => by
      rw [BitVec.getLsbD_ushiftRight]; exact hz (1 + j) (by omega)), ← BitVec.shiftRight_add, Nat.add_comm]

theorem split8 (x : BitVec 32) : x = (x &&& 0xff#32) ^^^ (x &&& 0xffffff00#32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  have h1 : ∀ i < 32, (Nat.testBit 255 i ^^ Nat.testBit 4294967040 i) = true := by decide
  have h2 : ∀ i < 32, (Nat.testBit 255 i && Nat.testBit 4294967040 i) = false := by decide
  have a := h1 i hi; have b := h2 i hi
  revert a b
  cases x.getLsbD i <;> cases Nat.testBit 255 i <;> cases Nat.testBit 4294967040 i <;> simp [hi]


theorem crcByte_table (c : BitVec 32) (b : BitVec 8) :
    crcByte c b = (c >>> 8) ^^^ crcEntry (c.setWidth 8 ^^^ b).toNat := by
  unfold crcByte crcEntry
  rw [split8 (c ^^^ b.setWidth 32), crcBits_xor, BitVec.xor_comm]
  have hz : ∀ j < 8, Nat.testBit 4294967040 j = false := by decide
  have ho : ∀ j < 24, Nat.testBit 4294967040 (8 + j) = true := by decide
  have hl : ∀ j < 32, Nat.testBit 255 j = decide (j < 8) := by decide
  congr 1
  · rw [crcBits_low_zero 8 _ (fun j hj => by
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hz j hj, Bool.and_false])]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_xor,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth]
    have hb : b.getLsbD (8 + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
    by_cases h : 8 + i < 32
    · simp [ho i (by omega), h]
    · have : c.getLsbD (8 + i) = false := BitVec.getLsbD_of_ge c _ (by omega)
      simp [this, h]
  · congr 1
    rw [BitVec.ofNat_toNat]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ofNat,
      BitVec.getLsbD_setWidth, hl i hi]
    by_cases h : i < 8 <;> simp [h, hi]
    have hb : b.getLsbD i = false := BitVec.getLsbD_of_ge b _ (by omega)
    simp [hb]

theorem step_crcT (c : BitVec 32) (b : Byte) :
    TableFold.step crcT (c.setWidth 64) b = (crcByte c b).setWidth 64 := by
  have hi : TableFold.index (c.setWidth 64) b = (c.setWidth 8 ^^^ b).toNat := by
    simp only [TableFold.index]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  rw [TableFold.step, hi, crcByte_table, crcT, BitVec.setWidth_xor]
  congr 1

theorem fold_crcT (c : BitVec 32) (bs : List Byte) :
    TableFold.fold crcT (c.setWidth 64) bs = (bs.foldl crcByte c).setWidth 64 := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => rw [TableFold.fold_cons, step_crcT, ih]; rfl

set_option maxRecDepth 100000 in
theorem crcTable_correct :
    ∀ i < 256, leValue ((crcTableBytes.drop (8 * i)).take 8) = (crcEntry i).toNat := by
  decide +kernel

theorem crcTableBytes_length : crcTableBytes.length = 2048 := by decide +kernel

theorem tableAt_of_readBytes {mem : Memory} {tbl : Nat}
    (h : mem.readBytes tbl 2048 = some crcTableBytes) : TableFold.TableAt mem tbl 256 crcT := by
  intro i hi
  have hr := Silmaril.Process.Memory.readBytes_sub_range h (offset := 8 * i) (len := 8)
    (by omega) (by omega)
  have hlim := Silmaril.Process.Memory.readWith_permitted h
  rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff] at hlim
  have hA : (BitVec.ofNat 64 (tbl + 8 * i)).toNat = tbl + 8 * i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := hlim.2.1; simp [Silmaril.Process.addressLimit] at this ⊢; omega
  rw [Silmaril.X86.Ext.loadN_of_readBytes (by rw [hA]; exact hr), crcTable_correct i hi, crcT]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

end Silmaril.Proofs.X86.Ladder.ZlibChecksums

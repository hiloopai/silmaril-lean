module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitTailB

/-!
# Proofs: rung 05 (first-fit) `malloc` — splitting a block (offset 55)

The block has room for `need` bytes and a remainder of at least 32: the remainder's header is
written at `b + 16 + need` (size, then next pointer), `b`'s size becomes `need`, and the final
link slot of the walked segment takes the remainder.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.FirstFit
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole
open Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitPost

/-- The operand `0x10(%rax,%rdi,1)`. -/
def mIdx : Silmaril.X86.Ext.Mem := ⟨.reg .rax, some ⟨.rdi, 0, by decide⟩, 0x10, fun h => by cases h⟩

theorem d58 : Silmaril.X86.Ext.decode ((mcode.drop 58).take 5) = some (.lea .q .r8 mIdx, 5) := by
  decide +kernel

/-! ## Word arithmetic of the split -/

theorem w_r8 (b : Block) (need : Nat) (hWF : b.WF) (hsp : need + 32 ≤ b.size) :
    b.addr + (BitVec.ofNat 64 need <<< (0 : BitVec 2).toNat) + BitVec.signExtend 64 (0x10 : BitVec 32) =
      (rem b need).addr := by
  obtain ⟨-, -, hb⟩ := hWF
  apply BitVec.eq_of_toNat_eq
  show _ = (b.addr + BitVec.ofNat 64 (16 + need)).toNat
  rw [show BitVec.signExtend 64 (0x10 : BitVec 32) = 16#64 by decide +kernel,
    show (0 : BitVec 2).toNat = 0 from rfl, BitVec.shiftLeft_zero]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := need) (by omega), Nat.mod_eq_of_lt (a := 16 + need) (by omega),
    Nat.mod_eq_of_lt (a := b.addr.toNat + need) (by omega)]
  rw [show (16 : Nat) % 2 ^ 64 = 16 from rfl]
  omega

theorem w_rdx (sz need : Nat) (hsp : need + 32 ≤ sz) (hsz : sz < 2 ^ 64) :
    Silmaril.X86.Ext.AluOp.resultN .sub
      (Silmaril.X86.Ext.AluOp.resultN .sub (BitVec.ofNat 64 sz) (BitVec.ofNat 64 need))
      (BitVec.signExtend 64 (0x10 : BitVec 8)) = BitVec.ofNat 64 (sz - need - 16) := by
  show (BitVec.ofNat 64 sz - BitVec.ofNat 64 need) - BitVec.signExtend 64 (0x10 : BitVec 8) = _
  rw [show BitVec.signExtend 64 (0x10 : BitVec 8) = 16#64 by decide +kernel]
  have hn : (BitVec.ofNat 64 need).toNat = need := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs : (BitVec.ofNat 64 sz).toNat = sz := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz]
  have h1 : BitVec.ofNat 64 need ≤ BitVec.ofNat 64 sz := by rw [BitVec.le_def, hn, hs]; omega
  have hd : (BitVec.ofNat 64 sz - BitVec.ofNat 64 need).toNat = sz - need := by
    rw [BitVec.toNat_sub_of_le h1, hn, hs]
  have h2 : (16#64 : Word) ≤ BitVec.ofNat 64 sz - BitVec.ofNat 64 need := by
    rw [BitVec.le_def, hd]; show 16 ≤ _; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le h2, hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  show sz - need - 16 = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The payload of the block, cut for the split. -/
theorem pay_split (b : Block) (need : Nat) (hWF : b.WF) (h16 : need % 16 = 0)
    (hsp : need + 32 ≤ b.size) :
    blockAny (b.addr.toNat + 16) b.size =
      (blockAny (b.addr.toNat + 16) need ∗ blockAny (rem b need).addr.toNat 8 ∗
        blockAny ((rem b need).addr + 8#64).toNat 8 ∗
        blockAny ((rem b need).addr.toNat + 16) (rem b need).size) := by
  obtain ⟨hra, hrWF⟩ := rem_facts b need hWF h16 hsp
  have h8 : ((rem b need).addr + 8#64).toNat = (rem b need).addr.toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by have := hrWF.2.2; omega)]
  rw [h8, hra, show b.size = need + (8 + (8 + (rem b need).size)) by
    show _ = need + (8 + (8 + (b.size - need - 16))); omega, blockAny_add, blockAny_add,
    blockAny_add]

/-- **Split the block.** -/
theorem tailC_split (S : Silmaril.X86.Sep.FnSpec) (hS : S.stack = 0) (x : S.Arg)
    (fl0 passed rest : List Block) (b : Block) (n nxt sp ret : Word) (hE : Exits S x n fl0)
    (f : Reg → Word) (fl : Flags) (hrax : f .rax = b.addr) (hrcx : f .rcx = nxt)
    (hrdx : f .rdx = BitVec.ofNat 64 b.size) (hrdi : f .rdi = BitVec.ofNat 64 (roundUp 16 n.toNat))
    (hrsi : f .rsi = lastSlot flAddr passed) (hrsp : f .rsp = sp) (hn4 : n.toNat ≤ 4096)
    (hfl : passed ++ b :: rest = fl0)
    (hsmall : ∀ c ∈ passed, c.size < roundUp 16 n.toNat)
    (hWF : b.WF) (hsp : roundUp 16 n.toNat + 32 ≤ b.size) (h16 : roundUp 16 n.toNat % 16 = 0) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 mcode) (St 0x401367 f fl (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
      hdrSeg rest nxt ∗ strue))
      (S.SysVPost x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hsz : b.size < 2 ^ 64 := by have := hWF.2.2; omega
  -- cut the payload and the walked segment's final slot
  refine SPEC.mem (M' := blockAny ((rem b (roundUp 16 n.toNat)).addr + 8#64).toNat 8 ∗
    (wordPt sp.toNat ret ∗ plistO flAddr passed ∗ wordPt (lastSlot flAddr passed).toNat b.addr ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) ∗
      blockAny (rem b (roundUp 16 n.toNat)).addr.toNat 8 ∗
      blockAny ((rem b (roundUp 16 n.toNat)).addr.toNat + 16) (rem b (roundUp 16 n.toNat)).size ∗
      hdrSeg rest nxt ∗ strue))
    (by rw [plist_last, pay_split b _ hWF h16 hsp]; ac_rfl) ?_
  -- sub %rdi, %rdx
  refine SPEC.trans (c_alu E (b := 0x401330) (code := mcode) (o := 55) (k := 3) (pc := 0x401367)
    (by decide) (fit 55 3) (op := .sub) (by decide) (r := .rdx) (q := .rdi) (by decide)
    (by decide) (by decide) d55) ?_
  -- lea 0x10(%rax,%rdi,1), %r8
  refine SPEC.trans (c_lea E (b := 0x401330) (code := mcode) (o := 58) (k := 5)
    (pc := 0x401367 + 3#64) (by decide) (fit 58 5) (dst := .r8) (by decide) d58
    (a := (rem b (roundUp 16 n.toNat)).addr) (fun st hregs next => by
      simp only [Silmaril.X86.Ext.Mem.addr, mIdx, Silmaril.X86.Ext.Base.value,
        Silmaril.X86.Ext.Index.value, Option.map_some, Option.getD_some]
      rw [hregs .rax (by decide), hregs .rdi (by decide)]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax, hrdi]
      exact w_r8 b _ hWF hsp)) ?_
  -- sub $0x10, %rdx
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := mcode) (o := 63) (k := 4)
    (pc := 0x401367 + 3#64 + 5#64) (by decide) (fit 63 4) (op := .sub) (by decide) (r := .rdx)
    (imm := 0x10) (by decide) d63) ?_
  -- mov %rcx, 0x8(%r8): the remainder's next pointer
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := mcode) (o := 67) (k := 4)
    (pc := 0x401367 + 3#64 + 5#64 + 4#64) (pc' := 0x401377) (by decide) (fit 67 4) (base := .r8)
    (src := .rcx) (by decide) (by decide) (by decide) (disp := 8) (entails_refl _) d67 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; rfl)) ?_
  -- mov %r8, %rcx
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := mcode) (o := 71) (k := 3) (pc := 0x401377)
    (by decide) (fit 71 3) (r := .rcx) (q := .r8) (by decide) (by decide) (by decide) d71) ?_
  -- mov %rdx, (%r8): the remainder's size
  refine SPEC.mem (M' := blockAny (rem b (roundUp 16 n.toNat)).addr.toNat 8 ∗ (wordPt sp.toNat ret ∗ plistO flAddr passed ∗
      wordPt (lastSlot flAddr passed).toNat b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) ∗
      blockAny ((rem b (roundUp 16 n.toNat)).addr.toNat + 16) (rem b (roundUp 16 n.toNat)).size ∗ hdrSeg rest nxt ∗ strue ∗
      wordPt ((rem b (roundUp 16 n.toNat)).addr + 8#64).toNat nxt))
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx]; ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := mcode) (o := 74) (k := 3)
    (pc := 0x401377 + 3#64) (pc' := 0x40137d) (by decide) (fit 74 3) (base := .r8) (src := .rdx)
    (by decide) (by decide) (by decide) (disp := 0) (entails_refl _) d74 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; simp)) ?_
  -- mov %rdi, (%rax): the served block's size becomes `need`
  refine SPEC.mem (M' := wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ (wordPt sp.toNat ret ∗
      plistO flAddr passed ∗ wordPt (lastSlot flAddr passed).toNat b.addr ∗
      wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) ∗
      blockAny ((rem b (roundUp 16 n.toNat)).addr.toNat + 16) (rem b (roundUp 16 n.toNat)).size ∗ hdrSeg rest nxt ∗ strue ∗
      wordPt ((rem b (roundUp 16 n.toNat)).addr + 8#64).toNat nxt ∗
      wordPt (rem b (roundUp 16 n.toNat)).addr.toNat (BitVec.ofNat 64 (b.size - roundUp 16 n.toNat - 16))))
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx, hrdi]
        rw [w_rdx b.size _ hsp hsz]; ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := mcode) (o := 77) (k := 3)
    (pc := 0x40137d) (pc' := 0x401380) (by decide) (fit 77 3) (base := .rax) (src := .rdi)
    (by decide) (by decide) (by decide) (disp := 0) (wordPt_blockAny _ _) d77 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]; simp)) ?_
  -- mov %rcx, (%rsi): the final link slot takes the remainder
  refine SPEC.mem (M' := wordPt (lastSlot flAddr passed).toNat b.addr ∗ (wordPt sp.toNat ret ∗
      plistO flAddr passed ∗ wordPt b.addr.toNat (BitVec.ofNat 64 (roundUp 16 n.toNat)) ∗
      wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) ∗
      blockAny ((rem b (roundUp 16 n.toNat)).addr.toNat + 16) (rem b (roundUp 16 n.toNat)).size ∗ hdrSeg rest nxt ∗ strue ∗
      wordPt ((rem b (roundUp 16 n.toNat)).addr + 8#64).toNat nxt ∗
      wordPt (rem b (roundUp 16 n.toNat)).addr.toNat (BitVec.ofNat 64 (b.size - roundUp 16 n.toNat - 16))))
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi]; ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := mcode) (o := 80) (k := 3)
    (pc := 0x401380) (pc' := 0x401383) (by decide) (fit 80 3) (base := .rsi) (src := .rcx)
    (by decide) (by decide) (by decide) (disp := 0) (wordPt_blockAny _ _) d80 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi]; simp)) ?_
  -- add $0x10, %rax; ret
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := mcode) (o := 83) (k := 4) (pc := 0x401383)
    (by decide) (fit 83 4) (op := .add) (by decide) (r := .rax) (imm := 0x10) (by decide) d83) ?_
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (plistO flAddr passed ∗
      wordPt (lastSlot flAddr passed).toNat (rem b (roundUp 16 n.toNat)).addr ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 (roundUp 16 n.toNat)) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) ∗
      wordPt (rem b (roundUp 16 n.toNat)).addr.toNat (BitVec.ofNat 64 (rem b (roundUp 16 n.toNat)).size) ∗
      wordPt ((rem b (roundUp 16 n.toNat)).addr + 8#64).toNat nxt ∗
      blockAny ((rem b (roundUp 16 n.toNat)).addr.toNat + 16) (rem b (roundUp 16 n.toNat)).size ∗ hdrSeg rest nxt ∗ strue))
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; ac_rfl) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := mcode) (o := 87) (k := 1)
    (pc := 0x401383 + 4#64) (by decide) (fit 87 1)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) r87) ?_
  refine St_post hS (by simp only [Function.update_self])
    (hE.split hn4 passed rest b nxt hfl hsmall hWF hsp _ ?_)
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax,
    Silmaril.X86.Ext.AluOp.resultN]
  rw [show BitVec.signExtend 64 (0x10 : BitVec 8) = 16#64 by decide +kernel]

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

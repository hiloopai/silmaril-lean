module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitTailA

/-!
# Proofs: rung 05 (first-fit) `malloc` — serving a block whole (offset 80)

The block fits but a split would leave less than 32 bytes: the final link slot of the walked
segment takes the block's next pointer, and `malloc` returns the payload.
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

/-- **Serve the block whole.** -/
theorem tailB_whole (S : Silmaril.X86.Sep.FnSpec) (hS : S.stack = 0) (x : S.Arg)
    (fl0 passed rest : List Block) (b : Block) (n nxt sp ret : Word) (hE : Exits S x n fl0)
    (f : Reg → Word) (fl : Flags) (hrax : f .rax = b.addr) (hrcx : f .rcx = nxt)
    (hrsi : f .rsi = lastSlot flAddr passed) (hrsp : f .rsp = sp) (hn4 : n.toNat ≤ 4096)
    (hfl : passed ++ b :: rest = fl0)
    (hsmall : ∀ c ∈ passed, c.size < roundUp 16 n.toNat)
    (hWF : b.WF) (hneed : roundUp 16 n.toNat ≤ b.size) (hns : ¬ roundUp 16 n.toNat + 32 ≤ b.size) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 mcode) (St 0x401380 f fl (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
      hdrSeg rest nxt ∗ strue))
      (S.SysVPost x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.mem (M' := wordPt (lastSlot flAddr passed).toNat b.addr ∗ (wordPt sp.toNat ret ∗
    plistO flAddr passed ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
    wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
    hdrSeg rest nxt ∗ strue)) (by rw [plist_last]; ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := mcode) (o := 80) (k := 3) (pc := 0x401380)
    (pc' := 0x401383) (by decide) (fit 80 3) (base := .rsi) (src := .rcx) (by decide) (by decide)
    (by decide) (disp := 0) (wordPt_blockAny _ _) d80 (by decide)
    (by rw [hrsi]; simp)) ?_
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := mcode) (o := 83) (k := 4) (pc := 0x401383)
    (by decide) (fit 83 4) (op := .add) (by decide) (r := .rax) (imm := 0x10) (by decide) d83) ?_
  rw [hrcx]
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (plistO flAddr passed ∗
    wordPt (lastSlot flAddr passed).toNat nxt ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
    wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
    hdrSeg rest nxt ∗ strue)) (by ac_rfl) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := mcode) (o := 87) (k := 1)
    (pc := 0x401383 + 4#64) (by decide) (fit 87 1)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) r87) ?_
  refine St_post hS (by simp only [Function.update_self])
    (hE.whole hn4 passed rest b nxt hfl hsmall hWF hneed hns _ ?_)
  simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax,
    Silmaril.X86.Ext.AluOp.resultN]
  rw [show BitVec.signExtend 64 (0x10 : BitVec 8) = 16#64 by decide +kernel]

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

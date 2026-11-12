module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree1

/-!
# Proofs: rung 06 (coalescing) `free` — the two shared tails

* `tail270` (offset 270): the freed block `H` (possibly already merged with its successor) becomes
  the head: `freelist := H`.
* `tail199` (offset 199): `H` is linked after the previous block `b`; when `b` ends exactly where
  `H` starts, `b` absorbs `H` (offset 224).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Coalesce
open Silmaril.Libc.X86Alloc.Ladder.FirstFit (iface flAddr)
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole

/-- The free postcondition we target for a live block. -/
abbrev Post (p : Word) (n : Nat) (sp ret : Word) : SProp :=
  (freeSpec iface.toIface).SysVPost (p, some n) sp ret

/-- A block's three parts as one `hdrSeg` cell. -/
theorem cell (H : Block) (hn : Word) (R : List Block) (hWF : H.WF) :
    (wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗ wordPt (H.addr + 8#64).toNat hn ∗
      blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn) ⊢ₛ hdrSeg (H :: R) H.addr := by
  rw [hdrSeg_cons]
  exact spure_sep_intro ⟨rfl, hWF⟩ (sexists_intro hn (entails_refl _))

/-- **`freelist := H`; ret.** -/
theorem tail270 (p : Word) (n : Nat) (H : Block) (hn old sp ret : Word) (R : List Block)
    (f : Reg → Word) (fl : Flags) (hrdx : f .rdx = H.addr) (hrsp : f .rsp = sp) (hWF : H.WF) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x40143e f fl (wordPt sp.toNat ret ∗
      wordPt flAddr.toNat old ∗ wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗
      wordPt (H.addr + 8#64).toNat hn ∗ blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue))
      (Post p n sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine SPEC.mem (M' := wordPt flAddr.toNat old ∗ (wordPt sp.toNat ret ∗
      wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗ wordPt (H.addr + 8#64).toNat hn ∗
      blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_storeRip E (b := 0x401330) (code := code) (o := 270) (k := 7)
    (pc := 0x40143e) (pc' := 0x401445) (by decide) (fit 270 7) (src := .rdx) (by decide)
    (disp := 0x1c5b) (wordPt_blockAny _ _) e270 (by decide) (by decide)) ?_
  rw [hrdx]
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (wordPt flAddr.toNat H.addr ∗
      (wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗ wordPt (H.addr + 8#64).toNat hn ∗
      blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn) ∗ strue)) (by ac_rfl) ?_
  refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 277)
    (k := 1) (pc := 0x401445) (by decide) (fit 277 1) hrsp q277) ?_
  exact St_post rfl (by simp only [Function.update_self])
    (entails_trans (sep_mono_right _ (sep_mono_left _ (cell H hn R hWF))) (close _ _))

/-! ## Word arithmetic of the header offsets -/

theorem w_m16 (a : Word) : a + 16#64 + BitVec.signExtend 64 (0xfffffff0 : BitVec 32) = a := by
  rw [show BitVec.signExtend 64 (0xfffffff0 : BitVec 32) = -16#64 by decide +kernel,
    BitVec.add_assoc]; simp

theorem w_m8 (a : Word) : a + 16#64 + BitVec.signExtend 64 (0xfffffff8 : BitVec 32) = a + 8#64 := by
  rw [show BitVec.signExtend 64 (0xfffffff8 : BitVec 32) = -8#64 by decide +kernel,
    BitVec.add_assoc]; congr 1

theorem w_z (a : Word) : a + BitVec.signExtend 64 (0 : BitVec 32) = a := by
  rw [show BitVec.signExtend 64 (0 : BitVec 32) = 0#64 by decide +kernel]; simp

theorem w_8 (a : Word) : a + BitVec.signExtend 64 (8 : BitVec 32) = a + 8#64 := by
  rw [show BitVec.signExtend 64 (8 : BitVec 32) = 8#64 by decide +kernel]

/-- The previous block ends where `H` starts. -/
theorem contig (b H : Block) (hb : b.WF) (hH : H.WF)
    (hm : H.addr = b.addr + BitVec.ofNat 64 b.size + 16#64) :
    H.addr.toNat = b.addr.toNat + 16 + b.size ∧ b.size + 16 + H.size < 2 ^ 64 := by
  have b2 := hb.2.2; have h2 := hH.2.2
  have e : H.addr.toNat = b.addr.toNat + 16 + b.size := by
    rw [hm, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b.size)
      (by omega), Nat.mod_eq_of_lt (a := b.addr.toNat + b.size) (by omega),
      show (16#64 : Word).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  exact ⟨e, by rw [e] at h2; omega⟩

/-- **Link `H` after `b`; merge `b` with `H` when contiguous.** -/
theorem tail199 (p : Word) (n : Nat) (passed R : List Block) (b H : Block) (Z hn sp ret : Word)
    (f : Reg → Word) (fl : Flags) (hrcx : f .rcx = b.addr) (hrdx : f .rdx = H.addr)
    (hrsi : f .rsi = H.addr + 16#64) (hrsp : f .rsp = sp) (hb : b.WF) (hH : H.WF) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4013f7 f fl (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat Z ∗ blockAny (b.addr.toNat + 16) b.size ∗
      wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗ wordPt (H.addr + 8#64).toNat hn ∗
      blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue))
      (Post p n sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hbs : b.size < 2 ^ 64 := by have := hb.2.2; omega
  -- mov (%rcx), %rax
  refine SPEC.mem (M' := wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt (b.addr + 8#64).toNat Z ∗ blockAny (b.addr.toNat + 16) b.size ∗
      wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗ wordPt (H.addr + 8#64).toNat hn ∗
      blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 199) (k := 3) (pc := 0x4013f7)
    (pc' := 0x4013fa) (by decide) (fit 199 3) (base := .rcx) (dst := .rax) (by decide) (by decide)
    (by decide) (disp := 0) e199 (by decide) (by rw [hrcx, w_z])) ?_
  -- mov %rdx, 0x8(%rcx)
  refine SPEC.mem (M' := wordPt (b.addr + 8#64).toNat Z ∗ (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      blockAny (b.addr.toNat + 16) b.size ∗
      wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗ wordPt (H.addr + 8#64).toNat hn ∗
      blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 202) (k := 4)
    (pc := 0x4013fa) (pc' := 0x4013fe) (by decide) (fit 202 4) (base := .rcx) (src := .rdx)
    (by decide) (by decide) (by decide) (disp := 8) (wordPt_blockAny _ _) e202 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx, w_8])) ?_
  -- lea 0x10(%rcx,%rax,1), %rdi; cmp %rdi, %rdx
  refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 206) (k := 5) (pc := 0x4013fe)
    (by decide) (fit 206 5) (dst := .rdi) (by decide) e206
    (a := b.addr + BitVec.ofNat 64 b.size + 16#64) (fun st hregs next => by
      rw [idx_addr, hregs .rcx (by decide), hregs .rax (by decide)]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx]
      rw [show BitVec.signExtend 64 (0x10 : BitVec 32) = 16#64 by decide +kernel])) ?_
  refine SPEC.trans (c_cmp E (b := 0x401330) (code := code) (o := 211) (k := 3)
    (pc := 0x4013fe + 5#64) (by decide) (fit 211 3) (r := .rdx) (q := .rdi) (by decide) (by decide)
    (by decide) e211) ?_
  by_cases hm : H.addr = b.addr + BitVec.ofNat 64 b.size + 16#64
  · -- merge b with H
    obtain ⟨hc, hbnd⟩ := contig b H hb hH hm
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 214) (k := 2)
      (pc := 0x4013fe + 5#64 + 3#64) (pc' := 0x401410) (by decide) (fit 214 2) (c := .e)
      (rel := 0x08) ?_ e214 (by decide)) ?_
    · rw [eval_e_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
      simp [hm]
    have hHs : H.size < 2 ^ 64 := by omega
    -- mov -0x10(%rsi), %rdx
    refine SPEC.mem (M' := wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗ (wordPt sp.toNat ret ∗
        plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
        wordPt (b.addr + 8#64).toNat H.addr ∗ blockAny (b.addr.toNat + 16) b.size ∗
        wordPt (H.addr + 8#64).toNat hn ∗ blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue))
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]; ac_rfl) ?_
    refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 224) (k := 4)
      (pc := 0x401410) (pc' := 0x401414) (by decide) (fit 224 4) (base := .rsi) (dst := .rdx)
      (by decide) (by decide) (by decide) (disp := 0xfffffff0) e224 (by decide)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi, w_m16])) ?_
    -- lea 0x10(%rax,%rdx,1), %rax
    refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 228) (k := 5)
      (pc := 0x401414) (by decide) (fit 228 5) (dst := .rax) (by decide) e228
      (a := BitVec.ofNat 64 (b.size + 16 + H.size)) (fun st hregs next => by
        rw [idx_addr, hregs .rax (by decide), hregs .rdx (by decide)]
        simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
        rw [show BitVec.signExtend 64 (0x10 : BitVec 32) = 16#64 by decide +kernel]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs, Nat.mod_eq_of_lt hHs]
        rw [Nat.mod_eq_of_lt (a := b.size + H.size) (by omega),
          Nat.mod_eq_of_lt (a := 16) (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega)) ?_
    -- mov %rax, (%rcx)
    refine SPEC.mem (M' := wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ (wordPt sp.toNat ret ∗
        plist flAddr passed b.addr ∗ wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗
        wordPt (b.addr + 8#64).toNat H.addr ∗ blockAny (b.addr.toNat + 16) b.size ∗
        wordPt (H.addr + 8#64).toNat hn ∗ blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue))
      (by ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 233) (k := 3)
      (pc := 0x401414 + 5#64) (pc' := 0x40141c) (by decide) (fit 233 3) (base := .rcx) (src := .rax)
      (by decide) (by decide) (by decide) (disp := 0) (wordPt_blockAny _ _) e233 (by decide)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx, w_z])) ?_
    -- mov -0x8(%rsi), %rax
    refine SPEC.mem (M' := wordPt (H.addr + 8#64).toNat hn ∗ (wordPt sp.toNat ret ∗
        plist flAddr passed b.addr ∗ wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗
        wordPt (b.addr + 8#64).toNat H.addr ∗ blockAny (b.addr.toNat + 16) b.size ∗
        wordPt b.addr.toNat (BitVec.ofNat 64 (b.size + 16 + H.size)) ∗
        blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue))
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; ac_rfl) ?_
    refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 236) (k := 4)
      (pc := 0x40141c) (pc' := 0x401420) (by decide) (fit 236 4) (base := .rsi) (dst := .rax)
      (by decide) (by decide) (by decide) (disp := 0xfffffff8) e236 (by decide)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi, w_m8])) ?_
    -- mov %rax, 0x8(%rcx)
    refine SPEC.mem (M' := wordPt (b.addr + 8#64).toNat H.addr ∗ (wordPt sp.toNat ret ∗
        plist flAddr passed b.addr ∗ wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗
        wordPt (H.addr + 8#64).toNat hn ∗ blockAny (b.addr.toNat + 16) b.size ∗
        wordPt b.addr.toNat (BitVec.ofNat 64 (b.size + 16 + H.size)) ∗
        blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn ∗ strue)) (by ac_rfl) ?_
    refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 240) (k := 4)
      (pc := 0x401420) (pc' := 0x401424) (by decide) (fit 240 4) (base := .rcx) (src := .rax)
      (by decide) (by decide) (by decide) (disp := 8) (wordPt_blockAny _ _) e240 (by decide)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx, w_8])) ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ ((plist flAddr passed b.addr ∗
        (wordPt b.addr.toNat (BitVec.ofNat 64 (b.size + 16 + H.size)) ∗
          wordPt (b.addr + 8#64).toNat hn ∗
          (blockAny (b.addr.toNat + 16) b.size ∗ wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗
            wordPt (H.addr + 8#64).toNat hn ∗ blockAny (H.addr.toNat + 16) H.size) ∗
          hdrSeg R hn)) ∗ strue))
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; ac_rfl) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 244)
      (k := 1) (pc := 0x401424) (by decide) (fit 244 1) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) q244) ?_
    refine St_post rfl (by simp only [Function.update_self]) ?_
    have hb' : Block.WF ⟨b.addr, b.size + 16 + H.size⟩ :=
      merge_WF b.addr b.size H hb hc hH
    refine entails_trans (sep_mono_left _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (sep_mono_left _ (merge_pay b.addr.toNat b.size H _ _ hc hH)))))) ?_
    refine entails_trans (sep_mono_left _ (sep_mono_right _
      (cell ⟨b.addr, b.size + 16 + H.size⟩ hn R hb'))) ?_
    refine entails_trans (sep_mono_left _ (plist_hdrSeg flAddr passed b.addr _)) ?_
    rw [sexists_sep]
    exact sexists_elim fun h => entails_trans (entails_of_eq (sep_assoc _ _ _)) (close _ _)
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 214) (k := 2)
      (pc := 0x4013fe + 5#64 + 3#64) (pc' := 0x401408) (by decide) (fit 214 2) (c := .e)
      (rel := 0x08) ?_ e214 (by decide)) ?_
    · rw [eval_e_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
      simp [hm]
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ ((plist flAddr passed b.addr ∗ ⌜b.WF⌝ ∗
        wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ blockAny (b.addr.toNat + 16) b.size ∗
        wordPt (b.addr + 8#64).toNat H.addr) ∗
        (wordPt H.addr.toNat (BitVec.ofNat 64 H.size) ∗ wordPt (H.addr + 8#64).toNat hn ∗
          blockAny (H.addr.toNat + 16) H.size ∗ hdrSeg R hn) ∗ strue))
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
          rw [show (⌜b.WF⌝ : SProp) = emp from by rw [← spure_true_emp]; simp [hb], emp_sep]
          ac_rfl) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 216)
      (k := 1) (pc := 0x401408) (by decide) (fit 216 1) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]) q216) ?_
    refine St_post rfl (by simp only [Function.update_self]) ?_
    rw [plist_snoc]
    refine entails_trans (sep_mono_right _ (sep_mono_left _ (cell H hn R hH))) ?_
    refine entails_trans (entails_of_eq (sep_assoc _ _ _).symm) ?_
    refine entails_trans (sep_mono_left _ (plist_hdrSeg flAddr (passed ++ [b]) H.addr _)) ?_
    rw [sexists_sep]
    exact sexists_elim fun h => entails_trans (entails_of_eq (sep_assoc _ _ _)) (close _ _)

end Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree

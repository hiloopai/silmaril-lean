module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree2

/-!
# Proofs: rung 06 (coalescing) `free` — after the walk (offset 177)

`H`'s next pointer takes the current block `cur`; if `cur` starts exactly where `H` ends, `H`
absorbs it (offset 278); then `tail199` links `H` after the previous block.
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

/-- `cur` starts where `H` ends. -/
theorem contig' (hb : Word) (sz : Nat) (c : Block) (hF : Block.WF ⟨hb, sz⟩) (hc : c.WF)
    (hm : c.addr = hb + 16#64 + BitVec.ofNat 64 sz) :
    c.addr.toNat = hb.toNat + 16 + sz ∧ sz + 16 + c.size < 2 ^ 64 := by
  have f2 := hF.2.2; have c2 := hc.2.2
  simp only at f2
  have ho : (BitVec.ofNat 64 sz).toNat = sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h16 : (hb + 16#64).toNat = hb.toNat + 16 := by
    rw [BitVec.toNat_add, show (16#64 : Word).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
  have e : c.addr.toNat = hb.toNat + 16 + sz := by
    rw [hm, BitVec.toNat_add, h16, ho, Nat.mod_eq_of_lt (by omega)]
  exact ⟨e, by rw [e] at c2; omega⟩

theorem path177 (p : Word) (n : Nat) (passed rest : List Block) (b : Block) (hb nxt sp ret : Word)
    (sz : Nat) (f : Reg → Word) (fl : Flags) (hrcx : f .rcx = b.addr) (hrax : f .rax = nxt)
    (hrdx : f .rdx = hb) (hrsi : f .rsi = hb + 16#64) (hrsp : f .rsp = sp) (hbW : b.WF)
    (hF : Block.WF ⟨hb, sz⟩) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4013e1 f fl (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt ∗
      wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ blockAny (hb + 8#64).toNat 8 ∗
      blockAny (hb.toNat + 16) sz ∗ strue))
      (Post p n sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hsz : sz < 2 ^ 64 := by have := hF.2.2; simp only at this; omega
  -- mov %rax, -0x8(%rsi): H.next := cur
  refine SPEC.mem (M' := blockAny (hb + 8#64).toNat 8 ∗ (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt ∗
      wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ blockAny (hb.toNat + 16) sz ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 177) (k := 4)
    (pc := 0x4013e1) (pc' := 0x4013e5) (by decide) (fit 177 4) (base := .rsi) (src := .rax)
    (by decide) (by decide) (by decide) (disp := 0xfffffff8) (entails_refl _) e177 (by decide)
    (by rw [hrsi, w_m8])) ?_
  rw [hrax]
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 181) (k := 3) (pc := 0x4013e5)
    (by decide) (fit 181 3) (r := .rax) (by decide) e181) ?_
  by_cases hz : nxt = 0
  · -- no successor: link after b
    subst hz
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 184) (k := 2)
      (pc := 0x4013e5 + 3#64) (pc' := 0x4013f7) (by decide) (fit 184 2) (c := .e) (rel := 0x0d) ?_
      e184 (by decide)) ?_
    · rw [eval_e_test, hrax]; rfl
    refine SPEC.mem ?_ (tail199 p n passed rest b ⟨hb, sz⟩ 0 0 sp ret f _ hrcx hrdx hrsi
      hrsp hbW hF)
    dsimp only; ac_rfl
  refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 184) (k := 2)
    (pc := 0x4013e5 + 3#64) (pc' := 0x4013ea) (by decide) (fit 184 2) (c := .e) (rel := 0x0d) ?_
    e184 (by decide)) ?_
  · rw [eval_e_test, hrax]; simpa using hz
  -- mov -0x10(%rsi), %rdi; lea (%rsi,%rdi,1), %r8; cmp %r8, %rax
  refine SPEC.mem (M' := wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt ∗
      wordPt (hb + 8#64).toNat nxt ∗ blockAny (hb.toNat + 16) sz ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 186) (k := 4)
    (pc := 0x4013ea) (pc' := 0x4013ee) (by decide) (fit 186 4) (base := .rsi) (dst := .rdi)
    (by decide) (by decide) (by decide) (disp := 0xfffffff0) e186 (by decide)
    (by rw [hrsi, w_m16])) ?_
  refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 190) (k := 4) (pc := 0x4013ee)
    (by decide) (fit 190 4) (dst := .r8) (by decide) e190
    (a := hb + 16#64 + BitVec.ofNat 64 sz) (fun st hregs next => by
      rw [idx_addr, hregs .rsi (by decide), hregs .rdi (by decide)]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi, w_z])) ?_
  refine SPEC.trans (c_cmp E (b := 0x401330) (code := code) (o := 194) (k := 3)
    (pc := 0x4013ee + 4#64) (by decide) (fit 194 3) (r := .rax) (q := .r8) (by decide) (by decide)
    (by decide) e194) ?_
  by_cases hm : nxt = hb + 16#64 + BitVec.ofNat 64 sz
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 197) (k := 2)
      (pc := 0x4013ee + 4#64 + 3#64) (pc' := 0x401446) (by decide) (fit 197 2) (c := .e)
      (rel := 0x4f) ?_ e197 (by decide)) ?_
    · rw [eval_e_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]; simp [hm]
    cases rest with
    | nil =>
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜nxt = 0⌝ ∗ (plist flAddr passed b.addr ∗
          wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
          blockAny (b.addr.toNat + 16) b.size ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
          wordPt (hb + 8#64).toNat nxt ∗ blockAny (hb.toNat + 16) sz ∗ strue)))
        (by rw [hdrSeg_nil]; ac_rfl) ?_
      rw [St_pure]
      exact SPEC.spure fun h0 => absurd h0 hz
    | cons c rest' =>
      refine SPEC.memPre (sep_mono_right _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
        (sep_mono_right _ (sep_mono_right _ (sep_mono_left _ (hdrSeg_head c rest' nxt)))))))) ?_
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜nxt = c.addr ∧ c.WF⌝ ∗
          (plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
          hdrSeg (c :: rest') nxt ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
          wordPt (hb + 8#64).toNat nxt ∗ blockAny (hb.toNat + 16) sz ∗ strue))) (by ac_rfl) ?_
      rw [St_pure]
      refine SPEC.spure fun ⟨hnc, hcW⟩ => ?_
      subst hnc
      obtain ⟨hc', hbnd⟩ := contig' hb sz c hF hcW hm
      have hcs : c.size < 2 ^ 64 := by omega
      refine SPEC.mem (M' := (wordPt sp.toNat ret ∗ plist flAddr passed b.addr ∗
          wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat c.addr ∗
          blockAny (b.addr.toNat + 16) b.size ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
          wordPt (hb + 8#64).toNat c.addr ∗ blockAny (hb.toNat + 16) sz ∗ strue) ∗
          (⌜c.addr = c.addr ∧ c.WF⌝ ∗ sexists fun cn =>
            wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ wordPt (c.addr + 8#64).toNat cn ∗
            blockAny (c.addr.toNat + 16) c.size ∗ hdrSeg rest' cn))
        (by rw [hdrSeg_cons]; ac_rfl) ?_
      refine SPEC.mem (M' := (wordPt sp.toNat ret ∗ plist flAddr passed b.addr ∗
          wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat c.addr ∗
          blockAny (b.addr.toNat + 16) b.size ∗ wordPt hb.toNat (BitVec.ofNat 64 sz) ∗
          wordPt (hb + 8#64).toNat c.addr ∗ blockAny (hb.toNat + 16) sz ∗ strue) ∗
          (⌜c.addr = c.addr ∧ c.WF⌝ ∗ sexists fun cn =>
            wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ wordPt (c.addr + 8#64).toNat cn ∗
            blockAny (c.addr.toNat + 16) c.size ∗ hdrSeg rest' cn)) rfl ?_
      rw [St_pure]
      refine SPEC.spure fun _ => ?_
      rw [St_ex]
      refine SPEC.sexists fun cn => ?_
      -- mov (%rax), %r8; mov 0x8(%rax), %rax
      refine SPEC.mem (M' := wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ (wordPt sp.toNat ret ∗
          plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat c.addr ∗ blockAny (b.addr.toNat + 16) b.size ∗
          wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ wordPt (hb + 8#64).toNat c.addr ∗
          blockAny (hb.toNat + 16) sz ∗ strue ∗ wordPt (c.addr + 8#64).toNat cn ∗
          blockAny (c.addr.toNat + 16) c.size ∗ hdrSeg rest' cn)) (by ac_rfl) ?_
      refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 278) (k := 3)
        (pc := 0x401446) (pc' := 0x401449) (by decide) (fit 278 3) (base := .rax) (dst := .r8)
        (by decide) (by decide) (by decide) (disp := 0) e278 (by decide)
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax, w_z])) ?_
      refine SPEC.mem (M' := wordPt (c.addr + 8#64).toNat cn ∗ (wordPt sp.toNat ret ∗
          plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat c.addr ∗ blockAny (b.addr.toNat + 16) b.size ∗
          wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ wordPt (hb + 8#64).toNat c.addr ∗
          blockAny (hb.toNat + 16) sz ∗ strue ∗ wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗
          blockAny (c.addr.toNat + 16) c.size ∗ hdrSeg rest' cn)) (by ac_rfl) ?_
      refine SPEC.trans (c_loadSelf E (b := 0x401330) (code := code) (o := 281) (k := 4)
        (pc := 0x401449) (pc' := 0x40144d) (by decide) (fit 281 4) (r := .rax) (by decide)
        (disp := 8) e281 (by decide) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax, w_8])) ?_
      -- lea 0x10(%rdi,%r8,1), %rdi
      refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 285) (k := 5)
        (pc := 0x40144d) (by decide) (fit 285 5) (dst := .rdi) (by decide) e285
        (a := BitVec.ofNat 64 (sz + 16 + c.size)) (fun st hregs next => by
          rw [idx_addr, hregs .rdi (by decide), hregs .r8 (by decide)]
          simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
          rw [show BitVec.signExtend 64 (0x10 : BitVec 32) = 16#64 by decide +kernel]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz,
            Nat.mod_eq_of_lt hcs]
          rw [Nat.mod_eq_of_lt (a := sz + c.size) (by omega), Nat.mod_eq_of_lt (a := 16) (by omega),
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega)) ?_
      -- mov %rax, -0x8(%rsi); mov %rdi, -0x10(%rsi)
      refine SPEC.mem (M' := wordPt (hb + 8#64).toNat c.addr ∗ (wordPt sp.toNat ret ∗
          plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat c.addr ∗ blockAny (b.addr.toNat + 16) b.size ∗
          wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ blockAny (hb.toNat + 16) sz ∗ strue ∗
          wordPt (c.addr + 8#64).toNat cn ∗ wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗
          blockAny (c.addr.toNat + 16) c.size ∗ hdrSeg rest' cn)) (by ac_rfl) ?_
      refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 290) (k := 4)
        (pc := 0x40144d + 5#64) (pc' := 0x401456) (by decide) (fit 290 4) (base := .rsi)
        (src := .rax) (by decide) (by decide) (by decide) (disp := 0xfffffff8) (wordPt_blockAny _ _)
        e290 (by decide) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi, w_m8])) ?_
      refine SPEC.mem (M' := wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ (wordPt sp.toNat ret ∗
          plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat c.addr ∗ blockAny (b.addr.toNat + 16) b.size ∗
          wordPt (hb + 8#64).toNat cn ∗ blockAny (hb.toNat + 16) sz ∗ strue ∗
          wordPt (c.addr + 8#64).toNat cn ∗ wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗
          blockAny (c.addr.toNat + 16) c.size ∗ hdrSeg rest' cn))
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; ac_rfl) ?_
      refine SPEC.trans (c_storeQ E (b := 0x401330) (code := code) (o := 294) (k := 4)
        (pc := 0x401456) (pc' := 0x40145a) (by decide) (fit 294 4) (base := .rsi) (src := .rdi)
        (by decide) (by decide) (by decide) (disp := 0xfffffff0) (wordPt_blockAny _ _) e294
        (by decide) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi, w_m16])) ?_
      refine SPEC.trans (c_jmp8 E (b := 0x401330) (code := code) (o := 298) (k := 2)
        (pc := 0x40145a) (by decide) (fit 298 2) (pc' := 0x4013f7) e298 (by decide)) ?_
      -- merge the payloads, then link after b
      refine SPEC.memPre (M' := wordPt hb.toNat (BitVec.ofNat 64 (sz + 16 + c.size)) ∗
          (wordPt sp.toNat ret ∗ plist flAddr passed b.addr ∗
          wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat c.addr ∗
          blockAny (b.addr.toNat + 16) b.size ∗ wordPt (hb + 8#64).toNat cn ∗ strue ∗
          blockAny (hb.toNat + 16) (sz + 16 + c.size) ∗ hdrSeg rest' cn)) ?_ ?_
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
        refine sep_mono_right _ (entails_trans (entails_of_eq (show _ =
          ((wordPt sp.toNat ret ∗ plist flAddr passed b.addr ∗
          wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat c.addr ∗
          blockAny (b.addr.toNat + 16) b.size ∗ wordPt (hb + 8#64).toNat cn ∗ strue ∗
          hdrSeg rest' cn) ∗ (blockAny (hb.toNat + 16) sz ∗
            wordPt c.addr.toNat (BitVec.ofNat 64 c.size) ∗ wordPt (c.addr + 8#64).toNat cn ∗
            blockAny (c.addr.toNat + 16) c.size)) by ac_rfl))
          (entails_trans (sep_mono_right _ (merge_pay hb.toNat sz c _ _ hc' hcW))
            (entails_of_eq (by ac_rfl))))
      refine SPEC.mem ?_ (tail199 p n passed rest' b ⟨hb, sz + 16 + c.size⟩ c.addr cn sp ret _ _
        ?_ ?_ ?_ ?_ hbW (merge_WF hb sz c hF hc' hcW))
      · dsimp only; ac_rfl
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 197) (k := 2)
      (pc := 0x4013ee + 4#64 + 3#64) (pc' := 0x4013f7) (by decide) (fit 197 2) (c := .e)
      (rel := 0x4f) ?_ e197 (by decide)) ?_
    · rw [eval_e_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]; simp [hm]
    refine SPEC.mem ?_ (tail199 p n passed rest b ⟨hb, sz⟩ nxt nxt sp ret _ _ ?_ ?_ ?_ ?_ hbW hF)
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; ac_rfl
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrcx]
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi]
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]

end Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree

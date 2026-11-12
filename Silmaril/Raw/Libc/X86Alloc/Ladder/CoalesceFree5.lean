module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree4
public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree

/-!
# Proofs: rung 06 (coalescing) `free` meets the loose `freeSpec`

The walk (offset 160) moves `prev` along the list while the next block is non-null and below the
freed header `H`; it is proved with `SPEC.loop` (measure: the unvisited tail). It exits to
`path177` (link after `prev`, with the merges). The entry handles `free(NULL)`, and an empty list
or a head not below `H` goes to `path248` (insert at the head).
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
open Silmaril.Raw.Libc.X86Alloc.Loop

/-- A loop index of the walk. -/
structure WIx where
  passed : List Block
  b : Block
  rest : List Block

/-- The freed block's parts. -/
abbrev FB (hb : Word) (sz : Nat) : SProp :=
  wordPt hb.toNat (BitVec.ofNat 64 sz) ∗ blockAny (hb + 8#64).toNat 8 ∗ blockAny (hb.toNat + 16) sz

/-- **The walk's invariant** at `0x4013d0`. -/
def WInv (hb : Word) (sz : Nat) (sp ret : Word) (x : WIx) : SProp :=
  sexists fun (f : Reg → Word) => sexists fun (fl : Flags) =>
    ⌜f .rax = x.b.addr ∧ f .rdx = hb ∧ f .rsi = hb + 16#64 ∧ f .rsp = sp⌝ ∗
    St 0x4013d0 f fl (wordPt sp.toNat ret ∗ plist flAddr x.passed x.b.addr ∗
      hdrSeg (x.b :: x.rest) x.b.addr ∗ FB hb sz ∗ strue)

def wμ (x : WIx) : Nat := x.rest.length

theorem St_mono' {pc : Word} {f : Reg → Word} {fl : Flags} {M M' : SProp} (h : M ⊢ₛ M') :
    St pc f fl M ⊢ₛ St pc f fl M' :=
  sep_mono_right _ (sep_mono_right _ (sep_mono_right _ h))

/-- **One step of the walk.** -/
theorem wbody (p : Word) (n : Nat) (hb sp ret : Word) (sz : Nat) (hF : Block.WF ⟨hb, sz⟩)
    (x : WIx) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (WInv hb sz sp ret x)
      (sor (Post p n sp ret) (sexists fun y => ⌜wμ y < wμ x⌝ ∗ WInv hb sz sp ret y)) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  obtain ⟨passed, b, rest⟩ := x
  refine SPEC.sexists fun f => SPEC.sexists fun fl => ?_
  refine SPEC.spure fun ⟨hrax, hrdx, hrsi, hrsp⟩ => ?_
  dsimp only at hrax
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜b.addr = b.addr ∧ b.WF⌝ ∗
      ((plist flAddr passed b.addr ∗ FB hb sz ∗ strue) ∗
        sexists fun nxt => wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
          hdrSeg rest nxt))) (by rw [hdrSeg_cons]; ac_rfl) ?_
  rw [St_pure]
  refine SPEC.spure fun ⟨_, hbW⟩ => ?_
  refine SPEC.mem (M' := (wordPt sp.toNat ret ∗ plist flAddr passed b.addr ∗ FB hb sz ∗ strue) ∗
      sexists fun nxt => wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
          hdrSeg rest nxt) (by ac_rfl) ?_
  rw [St_ex]
  refine SPEC.sexists fun nxt => ?_
  -- mov %rax, %rcx; mov 0x8(%rax), %rax
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 160) (k := 3) (pc := 0x4013d0)
    (by decide) (fit 160 3) (r := .rcx) (q := .rax) (by decide) (by decide) (by decide) e160) ?_
  refine SPEC.mem (M' := wordPt (b.addr + 8#64).toNat nxt ∗ (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt ∗ FB hb sz ∗ strue)) (by ac_rfl) ?_
  refine SPEC.trans (c_loadSelf E (b := 0x401330) (code := code) (o := 163) (k := 4)
    (pc := 0x4013d0 + 3#64) (pc' := 0x4013d7) (by decide) (fit 163 4) (r := .rax) (by decide)
    (disp := 8) e163 (by decide) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax, w_8])) ?_
  refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 167) (k := 3) (pc := 0x4013d7)
    (by decide) (fit 167 3) (r := .rax) (by decide) e167) ?_
  -- the exit to path177 at a given register file
  have exit177 : ∀ (g : Reg → Word) (gl : Flags), g .rcx = b.addr → g .rax = nxt → g .rdx = hb →
      g .rsi = hb + 16#64 → g .rsp = sp →
      SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x4013e1 g gl
        (wordPt (b.addr + 8#64).toNat nxt ∗ (wordPt sp.toNat ret ∗
        plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
        blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt ∗ FB hb sz ∗ strue)))
        (sor (Post p n sp ret) (sexists fun y => ⌜wμ y < wμ ⟨passed, b, rest⟩⌝ ∗
          WInv hb sz sp ret y)) := by
    intro g gl h1 h2 h3 h4 h5
    refine SPEC.conseq (entails_refl _) ?_ (sor_intro_left _ _)
    refine SPEC.mem ?_ (path177 p n passed rest b hb nxt sp ret sz g gl h1 h2 h3 h4 h5 hbW hF)
    simp only [FB]; ac_rfl
  by_cases hz : nxt = 0
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 170) (k := 2)
      (pc := 0x4013d7 + 3#64) (pc' := 0x4013e1) (by decide) (fit 170 2) (c := .e) (rel := 0x05) ?_
      e170 (by decide)) ?_
    · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hz]; rfl
    exact exit177 _ _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
  refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 170) (k := 2)
    (pc := 0x4013d7 + 3#64) (pc' := 0x4013dc) (by decide) (fit 170 2) (c := .e) (rel := 0x05) ?_
    e170 (by decide)) ?_
  · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; simpa using hz
  refine SPEC.trans (c_cmp E (b := 0x401330) (code := code) (o := 172) (k := 3) (pc := 0x4013dc)
    (by decide) (fit 172 3) (r := .rax) (q := .rdx) (by decide) (by decide) (by decide) e172) ?_
  by_cases hl : nxt.toNat < hb.toNat
  · -- continue the walk
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := code) (o := 175) (k := 2)
      (pc := 0x4013dc + 3#64) (pc' := 0x4013d0) (by decide) (fit 175 2) (c := .b) (rel := 0xef) ?_
      e175 (by decide)) ?_
    · rw [eval_b_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]; simp [hl]
    cases rest with
    | nil =>
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜nxt = 0⌝ ∗ (wordPt (b.addr + 8#64).toNat nxt ∗
          plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          blockAny (b.addr.toNat + 16) b.size ∗ FB hb sz ∗ strue))) (by rw [hdrSeg_nil]; ac_rfl) ?_
      rw [St_pure]
      exact SPEC.spure fun h0 => absurd h0 hz
    | cons c rest' =>
      refine SPEC.memPre (sep_mono_right _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
        (sep_mono_right _ (sep_mono_left _ (hdrSeg_head c rest' nxt))))))) ?_
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜nxt = c.addr ∧ c.WF⌝ ∗
          (wordPt (b.addr + 8#64).toNat nxt ∗ plist flAddr passed b.addr ∗
          wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ blockAny (b.addr.toNat + 16) b.size ∗
          hdrSeg (c :: rest') nxt ∗ FB hb sz ∗ strue))) (by ac_rfl) ?_
      rw [St_pure]
      refine SPEC.spure fun ⟨hnc, _⟩ => ?_
      subst hnc
      refine SPEC.conseq (entails_refl _) (Triple.refl _) ?_
      refine entails_trans ?_ (sor_intro_right _ _)
      refine sexists_intro ⟨passed ++ [b], c, rest'⟩
        (spure_sep_intro (by simp [wμ]) (sexists_intro _ (sexists_intro _
          (spure_sep_intro ⟨?_, ?_, ?_, ?_⟩ (St_mono' ?_)))))
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi]
      · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]
      · rw [← plist_snoc]
        refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ (sep_mono_right _
          (spure_sep_intro hbW (entails_refl _)))))
        exact entails_of_eq (by ac_rfl)
  · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := code) (o := 175) (k := 2)
      (pc := 0x4013dc + 3#64) (pc' := 0x4013e1) (by decide) (fit 175 2) (c := .b) (rel := 0xef) ?_
      e175 (by decide)) ?_
    · rw [eval_b_cmp]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx]; simp [hl]
    exact exit177 _ _ (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdx])
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi]) (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])

end Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree

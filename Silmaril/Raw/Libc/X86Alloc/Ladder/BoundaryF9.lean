module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF8
public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryM6
public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryDisj

/-!
# Proofs: rung 08 (boundary tags) — `free` meets the loose interface

`fentry` (`0x401429`, `p ≠ 0`): the size `s` is read from the token's size word, the token and
the request are folded into the block `[b, b + s)` (`b = p - 16`), its granule `g` and the
granule `e = g + s/16` after it are computed, and the block is apart from every free block (by
separation, `apart_of_sep`); then `fdispatch`. `free_sat` adds `free(NULL)`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.X86.Ext (ShiftOp)
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Boundary
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Whole
open Silmaril.Raw.Libc.X86Alloc.MemStep

/-- A fact every fragment of `P` satisfies may be made explicit. -/
theorem sep_fact {P : SProp} {φ : Prop} (h : ∀ x, P x → φ) : P ⊢ₛ (⌜φ⌝ ∗ P) := by
  intro x hx
  refine ⟨Frag.empty, x, fun _ => .inl rfl, ?_, ⟨rfl, h x hx⟩, hx⟩
  funext l; simp [Frag.union, Frag.empty]

variable {sp ret : Word}

/-- **`0x401429`: the freed block's size, granule and successor granule.** -/
theorem fentry (x : Word × Option Nat) (f : Reg → Word) (fl : Flags) (fs : List (Nat × Nat))
    (p : Word) (n s : Nat) (hw : WF fs)
    (ht : heap + 16 ≤ p.toNat ∧ p.toNat - 16 + s ≤ heap + 4096 ∧ p.toNat % 16 = 0 ∧
      s % 16 = 0 ∧ 32 ≤ s ∧ n + 16 ≤ s)
    (hrdi : f .rdi = p) (hrsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 code) (St 0x401429 f fl
      (wordPt (p.toNat - 16) (wd s) ∗ wordPt sp.toNat ret ∗ blockAny (p.toNat - 8) 8 ∗
        blockAny (p.toNat + n) (s - 16 - n) ∗ blockAny p.toNat n ∗ mmOf fs))
      (FQ x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  have hH := heap_eq
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
  have hpl := p.isLt
  have hrdi' : f .rdi = wd p.toNat := by rw [hrdi]; simp [wd]
  obtain ⟨g, hb⟩ : ∃ g, p.toNat - 16 = heap + 16 * g := ⟨(p.toNat - 16 - heap) / 16, by omega⟩
  have hg64 : 16 * g < 2 ^ 64 := by omega
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := code) (o := 249) (k := 4)
    (pc := 0x401429) (pc' := 0x40142d) (by decide) (fit 249 4) (base := .rdi) (dst := .rax)
    (by decide) (by decide) (by decide) (disp := 0xfffffff0) d249 (by decide)
    (by rw [hrdi']; exact addr_sub (d := 16) (by decide +kernel) (by omega) hpl)) ?_
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 253) (k := 3) (pc := 0x40142d)
    (by decide) (fit 253 3) (r := .rdx) (q := .rdi) (by decide) (by decide) (by decide) d253) ?_
  refine SPEC.trans (c_lea E (b := 0x401330) (code := code) (o := 256) (k := 4)
    (pc := 0x40142d + BitVec.ofNat 64 3) (by decide) (fit 256 4) (dst := .rcx) (by decide) d256
    (a := wd (p.toNat - 16)) (fun st hregs next => by
      rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rdi (by decide)]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi']
      rw [show BitVec.signExtend 64 (0xfffffff0 : BitVec 32) = wd (2 ^ 64 - 16) by
        decide +kernel, wd_sub (by omega) (by omega)])) ?_
  refine SPEC.trans (c_aluI E (b := 0x401330) (code := code) (o := 260) (k := 7)
    (pc := 0x40142d + BitVec.ofNat 64 3 + BitVec.ofNat 64 4) (by decide) (fit 260 7) (op := .sub)
    (by decide) (r := .rdx) (by decide) (imm := 0x4032d0) d260) ?_
  refine SPEC.trans (c_movQ E (b := 0x401330) (code := code) (o := 267) (k := 3)
    (pc := 0x40142d + BitVec.ofNat 64 3 + BitVec.ofNat 64 4 + BitVec.ofNat 64 7) (by decide)
    (fit 267 3) (r := .rsi) (q := .rax) (by decide) (by decide) (by decide) d267) ?_
  refine SPEC.trans (c_shr E (b := 0x401330) (code := code) (o := 270) (k := 4)
    (pc := 0x40142d + BitVec.ofNat 64 3 + BitVec.ofNat 64 4 + BitVec.ofNat 64 7 +
      BitVec.ofNat 64 3) (by decide) (fit 270 4) (r := .rdx) (by decide) (c := 0x4) (by decide)
    d270) ?_
  refine SPEC.trans (c_shr E (b := 0x401330) (code := code) (o := 274) (k := 4)
    (pc := 0x40142d + BitVec.ofNat 64 3 + BitVec.ofNat 64 4 + BitVec.ofNat 64 7 +
      BitVec.ofNat 64 3 + BitVec.ofNat 64 4) (by decide) (fit 274 4) (r := .rsi) (by decide)
    (c := 0x4) (by decide) d274) ?_
  refine SPEC.trans (c_alu E (b := 0x401330) (code := code) (o := 278) (k := 3)
    (pc := 0x40142d + BitVec.ofNat 64 3 + BitVec.ofNat 64 4 + BitVec.ofNat 64 7 +
      BitVec.ofNat 64 3 + BitVec.ofNat 64 4 + BitVec.ofNat 64 4) (by decide) (fit 278 3)
    (op := .add) (by decide) (r := .rsi) (q := .rdx) (by decide) (by decide) (by decide)
    d278) ?_
  have hsub : Silmaril.X86.Ext.AluOp.resultN .sub (wd p.toNat)
      (BitVec.signExtend 64 (0x4032d0 : BitVec 32)) = wd (16 * g) := by
    rw [show BitVec.signExtend 64 (0x4032d0 : BitVec 32) = wd 0x4032d0 by decide +kernel,
      show 16 * g = p.toNat - 0x4032d0 by omega]
    exact wd_minus (by omega) hpl
  have hdx : ShiftOp.shr.result (wd (16 * g)) ((0x4 : BitVec 8).toNat % 64) = wd g := by
    rw [shr4_wd hg64, Nat.mul_div_cancel_left g (by decide : 0 < 16)]
  have hsx : ShiftOp.shr.result (wd s) ((0x4 : BitVec 8).toNat % 64) = wd (s / 16) :=
    shr4_wd (by omega)
  -- fold the token and the request into the block, and read off its apartness
  have hsplit : blockAny (p.toNat - 16) s = (blockAny (p.toNat - 16) 8 ∗
      blockAny (p.toNat - 16 + 8) 8 ∗ blockAny (p.toNat - 16 + 8 + 8) n ∗
      blockAny (p.toNat - 16 + 8 + 8 + n) (s - 16 - n)) := by
    rw [← blockAny_add, ← blockAny_add, ← blockAny_add]; congr 1; omega
  have hblk : (wordPt (p.toNat - 16) (wd s) ∗ blockAny (p.toNat - 8) 8 ∗
      blockAny (p.toNat + n) (s - 16 - n) ∗ blockAny p.toNat n) ⊢ₛ
      blockAny (p.toNat - 16) s := by
    rw [hsplit, show p.toNat - 16 + 8 + 8 = p.toNat by omega,
      show p.toNat - 16 + 8 = p.toNat - 8 by omega]
    refine entails_trans (sep_mono_left _ (wordPt_blockAny _ _)) (entails_of_eq ?_)
    ac_rfl
  refine SPEC.memPre (M' := wordPt sp.toNat ret ∗ (⌜∀ y ∈ fs, Apart (p.toNat - 16, s) y⌝ ∗
      (blockAny (p.toNat - 16) s ∗ wordPt flistA (wd (hdOr fs 0)) ∗ blockAny (flistA + 8) 24 ∗
      tblPt lastA (lastT fs) ∗ tblPt firstA (firstT fs) ∗ dll fs 0 0))) ?_ ?_
  · refine entails_trans (entails_of_eq (show _ = ((wordPt (p.toNat - 16) (wd s) ∗
        blockAny (p.toNat - 8) 8 ∗ blockAny (p.toNat + n) (s - 16 - n) ∗ blockAny p.toNat n) ∗
        (wordPt sp.toNat ret ∗ mmOf fs)) by ac_rfl)) ?_
    refine entails_trans (sep_mono_left _ hblk) ?_
    unfold mmOf
    refine entails_trans (entails_of_eq (show _ = ((blockAny (p.toNat - 16) s ∗ dll fs 0 0) ∗
        (wordPt sp.toNat ret ∗ wordPt flistA (wd (hdOr fs 0)) ∗ blockAny (flistA + 8) 24 ∗
        tblPt lastA (lastT fs) ∗ tblPt firstA (firstT fs))) by ac_rfl)) ?_
    refine entails_trans (sep_mono_left _ (sep_fact fun h H =>
      apart_of_sep (by omega) (fun y hy => (hw.1 y hy).2.2.2.2) H)) ?_
    exact entails_of_eq (by ac_rfl)
  rw [St_pure]
  refine SPEC.spure fun hap => ?_
  have hgb : Good (p.toNat - 16, s) := by unfold Good; simp only; omega
  refine SPEC.mem ?_ (fdispatch x _ _ fs (p.toNat - 16) s g (s / 16 + g) hw hgb hap hb (by omega)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrdi']
        rw [hsx, hsub, hdx]; exact wd_add _ _)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, Function.update_self, hrdi']
        rw [hsub, hdx])
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi']
        congr 1; omega)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp]))
  ac_rfl

/-- **`free` meets `freeSpec iface`.** -/
theorem free_sat :
    (freeSpec iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  refine satWith_of_St rfl (fun x => x.1) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  rcases x with ⟨p, _ | n⟩
  · -- free(NULL)
    change SPEC _ (codePt 0x401330 code) (St 0x401420 f fl (wordPt sp.toNat ret ∗
      (mm ∗ ⌜p = 0⌝))) _
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜p = 0⌝ ∗ mm)) (by ac_rfl) ?_
    rw [St_pure]
    refine SPEC.spure fun hp => ?_
    dsimp only at hdi
    subst hp
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 240) (k := 3)
      (pc := 0x401420) (by decide) (fit 240 3) (r := .rdi) (by decide) d240) ?_
    refine SPEC.trans (c_jcc32_taken E (b := 0x401330) (code := code) (o := 243) (k := 6)
      (pc := 0x401420 + BitVec.ofNat 64 3) (pc' := 0x4014df) (by decide) (fit 243 6) (c := .e)
      (rel := 0xb6) (by rw [eval_e_test, hdi]; rfl) d243 (by decide)) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := code) (o := 431)
      (k := 1) (pc := 0x4014df) (by decide) (fit 431 1) hsp r431) ?_
    exact St_post rfl (by simp only [Function.update_self]) (entails_refl _)
  · change SPEC _ (codePt 0x401330 code) (St 0x401420 f fl (wordPt sp.toNat ret ∗
      (mm ∗ tok p n ∗ blockAny p.toNat n))) (FQ (p, some n) sp ret)
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ sexists fun s : Nat => sexists fun fs =>
      (⌜WF fs⌝ ∗ (⌜heap + 16 ≤ p.toNat ∧ p.toNat - 16 + s ≤ heap + 4096 ∧
        p.toNat % 16 = 0 ∧ s % 16 = 0 ∧ 32 ≤ s ∧ n + 16 ≤ s⌝ ∗
        (wordPt (p.toNat - 16) (wd s) ∗ blockAny (p.toNat - 8) 8 ∗
        blockAny (p.toNat + n) (s - 16 - n) ∗ blockAny p.toNat n ∗ mmOf fs))))
      (by unfold mm tok; simp only [sexists_sep, sep_sexists]; congr 1; funext s; congr 1
          funext fs; ac_rfl) ?_
    rw [St_ex]
    refine SPEC.sexists fun s => ?_
    rw [St_ex]
    refine SPEC.sexists fun fs => ?_
    rw [St_pure]
    refine SPEC.spure fun hw => ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜heap + 16 ≤ p.toNat ∧ p.toNat - 16 + s ≤ heap + 4096 ∧
        p.toNat % 16 = 0 ∧ s % 16 = 0 ∧ 32 ≤ s ∧ n + 16 ≤ s⌝ ∗
        (wordPt (p.toNat - 16) (wd s) ∗ blockAny (p.toNat - 8) 8 ∗
        blockAny (p.toNat + n) (s - 16 - n) ∗ blockAny p.toNat n ∗ mmOf fs))) rfl ?_
    rw [St_pure]
    refine SPEC.spure fun ht => ?_
    dsimp only at hdi
    have hp0 : p ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; rw [heap_eq] at ht; simp at this; omega
    refine SPEC.trans (c_test E (b := 0x401330) (code := code) (o := 240) (k := 3)
      (pc := 0x401420) (by decide) (fit 240 3) (r := .rdi) (by decide) d240) ?_
    refine SPEC.trans (c_jcc32_not E (b := 0x401330) (code := code) (o := 243) (k := 6)
      (pc := 0x401420 + BitVec.ofNat 64 3) (by decide) (fit 243 6) (c := .e)
      (rel := 0xb6) (by rw [eval_e_test, hdi]; simpa using hp0) d243) ?_
    rw [show (0x401420 + BitVec.ofNat 64 3 + BitVec.ofNat 64 6 : Word) = 0x401429 by decide]
    refine SPEC.mem ?_ (fentry (p, some n) f _ fs p n s hw ht hdi hsp)
    ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

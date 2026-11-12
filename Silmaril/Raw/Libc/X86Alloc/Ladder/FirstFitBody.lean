module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitTailC

/-!
# Proofs: rung 05 (first-fit) `malloc` — one iteration of the walk

`body`: from the loop invariant at `x = (passed, b, rest)`, read `b`'s size and next pointer and
compare with `need`; then one of the four tails: list exhausted (`tailA_end`), continue at a
strictly shorter tail (`tailA_next`), serve whole (`tailB_whole`), split (`tailC_split`). This is
exactly the premise of `SPEC.loop`.
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

theorem toNat_small {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **One iteration of the walk.** -/
theorem body (S : Silmaril.X86.Sep.FnSpec) (hS : S.stack = 0) (x : S.Arg) (fl0 : List Block)
    (n sp ret : Word) (hE : Exits S x n fl0) (hn4 : n.toNat ≤ 4096) (i : Ix) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 mcode) (Inv (roundUp 16 n.toNat) sp ret fl0 i)
      (sor (S.SysVPost x sp ret)
        (sexists fun y => ⌜μ y < μ i⌝ ∗ Inv (roundUp 16 n.toNat) sp ret fl0 y)) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  obtain ⟨passed, b, rest⟩ := i
  have hneed : roundUp 16 n.toNat = (n.toNat + 15) / 16 * 16 := rfl
  have hn : n.toNat ≤ roundUp 16 n.toNat := by rw [hneed]; omega
  have h16 : roundUp 16 n.toNat % 16 = 0 := by rw [hneed]; omega
  have hN : roundUp 16 n.toNat + 32 < 2 ^ 64 := by rw [hneed]; omega
  refine SPEC.sexists fun f => SPEC.sexists fun fl => ?_
  refine SPEC.spure fun ⟨hrax, hrsi, hrdi, hrsp, hsmall, hfl⟩ => ?_
  dsimp only at hrax hrsi hrsp hsmall hfl
  -- open the block under inspection
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜b.addr = b.addr ∧ b.WF⌝ ∗
      ((plist flAddr passed b.addr ∗ strue) ∗
        sexists fun nxt => wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
          hdrSeg rest nxt)))
    (by rw [hdrSeg_cons]; ac_rfl) ?_
  rw [St_pure]
  refine SPEC.spure fun ⟨_, hWF⟩ => ?_
  have hsz : b.size < 2 ^ 64 := by have := hWF.2.2; omega
  refine SPEC.mem (M' := (wordPt sp.toNat ret ∗ plist flAddr passed b.addr ∗ strue) ∗
      sexists fun nxt => wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
          hdrSeg rest nxt) (by ac_rfl) ?_
  rw [St_ex]
  refine SPEC.sexists fun nxt => ?_
  -- mov (%rax), %rdx; mov 0x8(%rax), %rcx
  refine SPEC.mem (M' := wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ strue ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt)) (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := mcode) (o := 34) (k := 3) (pc := 0x401352)
    (pc' := 0x401355) (by decide) (fit 34 3) (base := .rax) (dst := .rdx) (by decide) (by decide)
    (by decide) (disp := 0) d34 (by decide) (by rw [hrax]; simp)) ?_
  refine SPEC.mem (M' := wordPt (b.addr + 8#64).toNat nxt ∗ (wordPt sp.toNat ret ∗
      plist flAddr passed b.addr ∗ strue ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt)) (by ac_rfl) ?_
  refine SPEC.trans (c_loadQ E (b := 0x401330) (code := mcode) (o := 37) (k := 4) (pc := 0x401355)
    (pc' := 0x401359) (by decide) (fit 37 4) (base := .rax) (dst := .rcx) (by decide) (by decide)
    (by decide) (disp := 8) d37 (by decide)
    (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax]; rfl)) ?_
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ plist flAddr passed b.addr ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt ∗ strue) (by ac_rfl) ?_
  -- cmp %rdi, %rdx
  refine SPEC.trans (c_cmp E (b := 0x401330) (code := mcode) (o := 41) (k := 3) (pc := 0x401359)
    (by decide) (fit 41 3) (r := .rdx) (q := .rdi) (by decide) (by decide) (by decide) d41) ?_
  have vrdx : (Function.update (Function.update f .rdx (BitVec.ofNat 64 b.size)) .rcx nxt) .rdx =
      BitVec.ofNat 64 b.size := by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
  have vrdi : (Function.update (Function.update f .rdx (BitVec.ofNat 64 b.size)) .rcx nxt) .rdi =
      BitVec.ofNat 64 (roundUp 16 n.toNat) := by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi]
  by_cases hsm : b.size < roundUp 16 n.toNat
  · -- too small
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := mcode) (o := 44) (k := 2)
      (pc := 0x401359 + 3#64) (pc' := 0x401398) (by decide) (fit 44 2) (c := .b) (rel := 0x3a) ?_
      d44 (by decide)) ?_
    · rw [eval_b_cmp, vrdx, vrdi, toNat_small hsz, toNat_small (by omega)]; simp [hsm]
    cases rest with
    | nil =>
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜nxt = 0⌝ ∗ (plist flAddr passed b.addr ∗
          wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
          blockAny (b.addr.toNat + 16) b.size ∗ strue))) (by rw [hdrSeg_nil]; ac_rfl) ?_
      rw [St_pure]
      refine SPEC.spure fun hnx => ?_
      subst hnx
      refine SPEC.conseq (entails_refl _) ?_ (sor_intro_left _ _)
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ plist flAddr passed b.addr ∗
          wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat 0 ∗
          blockAny (b.addr.toNat + 16) b.size ∗ strue) rfl ?_
      exact tailA_end S hS x fl0 passed b n sp ret hE _ _
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
        hn4 (by simpa using hfl) hsmall hsm hWF
    | cons c rest' =>
      refine SPEC.memPre (sep_mono_right _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
        (sep_mono_right _ (sep_mono_left _ (hdrSeg_head c rest' nxt))))))) ?_
      refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜nxt = c.addr ∧ c.WF⌝ ∗
          (plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          wordPt (b.addr + 8#64).toNat nxt ∗ blockAny (b.addr.toNat + 16) b.size ∗
          hdrSeg (c :: rest') nxt ∗ strue))) (by ac_rfl) ?_
      rw [St_pure]
      refine SPEC.spure fun ⟨hnx, hcWF⟩ => ?_
      subst hnx
      exact tailA_next (roundUp 16 n.toNat) fl0 passed rest' b c sp ret _ _
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi])
        hsmall hsm hfl hWF hcWF.1 _
  · -- it fits
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := mcode) (o := 44) (k := 2)
      (pc := 0x401359 + 3#64) (pc' := 0x40135e) (by decide) (fit 44 2) (c := .b) (rel := 0x3a) ?_
      d44 (by decide)) ?_
    · rw [eval_b_cmp, vrdx, vrdi, toNat_small hsz, toNat_small (by omega)]; simp [hsm]
    refine SPEC.trans (c_lea E (b := 0x401330) (code := mcode) (o := 46) (k := 4)
      (pc := 0x40135e) (by decide) (fit 46 4) (dst := .r8) (by decide) d46
      (a := BitVec.ofNat 64 (roundUp 16 n.toNat + 32)) (fun st hregs next => by
        rw [Silmaril.X86.Sep.Insn.memAt_addr, hregs .rdi (by decide), vrdi]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, toNat_small (by omega), toNat_small hN,
          show (BitVec.signExtend 64 (0x20 : BitVec 32)).toNat = 32 by decide +kernel,
          Nat.mod_eq_of_lt hN])) ?_
    refine SPEC.trans (c_cmp E (b := 0x401330) (code := mcode) (o := 50) (k := 3)
      (pc := 0x40135e + 4#64) (by decide) (fit 50 3) (r := .rdx) (q := .r8) (by decide)
      (by decide) (by decide) d50) ?_
    refine SPEC.conseq (entails_refl _) ?_ (sor_intro_left _ _)
    have vrdx' : (Function.update (Function.update (Function.update f .rdx (BitVec.ofNat 64 b.size))
        .rcx nxt) .r8 (BitVec.ofNat 64 (roundUp 16 n.toNat + 32))) .rdx = BitVec.ofNat 64 b.size := by
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
    by_cases hw : b.size < roundUp 16 n.toNat + 32
    · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := mcode) (o := 53) (k := 2)
        (pc := 0x40135e + 4#64 + 3#64) (pc' := 0x401380) (by decide) (fit 53 2) (c := .b)
        (rel := 0x19) ?_ d53 (by decide)) ?_
      · rw [eval_b_cmp, vrdx', Function.update_self, toNat_small hsz, toNat_small hN]; simp [hw]
      exact tailB_whole S hS x fl0 passed rest b n nxt sp ret hE _ _
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
        hn4 hfl hsmall hWF (by omega) (by omega)
    · refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := mcode) (o := 53) (k := 2)
        (pc := 0x40135e + 4#64 + 3#64) (pc' := 0x401367) (by decide) (fit 53 2) (c := .b)
        (rel := 0x19) ?_ d53 (by decide)) ?_
      · rw [eval_b_cmp, vrdx', Function.update_self, toNat_small hsz, toNat_small hN]; simp [hw]
      exact tailC_split S hS x fl0 passed rest b n nxt sp ret hE _ _
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrax])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrdi])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsi])
        (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hrsp])
        hn4 hfl hsmall hWF (by omega) h16

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

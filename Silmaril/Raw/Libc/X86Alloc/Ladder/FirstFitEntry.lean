module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitBody

/-!
# Proofs: rung 05 (first-fit) `malloc` meets `mallocSpecL` of the first-fit capacity model

The entry: requests above 4096 fail; `need = roundUp 16 n`; an empty free list fails; otherwise
`rsi` starts at the `freelist` global and the walk runs (`SPEC.loop` with `body`, measure the
length of the unvisited tail).
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
open Silmaril.Raw.Libc.X86Alloc.Loop
open Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitPost

/-- A failing call when the request is not available. -/
theorem post_fail_entry (s : List Block) (n : Word) (hna : ¬ ffCap.avail s n.toNat) :
    iface.mmS s ⊢ₛ (mallocSpecL iface).post (s, n) 0 :=
  entails_trans (spure_sep_intro ⟨rfl, hna⟩ (entails_refl _)) (sor_intro_left _ _)

/-- Refold the allocator state. -/
theorem refold (s fl0 : List Block) (h : Word) (hs : ∀ c ∈ s, c ∈ fl0) :
    (wordPt flAddr.toNat h ∗ hdrSeg fl0 h ∗ strue) ⊢ₛ iface.mmS s :=
  sexists_intro fl0 (sexists_intro h (spure_sep_intro hs (entails_refl _)))

/-- `need = roundUp 16 n` as the machine computes it. -/
theorem w_need (n : Word) (hn : n.toNat ≤ 4096) :
    Silmaril.X86.Ext.AluOp.resultN .and
      (Silmaril.X86.Ext.AluOp.resultN .add n (BitVec.signExtend 64 (0x0f : BitVec 8)))
      (BitVec.signExtend 64 (0xf0 : BitVec 8)) = BitVec.ofNat 64 (roundUp 16 n.toNat) := by
  show (n + BitVec.signExtend 64 (0x0f : BitVec 8)) &&& BitVec.signExtend 64 (0xf0 : BitVec 8) = _
  have hmask : ∀ x : Word, (x &&& BitVec.signExtend 64 (0xf0 : BitVec 8)).toNat =
      x.toNat / 16 * 16 := Silmaril.Raw.Libc.X86Alloc.Steps.toNat_and_neg16
  apply BitVec.eq_of_toNat_eq
  rw [hmask, BitVec.toNat_add,
    show (BitVec.signExtend 64 (0x0f : BitVec 8)).toNat = 15 by decide +kernel,
    Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat]
  show _ = ((n.toNat + 15) / 16 * 16) % _
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Enter the loop invariant. -/
theorem inv_intro {need : Nat} {sp ret : Word} {fl0 : List Block} {x : Ix} (F : Reg → Word)
    (fl : Flags) {M : SProp}
    (hf : F .rax = x.b.addr ∧ F .rsi = lastSlot flAddr x.passed ∧
      F .rdi = BitVec.ofNat 64 need ∧ F .rsp = sp ∧ (∀ c ∈ x.passed, c.size < need) ∧
      x.passed ++ x.b :: x.rest = fl0)
    (hM : M ⊢ₛ (wordPt sp.toNat ret ∗ plist flAddr x.passed x.b.addr ∗
      hdrSeg (x.b :: x.rest) x.b.addr ∗ strue)) :
    St 0x401352 F fl M ⊢ₛ Inv need sp ret fl0 x :=
  sexists_intro F (sexists_intro fl (spure_sep_intro hf (St_mono hM)))

/-- **`malloc`'s run, generic in the spec**: from the free list `fl0` at the `freelist` global to
`S`'s System V postcondition, given the postconditions of the exits (`Exits`). -/
theorem malloc_core (S : Silmaril.X86.Sep.FnSpec) (hS : S.stack = 0) (x : S.Arg)
    (fl0 : List Block) (h n sp ret : Word) (hE : Exits S x n fl0) (f : Reg → Word) (fl : Flags)
    (hdi : f .rdi = n) (hsp : f .rsp = sp) :
    SPEC Silmaril.X86.Open.isa (codePt 0x401330 mcode) (St 0x401330 f fl (wordPt sp.toNat ret ∗
      (wordPt flAddr.toNat h ∗ hdrSeg fl0 h ∗ strue))) (S.SysVPost x sp ret) := by
  have E := Isa.Extends.refl Silmaril.X86.Open.isa
  -- cmp $0x1000, %rdi; ja
  refine SPEC.trans (c_cmpI E (b := 0x401330) (code := mcode) (o := 0) (k := 7) (pc := 0x401330)
    rfl (fit 0 7) (r := .rdi) (imm := 0x1000) (by decide) d0) ?_
  have h4k : (BitVec.signExtend 64 (0x1000 : BitVec 32)).toNat = 4096 := by decide +kernel
  by_cases hbig : 4096 < n.toNat
  · refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := mcode) (o := 7) (k := 2)
      (pc := 0x401330 + 7#64) (pc' := 0x401390) (by decide) (fit 7 2) (c := .a) (rel := 0x57) ?_
      d7 (by decide)) ?_
    · rw [eval_a_cmp, hdi, h4k]; simp [hbig]
    refine SPEC.trans (c_xor32 E (b := 0x401330) (code := mcode) (o := 96) (k := 2)
      (pc := 0x401390) (by decide) (fit 96 2) (r := .rax) (by decide) d96) ?_
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := mcode) (o := 98)
      (k := 1) (pc := 0x401390 + 2#64) (by decide) (fit 98 1)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]) r98) ?_
    refine St_post hS (by simp only [Function.update_self]) ?_
    simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
    exact hE.big hbig h
  have hn4 : n.toNat ≤ 4096 := by omega
  refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := mcode) (o := 7) (k := 2)
    (pc := 0x401330 + 7#64) (pc' := 0x401339) (by decide) (fit 7 2) (c := .a) (rel := 0x57) ?_
    d7 (by decide)) ?_
  · rw [eval_a_cmp, hdi, h4k]; simp [hbig]
  -- load the list head, round the request
  refine SPEC.mem (M' := wordPt flAddr.toNat h ∗ (wordPt sp.toNat ret ∗ hdrSeg fl0 h ∗ strue))
    (by ac_rfl) ?_
  refine SPEC.trans (c_loadRip E (b := 0x401330) (code := mcode) (o := 9) (k := 7) (pc := 0x401339)
    (pc' := 0x401340) (by decide) (fit 9 7) (dst := .rax) (by decide) (disp := 0x1d60) d9
    (by decide) (by decide)) ?_
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := mcode) (o := 16) (k := 4) (pc := 0x401340)
    (by decide) (fit 16 4) (op := .add) (by decide) (r := .rdi) (imm := 0x0f) (by decide) d16) ?_
  refine SPEC.trans (c_aluI8 E (b := 0x401330) (code := mcode) (o := 20) (k := 4)
    (pc := 0x401340 + 4#64) (by decide) (fit 20 4) (op := .and) (by decide) (r := .rdi)
    (imm := 0xf0) (by decide) d20) ?_
  refine SPEC.trans (c_test E (b := 0x401330) (code := mcode) (o := 24) (k := 3)
    (pc := 0x401340 + 4#64 + 4#64) (by decide) (fit 24 3) (r := .rax) (by decide) d24) ?_
  cases fl0 with
  | nil =>
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜h = 0⌝ ∗ (wordPt flAddr.toNat h ∗ strue)))
      (by rw [hdrSeg_nil]; ac_rfl) ?_
    rw [St_pure]; refine SPEC.spure fun h0 => ?_
    subst h0
    refine SPEC.trans (c_jcc_taken E (b := 0x401330) (code := mcode) (o := 27) (k := 2)
      (pc := 0x401340 + 4#64 + 4#64 + 3#64) (pc' := 0x401392) (by decide) (fit 27 2) (c := .e)
      (rel := 0x45) ?_ d27 (by decide)) ?_
    · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]; rfl
    refine SPEC.conseq (entails_refl _) (c_retAt E (b := 0x401330) (code := mcode) (o := 98)
      (k := 1) (pc := 0x401392) (by decide) (fit 98 1)
      (by simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]) r98) ?_
    refine St_post hS (by simp only [Function.update_self]) ?_
    simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
    exact hE.empty rfl
  | cons b rest =>
    refine SPEC.memPre (sep_mono_right _ (sep_mono_right _ (sep_mono_left _
      (hdrSeg_head b rest h)))) ?_
    refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜h = b.addr ∧ b.WF⌝ ∗
      (wordPt flAddr.toNat h ∗ hdrSeg (b :: rest) h ∗ strue))) (by ac_rfl) ?_
    rw [St_pure]; refine SPEC.spure fun ⟨hb, hWF⟩ => ?_
    subst hb
    refine SPEC.trans (c_jcc_not E (b := 0x401330) (code := mcode) (o := 27) (k := 2)
      (pc := 0x401340 + 4#64 + 4#64 + 3#64) (pc' := 0x40134d) (by decide) (fit 27 2) (c := .e)
      (rel := 0x45) ?_ d27 (by decide)) ?_
    · rw [eval_e_test]; simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
      simpa using hWF.1
    refine SPEC.trans (c_movI32 E (b := 0x401330) (code := mcode) (o := 29) (k := 5)
      (pc := 0x40134d) (pc' := 0x401352) (by decide) (fit 29 5) (r := .rsi) (imm := 0x4030a0)
      (by decide) d29 (by decide)) ?_
    -- enter the walk
    refine SPEC.conseq ?_ (SPEC.loop μ _ (Inv (roundUp 16 n.toNat) sp ret (b :: rest)) _
      (body S hS x (b :: rest) n sp ret hE hn4) ⟨[], b, rest⟩) (entails_refl _)
    refine inv_intro _ _ ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ ?_
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte]
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, lastSlot]; rfl
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hdi]
      exact w_need n hn4
    · simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, hsp]
    · intro c hc; simp at hc
    · exact entails_of_eq (by rw [plist_nil])


/-- The exits of the live spec. -/
theorem exits_live (s fl0 : List Block) (n : Word) (hs : ∀ c ∈ s, c ∈ fl0)
    (hnd : (fl0.map Block.addr).Nodup) : Exits (mallocSpecL iface) (s, n) n fl0 := by
  have hneed : roundUp 16 n.toNat = (n.toNat + 15) / 16 * 16 := rfl
  have hn : n.toNat ≤ roundUp 16 n.toNat := by rw [hneed]; omega
  have h16 : roundUp 16 n.toNat % 16 = 0 := by rw [hneed]; omega
  refine ⟨fun hbig h => entails_trans (refold s fl0 h hs)
      (post_fail_entry s n (fun ⟨h4, _⟩ => by omega)), fun he => ?_, ?_, ?_, ?_⟩
  · subst he
    refine entails_trans ?_ (post_fail_entry s n (fun ⟨_, c, hc, _⟩ => by simpa using hs c hc))
    refine entails_trans ?_ (refold s [] 0 hs)
    exact sep_mono_right _ (spure_sep_intro rfl (entails_refl _))
  · intro _ passed b hfl hsmall hb hWF
    exact post_exhaust s fl0 passed b n hs hfl hsmall hb hWF
  · intro _ passed rest b nxt hfl _ hWF hneed' hns v hv
    exact post_whole s fl0 passed rest b n nxt hs hnd hfl hWF hneed' hns hn v hv
  · intro _ passed rest b nxt hfl _ hWF hsp v hv
    exact post_split s fl0 passed rest b n nxt hs hnd hfl hWF hsp hn h16 v hv

theorem malloc_sat_m :
    (mallocSpecL iface).Sat Silmaril.X86.Open.isa (codePt 0x401330 mcode) layout.mallocAt := by
  refine satWith_of_St rfl (fun x => x.2) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  obtain ⟨s, n⟩ := x
  change List Block at s
  dsimp only at hdi
  change SPEC _ (codePt 0x401330 mcode) (St _ f fl (wordPt sp.toNat ret ∗ sexists fun (fl0 : List Block) =>
    sexists fun (h : Word) => ⌜∀ b ∈ s, b ∈ fl0⌝ ∗ wordPt flAddr.toNat h ∗ hdrSeg fl0 h ∗ strue)) _
  rw [St_ex]; refine SPEC.sexists fun fl0 => ?_
  rw [St_ex]; refine SPEC.sexists fun h => ?_
  rw [St_pure]; refine SPEC.spure fun hs => ?_
  refine SPEC.memPre (sep_mono_right _ (sep_mono_right _ (sep_mono_left _
    (hdrSeg_nodup_entails fl0 h)))) ?_
  refine SPEC.mem (M' := wordPt sp.toNat ret ∗ (⌜(fl0.map Block.addr).Nodup⌝ ∗
    (wordPt flAddr.toNat h ∗ hdrSeg fl0 h ∗ strue))) (by ac_rfl) ?_
  rw [St_pure]; refine SPEC.spure fun hnd => ?_
  exact malloc_core (mallocSpecL iface) rfl (s, n) fl0 h n sp ret (exits_live s fl0 n hs hnd) f fl
    hdi hsp

/-- A code region that starts with `malloc`'s 128 bytes. -/
theorem code_prefix (c : List Byte) (hc : c.take 128 = mcode) :
    codePt 0x401330 c = (codePt 0x401330 mcode ∗ codePt (0x401330 + 128) (c.drop 128)) := by
  conv_lhs => rw [← List.take_append_drop 128 c]
  rw [hc, codePt, bytesAt_append, show mcode.length = 128 from hlen]
  rfl

theorem malloc_sat :
    (mallocSpecL iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt := by
  show (mallocSpecL iface).Sat _ (codePt 0x401330 code) _
  rw [code_prefix code rfl]
  exact FnSpec.SatWith.code_frame malloc_sat_m _

/-- **Rung 06's `malloc`** is the same bytes at the same address. -/
theorem malloc_sat_coalesce :
    (mallocSpecL iface).Sat Silmaril.X86.Open.isa
      Silmaril.Libc.X86Alloc.Ladder.Coalesce.layout.C layout.mallocAt := by
  show (mallocSpecL iface).Sat _ (codePt 0x401330 Silmaril.Libc.X86Alloc.Ladder.Coalesce.code) _
  rw [code_prefix _ mcode_coalesce]
  exact FnSpec.SatWith.code_frame malloc_sat_m _

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

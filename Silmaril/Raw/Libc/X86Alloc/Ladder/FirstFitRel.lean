module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitEntry

/-!
# Proofs: rung 05 (first-fit) `malloc` against the relational first-fit model `ffRel`

The walk is `malloc_core`; this file supplies its exits for the exact free list: the result is
`ffFindB`'s first fit (`ffFindB_small`, `ffFindB_hit`) and the next list is `ffTakeB`'s
(`ffTakeB_small`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Ladder.FirstFit
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Steps
open Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitPost

/-! ## First fit on the exact list -/

theorem ffFindB_small (need : Nat) : ∀ (passed l : List Block), (∀ c ∈ passed, c.size < need) →
    ffFindB need (passed ++ l) = ffFindB need l
  | [], _, _ => rfl
  | c :: passed, l, h => by
    have hc : ¬ need ≤ c.size := by have := h c List.mem_cons_self; omega
    simp only [ffFindB, List.cons_append, List.find?_cons, hc, decide_false] at *
    exact ffFindB_small need passed l (fun d hd => h d (List.mem_cons_of_mem _ hd))

theorem ffFindB_hit (need : Nat) (b : Block) (rest : List Block) (h : need ≤ b.size) :
    ffFindB need (b :: rest) = some b := by
  simp [ffFindB, List.find?_cons, h]

theorem ffTakeB_small (need : Nat) : ∀ (passed l : List Block), (∀ c ∈ passed, c.size < need) →
    ffTakeB need (passed ++ l) = passed ++ ffTakeB need l
  | [], _, _ => rfl
  | c :: passed, l, h => by
    have hc : ¬ need ≤ c.size := by have := h c List.mem_cons_self; omega
    simp only [List.cons_append, ffTakeB, hc, ite_false]
    rw [ffTakeB_small need passed l (fun d hd => h d (List.mem_cons_of_mem _ hd))]

/-- Fold a walked-over list into the exact allocator state. -/
theorem fold_exact (passed rest : List Block) (cur : Word) :
    (plist flAddr passed cur ∗ hdrSeg rest cur ∗ strue) ⊢ₛ ifaceR.mmS (passed ++ rest) := by
  refine entails_trans (entails_of_eq (sep_assoc _ _ _).symm) ?_
  refine entails_trans (sep_mono_left _ (plist_hdrSeg flAddr passed cur rest)) ?_
  rw [sexists_sep]
  exact sexists_elim fun h => sexists_intro h (entails_of_eq (sep_assoc _ _ _))

/-! ## The exits -/

theorem exits_rel (s : List Block) (n : Word) : Exits (mallocSpecR ifaceR) (s, n) n s := by
  have hneed : roundUp 16 n.toNat = (n.toNat + 15) / 16 * 16 := rfl
  have hn : n.toNat ≤ roundUp 16 n.toNat := by rw [hneed]; omega
  have h16 : roundUp 16 n.toNat % 16 = 0 := by rw [hneed]; omega
  refine ⟨fun hbig h => ?_, fun he => ?_, ?_, ?_, ?_⟩
  · -- too big
    have hm : ffRel.malloc s n.toNat = 0 := by simp [ffRel, hbig]
    show _ ⊢ₛ (⌜(0 : Word) = ffRel.malloc s n.toNat⌝ ∗ sor (⌜(0 : Word) = 0⌝ ∗ ifaceR.mmS s) _)
    exact spure_sep_intro hm.symm (entails_trans (spure_sep_intro rfl
      (sexists_intro h (entails_refl _))) (sor_intro_left _ _))
  · -- empty list
    subst he
    have hm : ffRel.malloc [] n.toNat = 0 := by simp [ffRel, ffFindB]
    show _ ⊢ₛ (⌜(0 : Word) = ffRel.malloc [] n.toNat⌝ ∗ sor (⌜(0 : Word) = 0⌝ ∗ ifaceR.mmS []) _)
    refine spure_sep_intro hm.symm (entails_trans (spure_sep_intro rfl
      (sexists_intro (0 : Word) ?_)) (sor_intro_left _ _))
    rw [hdrSeg_nil]
    exact sep_mono_right _ (spure_sep_intro rfl (entails_refl _))
  · -- list exhausted
    intro hn4 passed b hfl hsmall hb hWF
    have hm : ffRel.malloc s n.toNat = 0 := by
      subst hfl
      have h1 := ffFindB_small (roundUp 16 n.toNat) passed [b] hsmall
      have hnb : ¬ roundUp 16 n.toNat ≤ b.size := by omega
      have h2 : ffFindB (roundUp 16 n.toNat) [b] = none := by
        simp [ffFindB, List.find?_cons, hnb]
      simp [ffRel, show ¬ 4096 < n.toNat by omega, h1, h2]
    show _ ⊢ₛ (⌜(0 : Word) = ffRel.malloc s n.toNat⌝ ∗ sor (⌜(0 : Word) = 0⌝ ∗ ifaceR.mmS s) _)
    refine spure_sep_intro hm.symm (entails_trans (spure_sep_intro rfl ?_) (sor_intro_left _ _))
    have e := plist_snoc flAddr passed b 0
    refine entails_trans (entails_of_eq (show _ = ((plist flAddr passed b.addr ∗ ⌜b.WF⌝ ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ blockAny (b.addr.toNat + 16) b.size ∗
      wordPt (b.addr + 8#64).toNat 0) ∗ hdrSeg [] 0 ∗ strue) from ?_)) ?_
    · rw [hdrSeg_nil]
      rw [show (⌜b.WF⌝ : SProp) = emp from ?_, show (⌜(0 : Word) = 0⌝ : SProp) = emp from ?_]
      · simp only [emp_sep]; ac_rfl
      · rw [← spure_true_emp]; simp
      · rw [← spure_true_emp]; simp [hWF]
    rw [e, ← hfl]
    simpa using fold_exact (passed ++ [b]) [] 0
  · -- served whole
    intro hn4 passed rest b nxt hfl hsmall hWF hneed' hns v hv
    subst hv
    obtain ⟨hvs, hvn, hv0, hv16⟩ := v_facts b hWF
    have hm : ffRel.malloc s n.toNat = b.addr + 16#64 := by
      subst hfl
      simp [ffRel, show ¬ 4096 < n.toNat by omega, ffFindB_small _ passed _ hsmall,
        ffFindB_hit _ b rest hneed']
    have ha : ffRel.alloc s n.toNat = passed ++ rest := by
      subst hfl
      show ffTakeB _ _ = _
      rw [ffTakeB_small _ passed _ hsmall]
      simp [ffTakeB, hneed', hns]
    have hpay : blockAny (b.addr.toNat + 16) b.size =
        (blockAny (b.addr + 16#64).toNat n.toNat ∗
          blockAny ((b.addr + 16#64).toNat + n.toNat) (b.size - n.toNat)) := by
      rw [← blockAny_add, hvn, Nat.add_sub_cancel' (by omega)]
    show _ ⊢ₛ (⌜b.addr + 16#64 = ffRel.malloc s n.toNat⌝ ∗ sor _
      ((⌜b.addr + 16#64 ≠ 0 ∧ (b.addr + 16#64).toNat % 16 = 0⌝ ∗
      (sexists fun (sz : Nat) => ⌜n.toNat ≤ sz ∧ (Block.WF ⟨(b.addr + 16#64) - 16#64, sz⟩) ∧
        b.addr + 16#64 = ((b.addr + 16#64) - 16#64) + 16#64⌝ ∗
        wordPt ((b.addr + 16#64) - 16#64).toNat (BitVec.ofNat 64 sz) ∗
        blockAny (((b.addr + 16#64) - 16#64) + 8#64).toNat 8 ∗
        blockAny ((b.addr + 16#64).toNat + n.toNat) (sz - n.toNat)) ∗
      blockAny (b.addr + 16#64).toNat n.toNat) ∗ ifaceR.mmS (ffRel.alloc s n.toNat)))
    refine spure_sep_intro hm.symm (entails_trans ?_ (sor_intro_right _ _))
    rw [hpay, hvs, ha]
    refine entails_trans ?_ (sep_mono_left _ (spure_sep_intro ⟨hv0, hv16⟩ (sep_mono_left _
      (sexists_intro b.size (spure_sep_intro ⟨by omega, hWF, rfl⟩ (entails_refl _))))))
    refine entails_trans ?_ (sep_mono_right _ (fold_exact passed rest nxt))
    rw [plist_last]
    refine entails_trans (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (sep_mono_left _ (wordPt_blockAny _ _))))) (entails_of_eq ?_)
    ac_rfl
  · -- split
    intro hn4 passed rest b nxt hfl hsmall hWF hsp v hv
    subst hv
    obtain ⟨hvs, hvn, hv0, hv16⟩ := v_facts b hWF
    obtain ⟨-, hrWF⟩ := rem_facts b _ hWF h16 hsp
    have hm : ffRel.malloc s n.toNat = b.addr + 16#64 := by
      subst hfl
      simp [ffRel, show ¬ 4096 < n.toNat by omega, ffFindB_small _ passed _ hsmall,
        ffFindB_hit _ b rest (by omega : roundUp 16 n.toNat ≤ b.size)]
    have ha : ffRel.alloc s n.toNat = passed ++ rem b (roundUp 16 n.toNat) :: rest := by
      subst hfl
      show ffTakeB _ _ = _
      rw [ffTakeB_small _ passed _ hsmall]
      simp [ffTakeB, show roundUp 16 n.toNat ≤ b.size by omega, hsp]
    have hpay : blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) =
        (blockAny (b.addr + 16#64).toNat n.toNat ∗
          blockAny ((b.addr + 16#64).toNat + n.toNat) (roundUp 16 n.toNat - n.toNat)) := by
      rw [← blockAny_add, hvn, Nat.add_sub_cancel' hn]
    show _ ⊢ₛ (⌜b.addr + 16#64 = ffRel.malloc s n.toNat⌝ ∗ sor _
      ((⌜b.addr + 16#64 ≠ 0 ∧ (b.addr + 16#64).toNat % 16 = 0⌝ ∗
      (sexists fun (sz : Nat) => ⌜n.toNat ≤ sz ∧ (Block.WF ⟨(b.addr + 16#64) - 16#64, sz⟩) ∧
        b.addr + 16#64 = ((b.addr + 16#64) - 16#64) + 16#64⌝ ∗
        wordPt ((b.addr + 16#64) - 16#64).toNat (BitVec.ofNat 64 sz) ∗
        blockAny (((b.addr + 16#64) - 16#64) + 8#64).toNat 8 ∗
        blockAny ((b.addr + 16#64).toNat + n.toNat) (sz - n.toNat)) ∗
      blockAny (b.addr + 16#64).toNat n.toNat) ∗ ifaceR.mmS (ffRel.alloc s n.toNat)))
    refine spure_sep_intro hm.symm (entails_trans ?_ (sor_intro_right _ _))
    rw [hpay, hvs, ha]
    have hbWF : Block.WF ⟨b.addr, roundUp 16 n.toNat⟩ :=
      ⟨hWF.1, hWF.2.1, by have := hWF.2.2; simp only at this ⊢; omega⟩
    refine entails_trans ?_ (sep_mono_left _ (spure_sep_intro ⟨hv0, hv16⟩ (sep_mono_left _
      (sexists_intro (roundUp 16 n.toNat) (spure_sep_intro ⟨hn, hbWF, rfl⟩ (entails_refl _))))))
    refine entails_trans ?_ (sep_mono_right _
      (fold_exact passed (rem b (roundUp 16 n.toNat) :: rest) (rem b (roundUp 16 n.toNat)).addr))
    rw [plist_last, hdrSeg_cons]
    refine entails_trans (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (sep_mono_left _ (wordPt_blockAny _ _))))) ?_
    have hφ : (rem b (roundUp 16 n.toNat)).addr = (rem b (roundUp 16 n.toNat)).addr ∧
        (rem b (roundUp 16 n.toNat)).WF := ⟨rfl, hrWF⟩
    refine entails_trans ?_ (sep_mono_right _ (sep_mono_right _ (sep_mono_left _
      (spure_sep_intro hφ (sexists_intro nxt (entails_refl _))))))
    exact entails_of_eq (by ac_rfl)

/-- **`malloc` returns the first fit of the exact free list.** -/
theorem malloc_sat_rel :
    (mallocSpecR ifaceR).Sat Silmaril.X86.Open.isa (codePt 0x401330 mcode) layout.mallocAt := by
  refine satWith_of_St rfl (fun x => x.2) (fun _ => rfl) fun x sp ret f fl _ hsp hdi => ?_
  obtain ⟨s, n⟩ := x
  change List Block at s
  dsimp only at hdi
  change SPEC _ (codePt 0x401330 mcode) (St _ f fl (wordPt sp.toNat ret ∗ sexists fun (h : Word) =>
    wordPt flAddr.toNat h ∗ hdrSeg s h ∗ strue)) _
  rw [St_ex]; refine SPEC.sexists fun h => ?_
  exact malloc_core (mallocSpecR ifaceR) rfl (s, n) s h n sp ret (exits_rel s n) f fl hdi hsp

theorem malloc_sat_rel_full :
    (mallocSpecR ifaceR).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt := by
  show (mallocSpecR ifaceR).Sat _ (codePt 0x401330 code) _
  rw [code_prefix code rfl]
  exact FnSpec.SatWith.code_frame malloc_sat_rel _

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc

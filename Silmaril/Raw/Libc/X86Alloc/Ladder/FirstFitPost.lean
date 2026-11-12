module

public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Live
public import Silmaril.Raw.Libc.X86Alloc.HdrSeg
public import Silmaril.X86.Sep.Alloc.Thms
public import Mathlib.Data.List.Nodup

/-!
# Proofs: rung 05 (first-fit) `malloc` — the postconditions of its exits

Pure separation-logic lemmas, one per exit of the walk: the list exhausted (`post_exhaust`), a
block served whole (`post_whole`), a block split (`post_split`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitPost

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Ladder.FirstFit

/-- Fold a walked-over list back into the allocator state. -/
theorem fold_mm (s : List Block) (passed rest : List Block) (cur : Word)
    (hs : ∀ c ∈ s, c ∈ passed ++ rest) :
    (plist flAddr passed cur ∗ hdrSeg rest cur ∗ strue) ⊢ₛ iface.mmS s := by
  refine entails_trans (entails_of_eq (sep_assoc _ _ _).symm) ?_
  refine entails_trans (sep_mono_left _ (plist_hdrSeg flAddr passed cur rest)) ?_
  rw [sexists_sep]
  refine sexists_elim fun h => ?_
  refine sexists_intro (passed ++ rest) (sexists_intro h ?_)
  refine spure_sep_intro hs (entails_of_eq ?_)
  show ((wordPt flAddr.toNat h ∗ hdrSeg (passed ++ rest) h) ∗ strue) = _
  rw [sep_assoc]

/-- **The list exhausted**: every block was too small, so the request was not available. -/
theorem post_exhaust (s fl0 passed : List Block) (b : Block) (n : Word)
    (hs : ∀ c ∈ s, c ∈ fl0) (hfl : passed ++ [b] = fl0)
    (hsmall : ∀ c ∈ passed, c.size < roundUp 16 n.toNat) (hb : b.size < roundUp 16 n.toNat)
    (hWF : b.WF) :
    (plist flAddr passed b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      wordPt (b.addr + 8#64).toNat 0 ∗ blockAny (b.addr.toNat + 16) b.size ∗ strue) ⊢ₛ
      (mallocSpecL iface).post (s, n) 0 := by
  have hna : ¬ ffCap.avail s n.toNat := by
    rintro ⟨-, c, hc, hcs⟩
    have := hs c hc
    rw [← hfl, List.mem_append, List.mem_singleton] at this
    rcases this with h | rfl
    · have := hsmall c h; omega
    · omega
  refine entails_trans ?_ (sor_intro_left _ _)
  refine spure_sep_intro ⟨rfl, hna⟩ ?_
  have e := plist_snoc flAddr passed b 0
  refine entails_trans (entails_of_eq (show _ = ((plist flAddr passed b.addr ∗ ⌜b.WF⌝ ∗
    wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ blockAny (b.addr.toNat + 16) b.size ∗
    wordPt (b.addr + 8#64).toNat 0) ∗ hdrSeg [] 0 ∗ strue) from ?_)) ?_
  · rw [hdrSeg_nil]
    rw [show (⌜b.WF⌝ : SProp) = emp from ?_, show (⌜(0 : Word) = 0⌝ : SProp) = emp from ?_]
    · simp only [emp_sep]; ac_rfl
    · rw [← spure_true_emp]; simp
    · rw [← spure_true_emp]; simp [hWF]
  rw [e]
  refine fold_mm s (passed ++ [b]) [] 0 ?_
  simpa [hfl] using hs

/-- **The abstract state after serving `b`** lies in the real list after the walk. -/
theorem alloc_sub (s fl0 passed rest : List Block) (b : Block) (n : Nat)
    (hs : ∀ c ∈ s, c ∈ fl0) (hnd : (fl0.map Block.addr).Nodup) (hfl : passed ++ b :: rest = fl0) :
    ∀ c ∈ ffAlloc s n (b.addr + 16#64),
      c ∈ passed ++ (if roundUp 16 n + 32 ≤ b.size then [rem b (roundUp 16 n)] else []) ++ rest := by
  have hb0 : b ∈ fl0 := by rw [← hfl]; simp
  have other : ∀ c ∈ s, c ≠ b → c ∈ passed ++ rest := by
    intro c hc hne
    have := hs c hc
    rw [← hfl] at this
    simp only [List.mem_append, List.mem_cons] at this ⊢
    rcases this with h | h | h
    · exact .inl h
    · exact absurd h hne
    · exact .inr h
  intro c hc
  unfold ffAlloc at hc
  cases hfind : s.find? (fun d => d.addr + 16#64 = b.addr + 16#64) with
  | none =>
    rw [hfind] at hc
    have hne : c ≠ b := by
      rintro rfl
      have := List.find?_eq_none.1 hfind c hc
      simp at this
    have := other c hc hne
    simp only [List.mem_append] at this ⊢
    rcases this with h | h
    · exact .inl (.inl h)
    · exact .inr h
  | some b' =>
    rw [hfind] at hc
    have hb's : b' ∈ s := List.mem_of_find?_eq_some hfind
    have hb'a : b'.addr = b.addr := by
      have := List.find?_some hfind
      simpa using this
    have hb'b : b' = b := List.inj_on_of_nodup_map hnd (hs b' hb's) hb0 hb'a
    subst hb'b
    simp only [List.mem_append, List.mem_filter] at hc
    rcases hc with ⟨hcs, hca⟩ | hc
    · have hne : c ≠ b' := by rintro rfl; simp at hca
      have := other c hcs hne
      simp only [List.mem_append] at this ⊢
      rcases this with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · simp only [List.mem_append]
      exact .inl (.inr hc)

/-- The returned block's address. -/
theorem v_facts (b : Block) (hWF : b.WF) :
    (b.addr + 16#64) - 16#64 = b.addr ∧ (b.addr + 16#64).toNat = b.addr.toNat + 16 ∧
      b.addr + 16#64 ≠ 0 ∧ (b.addr + 16#64).toNat % 16 = 0 := by
  obtain ⟨-, h16, hb⟩ := hWF
  have e : (b.addr + 16#64).toNat = b.addr.toNat + 16 := by
    rw [BitVec.toNat_add, show (16#64 : Word).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine ⟨BitVec.add_sub_cancel _ _, e, fun h0 => ?_, by rw [e]; omega⟩
  have := congrArg BitVec.toNat h0
  rw [e] at this; simp at this

/-- **A block served whole** (no split). -/
theorem post_whole (s fl0 passed rest : List Block) (b : Block) (n nxt : Word)
    (hs : ∀ c ∈ s, c ∈ fl0) (hnd : (fl0.map Block.addr).Nodup) (hfl : passed ++ b :: rest = fl0)
    (hWF : b.WF) (hneed : roundUp 16 n.toNat ≤ b.size) (hns : ¬ roundUp 16 n.toNat + 32 ≤ b.size)
    (hn : n.toNat ≤ roundUp 16 n.toNat) (v : Word) (hv : v = b.addr + 16#64) :
    (plistO flAddr passed ∗ wordPt (lastSlot flAddr passed).toNat nxt ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt ∗ strue) ⊢ₛ
      (mallocSpecL iface).post (s, n) v := by
  subst hv
  obtain ⟨hvs, hvn, hv0, hv16⟩ := v_facts b hWF
  refine entails_trans ?_ (sor_intro_right _ _)
  have hsub := alloc_sub s fl0 passed rest b n.toNat hs hnd hfl
  simp only [hns, ite_false, List.append_nil] at hsub
  have hpay : blockAny (b.addr.toNat + 16) b.size =
      (blockAny (b.addr + 16#64).toNat n.toNat ∗
        blockAny ((b.addr + 16#64).toNat + n.toNat) (b.size - n.toNat)) := by
    rw [← blockAny_add, hvn, Nat.add_sub_cancel' (by omega)]
  rw [hpay]
  show _ ⊢ₛ ((⌜b.addr + 16#64 ≠ 0 ∧ (b.addr + 16#64).toNat % 16 = 0⌝ ∗
      (sexists fun (sz : Nat) => ⌜n.toNat ≤ sz ∧ (Block.WF ⟨(b.addr + 16#64) - 16#64, sz⟩) ∧
        b.addr + 16#64 = ((b.addr + 16#64) - 16#64) + 16#64⌝ ∗
        wordPt ((b.addr + 16#64) - 16#64).toNat (BitVec.ofNat 64 sz) ∗
        blockAny (((b.addr + 16#64) - 16#64) + 8#64).toNat 8 ∗
        blockAny ((b.addr + 16#64).toNat + n.toNat) (sz - n.toNat)) ∗
      blockAny (b.addr + 16#64).toNat n.toNat) ∗ iface.mmS (ffCap.alloc s n.toNat (b.addr + 16#64)))
  rw [hvs]
  refine entails_trans ?_ (sep_mono_left _ (spure_sep_intro ⟨hv0, hv16⟩ (sep_mono_left _
    (sexists_intro b.size (spure_sep_intro ⟨by omega, hWF, rfl⟩ (entails_refl _))))))
  refine entails_trans ?_ (sep_mono_right _ (fold_mm _ passed rest nxt hsub))
  rw [plist_last]
  refine entails_trans (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_left _ (wordPt_blockAny _ _))))) (entails_of_eq ?_)
  ac_rfl

/-- The split remainder's address does not wrap, and the remainder is well formed. -/
theorem rem_facts (b : Block) (need : Nat) (hWF : b.WF) (h16 : need % 16 = 0)
    (hsp : need + 32 ≤ b.size) :
    (rem b need).addr.toNat = b.addr.toNat + 16 + need ∧ (rem b need).WF := by
  obtain ⟨-, ha, hb⟩ := hWF
  have e : (rem b need).addr.toNat = b.addr.toNat + 16 + need := by
    show (b.addr + BitVec.ofNat 64 (16 + need)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + need) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨e, fun h0 => ?_, by rw [e]; omega, by rw [e]; show _ + 16 + (b.size - need - 16) < _; omega⟩
  have := congrArg BitVec.toNat h0
  rw [e] at this; simp at this

/-- **A block split**: the first `need` bytes served, the remainder takes its place. -/
theorem post_split (s fl0 passed rest : List Block) (b : Block) (n nxt : Word)
    (hs : ∀ c ∈ s, c ∈ fl0) (hnd : (fl0.map Block.addr).Nodup) (hfl : passed ++ b :: rest = fl0)
    (hWF : b.WF) (hsp : roundUp 16 n.toNat + 32 ≤ b.size) (hn : n.toNat ≤ roundUp 16 n.toNat)
    (h16 : roundUp 16 n.toNat % 16 = 0) (v : Word) (hv : v = b.addr + 16#64) :
    (plistO flAddr passed ∗ wordPt (lastSlot flAddr passed).toNat (rem b (roundUp 16 n.toNat)).addr ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 (roundUp 16 n.toNat)) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) ∗
      wordPt (rem b (roundUp 16 n.toNat)).addr.toNat
        (BitVec.ofNat 64 (rem b (roundUp 16 n.toNat)).size) ∗
      wordPt ((rem b (roundUp 16 n.toNat)).addr + 8#64).toNat nxt ∗
      blockAny ((rem b (roundUp 16 n.toNat)).addr.toNat + 16) (rem b (roundUp 16 n.toNat)).size ∗
      hdrSeg rest nxt ∗ strue) ⊢ₛ
      (mallocSpecL iface).post (s, n) v := by
  subst hv
  obtain ⟨hvs, hvn, hv0, hv16⟩ := v_facts b hWF
  obtain ⟨-, hrWF⟩ := rem_facts b _ hWF h16 hsp
  refine entails_trans ?_ (sor_intro_right _ _)
  have hsub := alloc_sub s fl0 passed rest b n.toNat hs hnd hfl
  simp only [hsp, ite_true] at hsub
  have hpay : blockAny (b.addr.toNat + 16) (roundUp 16 n.toNat) =
      (blockAny (b.addr + 16#64).toNat n.toNat ∗
        blockAny ((b.addr + 16#64).toNat + n.toNat) (roundUp 16 n.toNat - n.toNat)) := by
    rw [← blockAny_add, hvn, Nat.add_sub_cancel' hn]
  rw [hpay]
  show _ ⊢ₛ ((⌜b.addr + 16#64 ≠ 0 ∧ (b.addr + 16#64).toNat % 16 = 0⌝ ∗
      (sexists fun (sz : Nat) => ⌜n.toNat ≤ sz ∧ (Block.WF ⟨(b.addr + 16#64) - 16#64, sz⟩) ∧
        b.addr + 16#64 = ((b.addr + 16#64) - 16#64) + 16#64⌝ ∗
        wordPt ((b.addr + 16#64) - 16#64).toNat (BitVec.ofNat 64 sz) ∗
        blockAny (((b.addr + 16#64) - 16#64) + 8#64).toNat 8 ∗
        blockAny ((b.addr + 16#64).toNat + n.toNat) (sz - n.toNat)) ∗
      blockAny (b.addr + 16#64).toNat n.toNat) ∗ iface.mmS (ffCap.alloc s n.toNat (b.addr + 16#64)))
  rw [hvs]
  have hbWF : Block.WF ⟨b.addr, roundUp 16 n.toNat⟩ :=
    ⟨hWF.1, hWF.2.1, by have := hWF.2.2; simp only at this ⊢; omega⟩
  refine entails_trans ?_ (sep_mono_left _ (spure_sep_intro ⟨hv0, hv16⟩ (sep_mono_left _
    (sexists_intro (roundUp 16 n.toNat) (spure_sep_intro ⟨hn, hbWF, rfl⟩ (entails_refl _))))))
  refine entails_trans ?_ (sep_mono_right _
    (fold_mm _ passed (rem b (roundUp 16 n.toNat) :: rest) (rem b (roundUp 16 n.toNat)).addr ?_))
  · rw [plist_last, hdrSeg_cons]
    refine entails_trans (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (sep_mono_left _ (wordPt_blockAny _ _))))) ?_
    have hφ : (rem b (roundUp 16 n.toNat)).addr = (rem b (roundUp 16 n.toNat)).addr ∧
        (rem b (roundUp 16 n.toNat)).WF := ⟨rfl, hrWF⟩
    refine entails_trans ?_ (sep_mono_right _ (sep_mono_right _ (sep_mono_left _
      (spure_sep_intro hφ (sexists_intro nxt (entails_refl _))))))
    exact entails_of_eq (by ac_rfl)
  · intro c hc
    have := hsub c hc
    simpa [List.mem_append, or_assoc] using this

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitPost

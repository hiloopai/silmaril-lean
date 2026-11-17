module

public import Silmaril.Data.Layout.Bitfield.Defs
public import Silmaril.Data.Layout.Thms

/-! # Proofs of `Silmaril.Data.Layout.Bitfield` -/

@[expose] public section

namespace Silmaril.Proofs.Data.Layout.Bitfield

open Silmaril.Data.Layout

theorem le_alignUp' (n a : Nat) : n ≤ alignUp n a := by
  by_cases h : a = 0
  · simp [alignUp, h]
  · exact le_alignUp n (Nat.pos_of_ne_zero h)

theorem le_base (c : BCur) : c.pos ≤ c.base := by
  unfold BCur.base; split <;> omega

/-- **One step** starts at or after the current bit and ends at or before the next one. -/
theorem bitStep_spec {pol : BitPolicy} {c c' : BCur} {m : BMember} {p : Nat}
    (h : bitStep pol c m = .ok (p, c')) : c.pos ≤ p ∧ p + m.width ≤ c'.pos := by
  have hb := le_base c
  unfold bitStep at h
  cases hm : m.bits with
  | none =>
    simp only [hm] at h
    cases h
    refine ⟨Nat.le_trans hb (le_alignUp' _ _), ?_⟩
    simp [BMember.width, hm]
  | some w =>
    simp only [hm] at h
    split at h
    · cases h
    split at h
    · cases h
    have hw : m.width = w := by simp [BMember.width, hm]
    rw [hw]
    cases pol with
    | sysv =>
      simp only at h
      split at h
      · cases h; rename_i hz; subst hz; exact ⟨le_alignUp' _ _, by simp⟩
      · cases h
        refine ⟨?_, Nat.le_refl _⟩
        split
        · exact Nat.le_refl _
        · exact le_alignUp' _ _
    | ms =>
      simp only at h
      split at h
      · cases h; rename_i hz; subst hz; exact ⟨hb, by simp⟩
      · split at h
        · split at h
          · cases h; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
          · cases h; exact ⟨Nat.le_trans hb (le_alignUp' _ _), Nat.le_refl _⟩
        · cases h; exact ⟨le_alignUp' _ _, Nat.le_refl _⟩

/-- Slots in increasing order without overlap, all at or after `lo`. -/
def BChain : Nat → List BitSlot → Prop
  | _, [] => True
  | lo, s :: ss => lo ≤ s.off ∧ BChain (s.off + s.width) ss

theorem bitPlace_spec {pol : BitPolicy} : ∀ {c c'' : BCur} {ms : List BMember} {ss : List BitSlot},
    bitPlace pol c ms = .ok (ss, c'') →
      BChain c.pos ss ∧ (∀ s ∈ ss, s.off + s.width ≤ c''.pos) ∧ c.pos ≤ c''.pos
  | c, c'', [], ss, h => by
    simp only [bitPlace] at h; cases h; exact ⟨trivial, by simp, Nat.le_refl _⟩
  | c, c'', m :: ms, ss, h => by
    simp only [bitPlace] at h
    split at h
    · cases h
    rename_i p c' hs
    split at h
    · cases h
    rename_i ss' c3 hr
    cases h
    obtain ⟨h1, h2⟩ := bitStep_spec hs
    obtain ⟨r1, r2, r3⟩ := bitPlace_spec hr
    refine ⟨⟨h1, ?_⟩, ?_, by omega⟩
    · -- the chain continues from the end of this slot (the next state's bit is at least that)
      exact chain_mono (by simpa [BMember.width] using h2) r1
    · intro s hs'
      simp only [List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · simp only; omega
      · exact r2 s hs'
where
  chain_mono : ∀ {lo lo' : Nat} {ss : List BitSlot}, lo ≤ lo' → BChain lo' ss → BChain lo ss
    | _, _, [], _, _ => trivial
    | _, _, _ :: _, hl, ⟨h, r⟩ => ⟨Nat.le_trans hl h, r⟩

theorem chain_lower : ∀ {lo : Nat} {ss : List BitSlot}, BChain lo ss → ∀ t ∈ ss, lo ≤ t.off
  | _, [], _, _, h => by simp at h
  | _, s :: ss, ⟨h, r⟩, t, ht => by
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact h
    · exact Nat.le_trans (Nat.le_trans h (Nat.le_add_right _ _)) (chain_lower r t ht)

theorem chain_pairwise : ∀ {lo : Nat} {ss : List BitSlot}, BChain lo ss →
    ss.Pairwise fun a b => a.off + a.width ≤ b.off
  | _, [], _ => List.Pairwise.nil
  | _, _ :: _, ⟨_, r⟩ => List.Pairwise.cons (fun t ht => chain_lower r t ht) (chain_pairwise r)

theorem bytesOf_spec (n : Nat) : n ≤ 8 * bytesOf n := by unfold bytesOf; omega

/-- **A struct with bit-fields is well formed**: slots pairwise disjoint and in increasing order,
every slot inside the record. -/
theorem bitStruct_wf {pol : BitPolicy} {ms : List BMember} {ss : List BitSlot} {sh : Shape}
    (h : bitStruct pol ms = .ok (ss, sh)) :
    (ss.Pairwise fun a b => a.off + a.width ≤ b.off) ∧ ∀ s ∈ ss, s.off + s.width ≤ 8 * sh.size := by
  unfold bitStruct at h
  split at h
  · cases h
  rename_i ss' c hp
  cases h
  obtain ⟨r1, r2, -⟩ := bitPlace_spec hp
  refine ⟨chain_pairwise r1, fun s hs => ?_⟩
  have := r2 s hs
  have h1 := le_base c
  have h2 := bytesOf_spec c.base
  have h3 := le_alignUp' (bytesOf c.base) c.align
  simp only
  omega

theorem foldl_max_ge {α : Type} (f : α → Nat) : ∀ (l : List α) (e : Nat),
    e ≤ l.foldl (fun e m => max e (f m)) e ∧ ∀ m ∈ l, f m ≤ l.foldl (fun e m => max e (f m)) e
  | [], e => ⟨Nat.le_refl _, by simp⟩
  | m :: l, e => by
    obtain ⟨h1, h2⟩ := foldl_max_ge f l (max e (f m))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun x hx => ?_⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

/-- **A union with bit-fields**: every slot starts at bit 0 and lies inside the record. -/
theorem bitUnion_wf {pol : BitPolicy} {ms : List BMember} {ss : List BitSlot} {sh : Shape}
    (h : bitUnion pol ms = .ok (ss, sh)) : ∀ s ∈ ss, s.off = 0 ∧ s.width ≤ 8 * sh.size := by
  unfold bitUnion at h
  split at h
  · cases h
  cases h
  intro s hs
  simp only [List.mem_map] at hs
  obtain ⟨m, hm, rfl⟩ := hs
  refine ⟨rfl, ?_⟩
  have h0 : m.width ≤ unionExtent pol m := by
    unfold unionExtent; split <;> omega
  have h1 := (foldl_max_ge (unionExtent pol) ms 0).2 m hm
  have h2 := bytesOf_spec (ms.foldl (fun e m => max e (unionExtent pol m)) 0)
  have h3 := le_alignUp' (bytesOf (ms.foldl (fun e m => max e (unionExtent pol m)) 0))
    (ms.foldl (fun a m => max a (unionAlign pol m)) 1)
  simp only
  omega

end Silmaril.Proofs.Data.Layout.Bitfield

namespace Silmaril.Proofs.Data.Layout.Bitfield

open Silmaril.Data.Layout

theorem wf_of (a k size : Nat) (h : a = 2 ^ k) (hd : a ∣ size) : (⟨size, a⟩ : Shape).WF :=
  ⟨⟨k, h⟩, hd⟩

theorem msX64_wf : msX64.WF where
  int k s h := by
    cases k <;> simp only [msX64, Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;>
      first
      | exact exactShape_wf h
      | exact wf_of 1 0 _ rfl (by decide) | exact wf_of 2 1 _ rfl (by decide)
      | exact wf_of 4 2 _ rfl (by decide) | exact wf_of 8 3 _ rfl (by decide)
  float k s h := by
    cases k <;> simp only [msX64, Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;>
      first
      | exact wf_of 4 2 _ rfl (by decide) | exact wf_of 8 3 _ rfl (by decide)
  ptr := wf_of 8 3 _ rfl (by decide)
  bool := wf_of 1 0 _ rfl (by decide)

end Silmaril.Proofs.Data.Layout.Bitfield

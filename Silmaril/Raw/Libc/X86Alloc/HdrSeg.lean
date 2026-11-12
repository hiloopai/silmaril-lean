module

public import Silmaril.Libc.X86Alloc.HdrSeg.Defs
public import Silmaril.X86.Sep.Thms
public import Silmaril.X86.Sep.Extra.Thms

/-!
# Proofs: the header list-segment laws

* `plist_hdrSeg`: an open segment `plist prev passed cur` and a tail `hdrSeg rest cur` join into
  `∃ h, wordPt prev h ∗ hdrSeg (passed ++ rest) h` — the fold that closes a free-list walk (the
  slot at `prev`, e.g. the `freelist` global, holds the head `h` of the joined list).
* `hdrSeg_cons`, `plist_nil`, `plist_cons`: unfolding.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Libc.X86Alloc

open Silmaril.X86 (Word)
open Silmaril.X86.Sep

theorem hdrSeg_nil (head : Word) : hdrSeg [] head = ⌜head = 0⌝ := rfl

theorem hdrSeg_cons (b : Block) (rest : List Block) (head : Word) :
    hdrSeg (b :: rest) head = (⌜head = b.addr ∧ b.WF⌝ ∗ sexists fun nxt =>
      wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
      blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt) := rfl

theorem plist_nil (prev cur : Word) : plist prev [] cur = wordPt prev.toNat cur := rfl

theorem plist_cons (prev : Word) (b : Block) (rest : List Block) (cur : Word) :
    plist prev (b :: rest) cur = (⌜b.WF⌝ ∗ wordPt prev.toNat b.addr ∗
      wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ blockAny (b.addr.toNat + 16) b.size ∗
      plist (b.addr + 8#64) rest cur) := rfl

/-- **Join**: an open segment and the tail it points to form one `hdrSeg`, whose head is the
value in the slot at `prev`. -/
theorem plist_hdrSeg (prev : Word) :
    ∀ (passed : List Block) (cur : Word) (rest : List Block),
      (plist prev passed cur ∗ hdrSeg rest cur) ⊢ₛ
        sexists fun h => wordPt prev.toNat h ∗ hdrSeg (passed ++ rest) h
  | [], cur, rest => by
    rw [plist_nil, List.nil_append]
    exact sexists_intro cur (entails_refl _)
  | b :: passed, cur, rest => by
    rw [plist_cons]
    refine sexists_intro b.addr ?_
    rw [sep_assoc]
    -- peel the pure WF and reassociate: wordPt prev b.addr frames out, the rest is the IH
    refine spure_sep_elim fun hWF => ?_
    refine entails_trans (entails_of_eq (show _ =
        (wordPt prev.toNat b.addr ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
          blockAny (b.addr.toNat + 16) b.size ∗
          (plist (b.addr + 8#64) passed cur ∗ hdrSeg rest cur)) by ac_rfl)) ?_
    refine entails_trans (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (plist_hdrSeg _ passed cur rest)))) ?_
    simp only [sep_sexists]
    refine sexists_elim fun h' => ?_
    rw [List.cons_append, hdrSeg_cons]
    refine sep_mono_right _ (spure_sep_intro (show b.addr = b.addr ∧ b.WF from ⟨rfl, hWF⟩)
      (sexists_intro h' (entails_of_eq ?_)))
    ac_rfl

/-! ## Walking: extend a segment, split off its final slot -/

theorem lastSlot_snoc : ∀ (prev : Word) (passed : List Block) (b : Block),
    lastSlot prev (passed ++ [b]) = b.addr + 8#64
  | _, [], _ => rfl
  | _, c :: passed, b => lastSlot_snoc (c.addr + 8#64) passed b

/-- **Extend** an open segment by the block it points to. -/
theorem plist_snoc : ∀ (prev : Word) (passed : List Block) (b : Block) (cur : Word),
    (plist prev passed b.addr ∗ ⌜b.WF⌝ ∗ wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
      blockAny (b.addr.toNat + 16) b.size ∗ wordPt (b.addr + 8#64).toNat cur) =
      plist prev (passed ++ [b]) cur
  | prev, [], b, cur => by
    simp only [plist_nil, List.nil_append, plist_cons]; ac_rfl
  | prev, c :: passed, b, cur => by
    rw [plist_cons, List.cons_append, plist_cons, ← plist_snoc (c.addr + 8#64) passed b cur]
    ac_rfl

/-- **Split off the final link slot** of an open segment. -/
theorem plist_last : ∀ (prev : Word) (passed : List Block) (cur : Word),
    plist prev passed cur = (plistO prev passed ∗ wordPt (lastSlot prev passed).toNat cur)
  | prev, [], cur => by rw [plist_nil]; simp only [plistO, lastSlot, emp_sep]
  | prev, b :: passed, cur => by
    rw [plist_cons, plist_last (b.addr + 8#64) passed cur]
    simp only [plistO, lastSlot]
    ac_rfl

/-! ## Distinct addresses, from separation -/

theorem hdrSeg_owns : ∀ {fl : List Block} {h : Word} {hf : Silmaril.X86.Sep.Frag},
    hdrSeg fl h hf → ∀ c ∈ fl, (hf (.mem c.addr.toNat)).isSome
  | [], _, _, _, c, hc => absurd hc List.not_mem_nil
  | b :: rest, h, hf, hp, c, hc => by
    obtain ⟨h₁, h₂, -, rfl, -, ⟨nxt, hb⟩⟩ := hp
    obtain ⟨g₁, g₂, -, rfl, hsz, hr⟩ := hb
    obtain ⟨g₃, g₄, -, rfl, -, hr'⟩ := hr
    obtain ⟨g₅, g₆, -, rfl, -, hseg⟩ := hr'
    have union_some : ∀ {a b : Silmaril.X86.Sep.Frag} {l}, (a l).isSome ∨ (b l).isSome →
        ((Silmaril.X86.Sep.Frag.union a b) l).isSome := by
      intro a b l hab
      simp only [Silmaril.X86.Sep.Frag.union]
      cases e : a l <;> simp_all
    apply union_some; right
    rcases List.mem_cons.1 hc with rfl | hc
    · apply union_some; left
      have := bytesAt_dom hsz 0 (by simp [Silmaril.Machine.LittleEndian.encodeWords])
      simpa using this
    · apply union_some; right; apply union_some; right; apply union_some; right
      exact hdrSeg_owns hseg c hc

theorem hdrSeg_nodup : ∀ {fl : List Block} {h : Word} {hf : Silmaril.X86.Sep.Frag},
    hdrSeg fl h hf → (fl.map Block.addr).Nodup
  | [], _, _, _ => List.nodup_nil
  | b :: rest, h, hf, hp => by
    obtain ⟨h₁, h₂, -, rfl, -, ⟨nxt, hb⟩⟩ := hp
    obtain ⟨g₁, g₂, hd, rfl, hsz, hr⟩ := hb
    obtain ⟨g₃, g₄, -, rfl, -, hr'⟩ := hr
    obtain ⟨g₅, g₆, -, rfl, -, hseg⟩ := hr'
    refine List.nodup_cons.2 ⟨fun hm => ?_, hdrSeg_nodup hseg⟩
    obtain ⟨c, hc, he⟩ := List.mem_map.1 hm
    have h1 : (g₁ (.mem b.addr.toNat)).isSome := by
      have := bytesAt_dom hsz 0 (by simp [Silmaril.Machine.LittleEndian.encodeWords])
      simpa using this
    have h2 : ((Silmaril.X86.Sep.Frag.union g₃ (Silmaril.X86.Sep.Frag.union g₅ g₆))
        (.mem b.addr.toNat)).isSome := by
      have := hdrSeg_owns hseg c hc
      rw [he] at this
      simp only [Silmaril.X86.Sep.Frag.union]
      cases e3 : g₃ (.mem b.addr.toNat) <;> cases e5 : g₅ (.mem b.addr.toNat) <;> simp_all
    rcases hd (.mem b.addr.toNat) with e | e
    · rw [e] at h1; cases h1
    · rw [e] at h2; cases h2

/-- The pure fact `Nodup` read off a free list. -/
theorem hdrSeg_nodup_entails (fl : List Block) (h : Word) :
    hdrSeg fl h ⊢ₛ (⌜(fl.map Block.addr).Nodup⌝ ∗ hdrSeg fl h) :=
  fun _ hp => (spure_sep_apply _ _ _).2 ⟨hdrSeg_nodup hp, hp⟩

/-- Read the head facts of a non-empty free list without consuming it. -/
theorem hdrSeg_head (c : Block) (rest : List Block) (h : Word) :
    hdrSeg (c :: rest) h ⊢ₛ (⌜h = c.addr ∧ c.WF⌝ ∗ hdrSeg (c :: rest) h) := by
  intro hf hp
  have hp' := hp
  rw [hdrSeg_cons, spure_sep_apply] at hp'
  exact (spure_sep_apply _ _ _).2 ⟨hp'.1, hp⟩

end Silmaril.Libc.X86Alloc

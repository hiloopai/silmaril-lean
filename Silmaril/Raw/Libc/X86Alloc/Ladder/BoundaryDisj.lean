module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryM3

/-!
# Proofs: rung 08 (boundary tags) — a block given to `free` is apart from every free block

The token and the request own all of `[b, b + s)`, the free list owns all of every free block,
and they are separate: `apart_of_sep` reads the disjointness of the intervals off the
separating conjunction, and `St_fact` lifts such a pure fact out of the canonical frame. This is
why merging the freed block with the free blocks the tables name is sound even for a token that
was never handed out: whatever it owns is not free.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint)
open Silmaril.Libc.X86Alloc.Ladder.Boundary
open Silmaril.Raw.Libc.X86Alloc.Frame

/-- A free block owns its whole interval. -/
theorem blk_blockAny (y : Nat × Nat) (hy : 32 ≤ y.2) (nx pv : Nat) :
    blk y nx pv ⊢ₛ blockAny y.1 y.2 := by
  unfold blk
  refine entails_trans (sep_mono (wordPt_blockAny _ _) (sep_mono (wordPt_blockAny _ _)
    (blk_tail y hy pv))) ?_
  rw [show y.1 + 16 = y.1 + 8 + 8 by omega, ba3, show 8 + 8 + (y.2 - 16) = y.2 by omega]
  exact entails_refl _

theorem union_isSome_left {a b : Frag} {l : Loc} (h : (a l).isSome) : ((union a b) l).isSome := by
  simp only [union]; cases e : a l <;> simp_all

theorem union_isSome_right {a b : Frag} {l : Loc} (h : (b l).isSome) :
    ((union a b) l).isSome := by
  simp only [union]; cases e : a l <;> simp_all

theorem dll_dom : ∀ (fs : List (Nat × Nat)) (p n : Nat), (∀ y ∈ fs, 32 ≤ y.2) →
    ∀ {h : Frag}, dll fs p n h → ∀ y ∈ fs, ∀ i < y.2, (h (.mem (y.1 + i))).isSome
  | [], _, _, _, _, _, y, hy, _, _ => absurd hy List.not_mem_nil
  | x :: l, p, n, hg, h, hp, y, hy, i, hi => by
    obtain ⟨h₁, h₂, -, rfl, hx, hl⟩ := hp
    rcases List.mem_cons.1 hy with rfl | hy
    · exact union_isSome_left (blockAny_dom (blk_blockAny y (hg y (by simp)) _ _ _ hx) i hi)
    · exact union_isSome_right
        (dll_dom l x.1 n (fun z hz => hg z (List.mem_cons_of_mem _ hz)) hl y hy i hi)

/-- **Owned intervals are disjoint.** -/
theorem apart_of_sep {b s : Nat} (hs : 0 < s) {fs : List (Nat × Nat)}
    (hg : ∀ y ∈ fs, 32 ≤ y.2) {p n : Nat} {h : Frag} (H : (blockAny b s ∗ dll fs p n) h) :
    ∀ y ∈ fs, Apart (b, s) y := by
  obtain ⟨h₁, h₂, hd, -, hb, hl⟩ := H
  intro y hy
  by_contra hc
  unfold Apart at hc
  simp only at hc
  have hy2 := hg y hy
  have e1 := blockAny_dom hb (max b y.1 - b) (by omega)
  have e2 := dll_dom fs p n hg hl y hy (max b y.1 - y.1) (by omega)
  rw [show b + (max b y.1 - b) = max b y.1 by omega] at e1
  rw [show y.1 + (max b y.1 - y.1) = max b y.1 by omega] at e2
  rcases hd (.mem (max b y.1)) with e | e
  · rw [e] at e1; cases e1
  · rw [e] at e2; cases e2

/-- A pure fact of the memory part, kept. -/
theorem St_fact {pc : Word} {f : Reg → Word} {fl : Flags} {A R : SProp} {φ : Prop}
    (h : ∀ hf, A hf → φ) : St pc f fl (A ∗ R) ⊢ₛ (⌜φ⌝ ∗ St pc f fl (A ∗ R)) := by
  intro hf hp
  refine (spure_sep_apply _ _ _).2 ⟨?_, hp⟩
  obtain ⟨_, h₁, -, -, -, hr⟩ := hp
  obtain ⟨_, h₂, -, -, -, hr⟩ := hr
  obtain ⟨_, h₃, -, -, -, hr⟩ := hr
  obtain ⟨h₄, _, -, -, hA, -⟩ := hr
  exact h h₄ hA

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

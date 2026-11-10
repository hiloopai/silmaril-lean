module

public import Silmaril.X86.Sep.Spec.Defs
public import Silmaril.X86.Extends.Thms
public import Silmaril.Proofs.X86.Sep.Algebra

/-!
# Proofs: triples from runs, runs from triples, and triples along extensions

* `triple_of_local`: a triple from a run that changes nothing outside the precondition's
  fragment and whose final state, re-valued on that fragment, satisfies the postcondition.
* `triple_run`: the converse. Instantiating the built-in frame with "the rest of the state,
  exactly" gives a run on which every location outside the precondition's fragment is
  unchanged.
* `triple_of_local_mstate`: the same on a machine over `MState` (`Open.isa`, `Open9.isa`),
  stated with `toFrag`.
* `frag_view`, `triple_lift`: a machine extension's states have the fragments of their
  views, so a triple of `I` is a triple of every `J` extending `I`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep

open Silmaril.X86 (MState)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval diff)

variable {σ τ : Type} {I : Isa σ}

theorem frag_isSome (s : σ) (l : Loc) : (frag I s l).isSome := toFrag_isSome _ l

theorem triple_of_local {P Q : SProp}
    (h : ∀ s h₁, I.live s → P h₁ → Le h₁ (frag I s) →
      ∃ t, Reaches I.step s t ∧
        (∀ l, h₁ l = none → frag I t l = frag I s l) ∧ Q (reval h₁ (frag I t))) :
    Triple I P Q := by
  intro F m hlive ⟨h₁, h₂, hd, he, hp, hf⟩
  have hl : Le h₁ (frag I m) := by rw [he]; exact Frag.le_union_left h₁ h₂
  obtain ⟨m', hr, hsame, hq⟩ := h m h₁ hlive hp hl
  refine ⟨m', hr, reval h₁ (frag I m'), h₂, ?_, ?_, hq, hf⟩
  · intro l
    rcases hd l with e | e
    · left; simp [reval, e]
    · right; exact e
  · funext l
    cases e : h₁ l with
    | none =>
      rw [hsame l e, he, Frag.union_of_none e, Frag.union_of_none]
      simp [reval, e]
    | some v =>
      rw [Frag.union_of_some (v := (frag I m' l).get (frag_isSome m' l))]
      · simp
      · simp [reval, e]

theorem frag_eq_toFrag {I : Isa MState} (hc : ∀ m, I.core m = m.core)
    (hm : ∀ m, I.mem m = m.memory) (m : MState) : frag I m = toFrag m := by
  unfold frag; rw [hc, hm]

/-- `triple_of_local` on a machine over `MState` whose core and memory are the state's. -/
theorem triple_of_local_mstate {I : Isa MState} {P Q : SProp} (hc : ∀ m, I.core m = m.core)
    (hm : ∀ m, I.mem m = m.memory)
    (h : ∀ m h₁, P h₁ → Le h₁ (toFrag m) →
      ∃ m', Reaches I.step m m' ∧
        (∀ l, h₁ l = none → toFrag m' l = toFrag m l) ∧ Q (reval h₁ (toFrag m'))) :
    Triple I P Q := by
  apply triple_of_local
  intro m h₁ _ hp hl
  simp only [frag_eq_toFrag hc hm] at hl ⊢
  exact h m h₁ hp hl

theorem triple_run {P Q : SProp} (h : Triple I P Q) {h₁ : Frag} {m : σ} (hlive : I.live m)
    (hp : P h₁) (hl : Le h₁ (frag I m)) :
    ∃ m' h₁', Reaches I.step m m' ∧ Q h₁' ∧ Le h₁' (frag I m') ∧
      ∀ l, h₁ l = none → frag I m' l = frag I m l := by
  obtain ⟨m', hr, a, b, hd, he, hq, hb⟩ :=
    h (fun f => f = diff (frag I m) h₁) m hlive
      ⟨h₁, diff (frag I m) h₁, Frag.diff_disjoint _ _, (Frag.union_diff hl).symm, hp, rfl⟩
  subst hb
  refine ⟨m', a, hr, hq, by rw [he]; exact Frag.le_union_left _ _, fun l e => ?_⟩
  have hdiff : diff (frag I m) h₁ l = frag I m l := by simp [diff, e]
  have hsome : (diff (frag I m) h₁ l).isSome := by rw [hdiff]; exact frag_isSome m l
  have ha : a l = none := by
    rcases hd l with e' | e'
    · exact e'
    · rw [e'] at hsome; cases hsome
  rw [he, Frag.union_of_none ha, hdiff]

theorem frag_view {J : Isa τ} (E : I.Extends J) (x : τ) : frag J x = frag I (E.view x) := by
  unfold frag; rw [E.core, E.mem]

theorem triple_lift {J : Isa τ} (E : I.Extends J) {P Q : SProp} (h : Triple I P Q) :
    Triple J P Q := by
  intro F x hlive hm
  rw [frag_view E] at hm
  obtain ⟨t, hr, hq⟩ := h F (E.view x) (E.live x hlive) hm
  refine ⟨E.put x t, E.reaches hr, ?_⟩
  rw [frag_view E, E.view_put]
  exact hq

end Silmaril.Proofs.X86.Sep

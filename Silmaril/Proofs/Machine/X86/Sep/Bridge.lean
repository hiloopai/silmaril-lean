module

public import Silmaril.Machine.X86.Sep.Spec.Defs
public import Silmaril.Proofs.Machine.X86.Sep.Algebra

/-!
# Proofs: triples from runs, and runs from triples

* `of_local`: a triple from a run that changes nothing outside the precondition's fragment
  and whose final state, re-valued on that fragment, satisfies the postcondition. This is the
  bridge used for every existing proof (instruction steps, `Ext.Returns` certificates).
* `run`: the converse. Instantiating the built-in frame with "the rest of the state, exactly"
  gives a run on which every location outside the precondition's fragment is unchanged.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Sep

open Silmaril.X86 (MState)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Sep.Frag (union Disjoint Le reval diff)

theorem triple_of_local {P Q : SProp}
    (h : ∀ m h₁, P h₁ → Le h₁ (toFrag m) →
      ∃ m', Reaches Silmaril.Machine.X86.Open.step m m' ∧
        (∀ l, h₁ l = none → toFrag m' l = toFrag m l) ∧ Q (reval h₁ (toFrag m'))) :
    Triple P Q := by
  intro F m ⟨h₁, h₂, hd, he, hp, hf⟩
  have hl : Le h₁ (toFrag m) := by rw [he]; exact Frag.le_union_left h₁ h₂
  obtain ⟨m', hr, hsame, hq⟩ := h m h₁ hp hl
  refine ⟨m', hr, reval h₁ (toFrag m'), h₂, ?_, ?_, hq, hf⟩
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
      rw [Frag.union_of_some (v := (toFrag m' l).get (toFrag_isSome m' l))]
      · simp
      · simp [reval, e]

theorem triple_run {P Q : SProp} (h : Triple P Q) {h₁ : Frag} {m : MState} (hp : P h₁)
    (hl : Le h₁ (toFrag m)) :
    ∃ m' h₁', Reaches Silmaril.Machine.X86.Open.step m m' ∧ Q h₁' ∧ Le h₁' (toFrag m') ∧
      ∀ l, h₁ l = none → toFrag m' l = toFrag m l := by
  obtain ⟨m', hr, a, b, hd, he, hq, hb⟩ :=
    h (fun f => f = diff (toFrag m) h₁) m
      ⟨h₁, diff (toFrag m) h₁, Frag.diff_disjoint _ _, (Frag.union_diff hl).symm, hp, rfl⟩
  subst hb
  refine ⟨m', a, hr, hq, by rw [he]; exact Frag.le_union_left _ _, fun l e => ?_⟩
  have hdiff : diff (toFrag m) h₁ l = toFrag m l := by simp [diff, e]
  have hsome : (diff (toFrag m) h₁ l).isSome := by rw [hdiff]; exact toFrag_isSome m l
  have ha : a l = none := by
    rcases hd l with e' | e'
    · exact e'
    · rw [e'] at hsome; cases hsome
  rw [he, Frag.union_of_none ha, hdiff]

end Silmaril.Proofs.Machine.X86.Sep

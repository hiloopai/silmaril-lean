module

public import Silmaril.X86.Sep.Spec.Thms
public import Silmaril.X86.Sep.Extra.Thms

/-!
# Proofs: a loop rule for the angelic `Triple`

`Triple.loop`: a loop whose body, from the invariant `P x`, either reaches `Q` or reaches the
invariant at a point `y` of strictly smaller measure, reaches `Q` from every `P x`. The proof is
strong induction on the measure, using `live_reaches` (reaching keeps the machine live) and
`Reaches.trans`. `Q` carries the exit value; the continue branch is `sexists` over the loop
index. This is the reusable piece for the free-list walk of first-fit and coalescing (and glibc).

**Angelic, so read it on a deterministic machine.** `Triple` promises that *some* run reaches the
postcondition (`∃ t, Reaches I.step s t ∧ …`), and the rule is sound for that reading on every
`Isa`. It says *every* run gets there only when the machine is deterministic: `I.step` is a
function `σ → Option σ`, so on `Open.isa`, `Open9.isa` and `Str9.isa` there is exactly one run
from each state (`Silmaril.X86.Ext.Returns.eq_of_run` in `Silmaril/X86/Ext/SymExec.lean` makes
this explicit for returning runs), and "some run" is "the run". Do **not** reuse this rule as a
demonic (all-runs) statement on a relational or nondeterministic machine (the loose-top classes of
`Silmaril.Problems.Shapes.CorrectLoose`, concurrency models): there it only gives one good run.
-/

@[expose] public section

namespace Silmaril.Raw.Libc.X86Alloc.Loop

open Silmaril.X86 (MState)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.Machine.Execution (Reaches)

variable {σ : Type} {I : Isa σ}

/-- **The loop rule.** `P x` is the loop invariant at index `x`, `μ` its measure. If every `P x`
reaches either `Q` or some `P y` with `μ y < μ x`, then every `P x` reaches `Q`. -/
theorem Triple.loop {α : Type} (μ : α → Nat) (P : α → SProp) (Q : SProp)
    (body : ∀ x, Triple I (P x) (sor Q (sexists fun y => ⌜μ y < μ x⌝ ∗ P y))) :
    ∀ x, Triple I (P x) Q := by
  have key : ∀ n x, μ x ≤ n → Triple I (P x) Q := by
    intro n
    induction n with
    | zero =>
      intro x hx F s hlive hP
      obtain ⟨t, hr, ht⟩ := body x F s hlive hP
      rw [sor_sep] at ht
      rcases ht with hQ | ⟨hf, hf', hd, heq, ⟨y, hcy⟩, hF⟩
      · exact ⟨t, hr, hQ⟩
      · rw [spure_sep_apply] at hcy; omega
    | succ n ih =>
      intro x hx F s hlive hP
      obtain ⟨t, hr, ht⟩ := body x F s hlive hP
      rw [sor_sep] at ht
      rcases ht with hQ | hcont
      · exact ⟨t, hr, hQ⟩
      · obtain ⟨hf, hf', hd, heq, ⟨y, hcy⟩, hF⟩ := hcont
        rw [spure_sep_apply] at hcy
        obtain ⟨hμ, hPy⟩ := hcy
        have hlt : I.live t := Silmaril.X86.SegVC.live_reaches (I := I) hlive hr
        obtain ⟨u, hru, hu⟩ := ih y (by omega) F t hlt ⟨hf, hf', hd, heq, hPy, hF⟩
        exact ⟨u, hr.trans hru, hu⟩
  exact fun x => key (μ x) x (Nat.le_refl _)

/-- The `SPEC` form: the code `C` is owned throughout. -/
theorem SPEC.loop {α : Type} (μ : α → Nat) (C : SProp) (P : α → SProp) (Q : SProp)
    (body : ∀ x, SPEC I C (P x) (sor Q (sexists fun y => ⌜μ y < μ x⌝ ∗ P y))) :
    ∀ x, SPEC I C (P x) Q := by
  refine fun x => Triple.loop μ (fun x => C ∗ P x) (C ∗ Q) (fun x => ?_) x
  refine Triple.post (body x) ?_
  rw [sep_sor]
  refine sor_mono (entails_refl _) (entails_of_eq ?_)
  rw [sep_sexists]
  congr 1; funext y
  rw [← sep_assoc, sep_comm C, sep_assoc]

end Silmaril.Raw.Libc.X86Alloc.Loop

module

public import Silmaril.Foundations.InfiniteTrace

/-! # Stuttering at stop states

`Stutter R Stop` adds a self-loop at every state satisfying `Stop` to the
relation `R`. Both Lir backends use this shape for a machine that stopped at a
stack-limit check (`X86.Backend.Env.TStep`, `RiscV.Backend.XStep`): the stopped
machine is treated as looping, so a forward simulation can keep stepping.

Self-loops do not move, so every finite `Stutter` path projects to an `R` path
(`Stutter.reflTransGen_proj`). An infinite `Stutter` path is an infinite `R`
path or reaches a stop state along `R` (`Stutter.infinite`). No relation
between `Stop` and `R` is assumed; in particular a stop state may still have
`R`-successors.
-/

@[expose] public section

namespace Silmaril

open Relation

variable {α : Type*}

/-- A step of `R`, or the self-loop at a state satisfying `Stop`. -/
def Stutter (R : α → α → Prop) (Stop : α → Prop) (a b : α) : Prop :=
  R a b ∨ (Stop a ∧ b = a)

namespace Stutter

variable {R : α → α → Prop} {Stop : α → Prop} {a b : α}

theorem of_step (h : R a b) : Stutter R Stop a b := .inl h

theorem loop (h : Stop a) : Stutter R Stop a a := .inr ⟨h, rfl⟩

theorem transGen_of (h : TransGen R a b) : TransGen (Stutter R Stop) a b :=
  h.lift id fun _ _ => of_step

theorem reflTransGen_of (h : ReflTransGen R a b) : ReflTransGen (Stutter R Stop) a b :=
  h.lift id fun _ _ => of_step

/-- A finite stuttering path is a path of `R`: self-loops do not move. -/
theorem reflTransGen_proj (h : ReflTransGen (Stutter R Stop) a b) : ReflTransGen R a b := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with hs | ⟨-, rfl⟩
    · exact ih.tail hs
    · exact ih

/-- An infinite stuttering path is an infinite path of `R`, or reaches a stop
state along `R`. -/
theorem infinite (h : InfiniteTrace (Stutter R Stop) a) :
    InfiniteTrace R a ∨ ∃ b, ReflTransGen R a b ∧ Stop b := by
  classical
  by_cases hstop : ∃ b, ReflTransGen R a b ∧ Stop b
  · exact .inr hstop
  · left
    refine InfiniteTrace.coinduct (fun x => ReflTransGen R a x ∧ InfiniteTrace (Stutter R Stop) x)
      ?_ ⟨.refl, h⟩
    intro x ⟨hx, hi⟩
    obtain ⟨y, hy, hi'⟩ := hi.unfold
    rcases hy with hy | ⟨hxs, -⟩
    · exact ⟨y, hy, hx.tail hy, hi'⟩
    · exact absurd ⟨x, hx, hxs⟩ hstop

end Stutter

end Silmaril

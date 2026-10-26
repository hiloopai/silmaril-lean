module

public import Silmaril.Process.LPS.State

/-!
# LPS in Lean: the syscall specification monad

Translation of LPS `Monad.v` (upstream commit `f1006fe8`). A specification
`Sys α := SyscallInput → Model → Outcome α → Prop` relates an input and a model to the
outcomes the kernel may give. It combines a reader (the input), state (the model), a writer
(events), powerset nondeterminism (`choose`, `alt`) and a fail-closed exception
`unmodeled`.

`unmodeled` is a positive outcome, not an empty relation: it drives the explicit error
transition of the run semantics (fail closed) rather than leaving the semantics stuck
(`Monad.v:5-16`). As in LPS, the exception sits under the state and writer, so `unmodeled`
drops the model and the events. The monad laws hold up to `SysEquiv` (`bind_pure_l`,
`bind_pure_r`, `bind_assoc`).
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- LPS `Monad.v:129` `outcome`. -/
inductive Outcome (α : Type) where
  | ok (x : α) (m : Model) (evs : List Event)
  | unmodeled

/-- LPS `Monad.v:135` `Sys`. -/
def Sys (α : Type) : Type := SyscallInput → Model → Outcome α → Prop

namespace Sys

/-- LPS `Monad.v:137` `pure`. -/
def pure {α : Type} (x : α) : Sys α := fun _ m o => o = .ok x m []

/-- LPS `Monad.v:141` `bind`. -/
def bind {α β : Type} (c : Sys α) (k : α → Sys β) : Sys β := fun i m o =>
  match o with
  | .unmodeled => c i m .unmodeled ∨ ∃ x m₁ evs₁, c i m (.ok x m₁ evs₁) ∧ k x i m₁ .unmodeled
  | .ok y m₂ evs =>
    ∃ x m₁ evs₁ evs₂, c i m (.ok x m₁ evs₁) ∧ k x i m₁ (.ok y m₂ evs₂) ∧ evs = evs₁ ++ evs₂

instance : Monad Sys where
  pure := pure
  bind := bind

/-- LPS `Monad.v:172` `sys_equiv`. -/
def Equiv {α : Type} (c₁ c₂ : Sys α) : Prop := ∀ i m o, c₁ i m o ↔ c₂ i m o

/-- LPS `Monad.v:268` `unmodeled`: the model declines (fail closed). -/
def unmodeled {α : Type} : Sys α := fun _ _ o => o = .unmodeled

/-- LPS `Monad.v:271` `choose`: the environment picks any value satisfying `P`. -/
def choose {α : Type} (P : α → Prop) : Sys α := fun _ m o => ∃ x, P x ∧ o = .ok x m []

/-- LPS `Monad.v:275` `alt`: either behaviour. -/
def alt {α : Type} (c₁ c₂ : Sys α) : Sys α := fun i m o => c₁ i m o ∨ c₂ i m o

/-- LPS `Monad.v:279` `emit`. -/
def emit (evs : List Event) : Sys Unit := fun _ m o => o = .ok () m evs

/-- LPS `Monad.v:285` `input`. -/
def input : Sys SyscallInput := fun i m o => o = .ok i m []

/-- LPS `Monad.v:289` `get_model`. -/
def getModel : Sys Model := fun _ m o => o = .ok m m []

/-- LPS `Monad.v:290` `modify`. -/
def modify (f : Model → Model) : Sys Unit := fun _ m o => o = .ok () (f m) []

/-- LPS `Monad.v:314` `get_vmmaps`. -/
def getVmmaps : Sys VmMaps := fun _ m o => o = .ok m.vmmaps m []

theorem bind_pure_l {α β : Type} (a : α) (k : α → Sys β) : Equiv (bind (pure a) k) (k a) := by
  intro i m o
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      cases h₁
      simpa using h₂
    · intro h
      exact ⟨a, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h | ⟨x, m₁, evs₁, h₁, h₂⟩)
      · cases h
      · cases h₁
        exact h₂
    · intro h
      exact .inr ⟨a, m, [], rfl, h⟩

theorem bind_pure_r {α : Type} (c : Sys α) : Equiv (bind c pure) c := by
  intro i m o
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      cases h₂
      simpa using h₁
    · intro h
      exact ⟨y, m₂, evs, [], h, rfl, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h | ⟨x, m₁, evs₁, h₁, h₂⟩)
      · exact h
      · cases h₂
    · exact .inl

theorem bind_assoc {α β γ : Type} (c : Sys α) (k : α → Sys β) (h : β → Sys γ) :
    Equiv (bind (bind c k) h) (bind c fun x => bind (k x) h) := by
  intro i m o
  cases o with
  | ok z m₃ evs =>
    constructor
    · rintro ⟨y, m₂, evsA, evsB, ⟨x, m₁, evs₁, evs₂, hc, hk, rfl⟩, hh, rfl⟩
      exact ⟨x, m₁, evs₁, evs₂ ++ evsB, hc, ⟨y, m₂, evs₂, evsB, hk, hh, rfl⟩, by simp⟩
    · rintro ⟨x, m₁, evs₁, evsBC, hc, ⟨y, m₂, evs₂, evsB, hk, hh, rfl⟩, rfl⟩
      exact ⟨y, m₂, evs₁ ++ evs₂, evsB, ⟨x, m₁, evs₁, evs₂, hc, hk, rfl⟩, hh, by simp⟩
  | unmodeled =>
    constructor
    · rintro ((hc | ⟨x, m₁, evs₁, hc, hk⟩) | ⟨y, m₂, evsA, ⟨x, m₁, evs₁, evs₂, hc, hk, -⟩, hh⟩)
      · exact .inl hc
      · exact .inr ⟨x, m₁, evs₁, hc, .inl hk⟩
      · exact .inr ⟨x, m₁, evs₁, hc, .inr ⟨y, m₂, evs₂, hk, hh⟩⟩
    · rintro (hc | ⟨x, m₁, evs₁, hc, hk | ⟨y, m₂, evs₂, hk, hh⟩⟩)
      · exact .inl (.inl hc)
      · exact .inl (.inr ⟨x, m₁, evs₁, hc, hk⟩)
      · exact .inr ⟨y, m₂, evs₁ ++ evs₂, ⟨x, m₁, evs₁, evs₂, hc, hk, rfl⟩, hh⟩

end Sys

end Silmaril.Process.LPS

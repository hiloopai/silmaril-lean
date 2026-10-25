module

public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.SingleThreaded.Determinism.Basic
public import Silmaril.Wasm.SingleThreaded.Determinism.Join

@[expose] public section

/-! # Determinism of the single-threaded machine (U27)

With the grow oracle fixed, the deterministic profile makes every internal step
a function of the configuration *up to bubbling*: canonical NaNs, `$ND = false`,
and grow success/failure decided by the oracle. Casts are decided by `RefOk`,
which is a proposition, so determinism does not need decidability.

Core reduction is not literally a function: SpecTec's `Step_pure/trap-instrs`
(`val* TRAP instr* ~> TRAP`) and `Step_read/throw_ref-instrs` overlap with
`Step/ctxt-instrs` applied to a shorter bubble (`v₁ v₂ TRAP` steps both to
`TRAP` and to `v₁ TRAP`). The milestones therefore state the diamond property:
two successors are joinable in at most one step each (`Det.Join`).
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The thread of a configuration reached by an internal step. -/
def toThread (c : Config H) : Store H × Thread := (c.store, .active c.frame c.code)

theorem internal_of_dstep {o : GrowOracle} {a b : Config H} (h : Det.DStep o a b) :
    Internal o (toThread a) (toThread b) :=
  ⟨b.frame, b.code, rfl, by rcases a with ⟨s, f, is⟩; rcases b with ⟨s', f', is'⟩; exact h⟩

theorem Det.Join.map' {α β : Type _} {R : α → α → Prop} {S : β → β → Prop} (F : α → β)
    (hF : ∀ a b, R a b → S (F a) (F b)) {x y : α} (h : Det.Join R x y) :
    Det.Join S (F x) (F y) := by
  obtain ⟨z, h₁, h₂⟩ := h
  refine ⟨F z, ?_, ?_⟩
  · cases h₁ with
    | refl => exact .refl
    | single h => exact .single (hF _ _ h)
  · cases h₂ with
    | refl => exact .refl
    | single h => exact .single (hF _ _ h)

/-- **Milestone.** Internal steps are deterministic up to bubbling: two
successors are joinable in at most one internal step each. -/
theorem Internal.deterministic {o : GrowOracle} {x y z : Store H × Thread}
    (hy : Internal o x y) (hz : Internal o x z) : Det.Join (Internal o) y z := by
  rcases x with ⟨s, t⟩
  rcases y with ⟨s₁, t₁⟩
  rcases z with ⟨s₂, t₂⟩
  obtain ⟨f₁, c₁, rfl, h₁⟩ := hy
  obtain ⟨f₂, c₂, rfl, h₂⟩ := hz
  have hj := Det.DStep.join' (o := o) h₁ h₂
  exact Det.Join.map' toThread (fun a b h => internal_of_dstep h) hj

/-- Core reduction in the single-threaded profile is deterministic (up to
bubbling) on configurations that are not at a callout. -/
theorem Step.deterministic_profile {o : GrowOracle} {host : HostSemantics H} {c c₁ c₂ : Config H}
    (hno : decompose? c.store c.code = none)
    (h₁ : Step (profile o) host c c₁) (h₂ : Step (profile o) host c c₂) :
    Det.Join (Step (profile o) host) c₁ c₂ := by
  have nh : ∀ {c' : Config H}, Step (profile o) host c c' → Det.DStep o c c' := by
    intro c' h
    rcases Step.split_host h with h | ⟨E, a, hh, args, hd, -⟩
    · exact h
    · rw [hno] at hd; cases hd
  have hj := Det.DStep.join' (nh h₁) (nh h₂)
  exact Det.Join.map' id (fun a b h => Step.of_noHost host h) hj

/-- `status` and `resume` are functions (trivially), and a status is stable along
host-free determinism: a running thread has a successor, unique up to bubbling. -/
theorem running_unique {o : GrowOracle} {s : Store H} {t : Thread}
    (hs : status o s t = .running) :
    ∃ y, Internal o (s, t) y ∧ ∀ z, Internal o (s, t) z → Det.Join (Internal o) y z := by
  have hex : ∃ y, Internal o (s, t) y := by
    by_contra hne
    unfold status at hs
    simp only at hs
    split_ifs at hs
    try cases hs
    all_goals (split at hs <;> cases hs)
  obtain ⟨y, hy⟩ := hex
  exact ⟨y, hy, fun z hz => Internal.deterministic hy hz⟩

end Silmaril.Wasm.SingleThreaded

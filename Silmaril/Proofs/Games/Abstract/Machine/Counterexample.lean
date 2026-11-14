module

public import Silmaril.Games.Abstract.Machine.Defs
import Silmaril.Proofs.Games.Abstract.Machine.Basic

/-!
# Trace equality does not determine a nondeterministic machine

The classic pair `a.b + a.c` and `a.(b + c)`, as machines of the free game on
three Proponent moves: both have the traces `[]`, `[a]`, `[a, b]` and `[a, c]`,
but they are not bisimilar. The second machine is a deterministic labelled
transition system; the first is not. So state erasure is injective on the
bisimulation quotient of deterministic machines
(`Silmaril.Games.Abstract.Machine.lDet_bisim_iff_traces`) and not beyond.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Machine.Counterexample

open Silmaril.Games.Abstract Silmaril.Games.Abstract.Machine

/-- Three moves. -/
inductive Mv | a | b | c

/-- The free game on `Mv`, every move the component's. -/
def G : Game.{0} := Game.free Mv fun _ => False

/-- Five states. -/
inductive St | s0 | s1 | s2 | s3 | s4

/-- `a.b + a.c`: the choice is made on the first move. -/
inductive Early : St → Option G.Move → St → Prop
  | ab : Early .s0 (some Mv.a) .s1
  | ac : Early .s0 (some Mv.a) .s2
  | b : Early .s1 (some Mv.b) .s3
  | c : Early .s2 (some Mv.c) .s4

/-- `a.(b + c)`: the choice is made after the first move. -/
inductive Late : St → Option G.Move → St → Prop
  | a : Late .s0 (some Mv.a) .s1
  | b : Late .s1 (some Mv.b) .s2
  | c : Late .s1 (some Mv.c) .s3

/-- The early-choice machine. -/
def early : Machine G := ⟨St, .s0, Early⟩

/-- The late-choice machine. -/
def late : Machine G := ⟨St, .s0, Late⟩

theorem late_lDet : late.LDet where
  tau_free h := by cases h
  det h h' := by cases h <;> cases h' <;> rfl

/-- The traces of both machines. -/
def tr : Set (List G.Move) := {s | s = [] ∨ s = [Mv.a] ∨ s = [Mv.a, Mv.b] ∨ s = [Mv.a, Mv.c]}

theorem early_traces : early.traces = tr := by
  ext s
  constructor
  · rintro ⟨z, h⟩
    rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
    · exact .inl rfl
    · cases h
    · cases h
      · rcases h₁ with _ | ⟨h, _⟩ | ⟨h, h₂⟩
        · exact .inr (.inl rfl)
        · cases h
        · cases h
          rcases h₂ with _ | ⟨h, _⟩ | ⟨h, _⟩
          · exact .inr (.inr (.inl rfl))
          · cases h
          · cases h
      · rcases h₁ with _ | ⟨h, _⟩ | ⟨h, h₂⟩
        · exact .inr (.inl rfl)
        · cases h
        · cases h
          rcases h₂ with _ | ⟨h, _⟩ | ⟨h, _⟩
          · exact .inr (.inr (.inr rfl))
          · cases h
          · cases h
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, .nil _⟩
    · exact ⟨_, .vis Early.ab (.nil _)⟩
    · exact ⟨_, .vis Early.ab (.vis Early.b (.nil _))⟩
    · exact ⟨_, .vis Early.ac (.vis Early.c (.nil _))⟩

theorem late_traces : late.traces = tr := by
  ext s
  constructor
  · rintro ⟨z, h⟩
    rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
    · exact .inl rfl
    · cases h
    · cases h
      rcases h₁ with _ | ⟨h, _⟩ | ⟨h, h₂⟩
      · exact .inr (.inl rfl)
      · cases h
      · cases h
        · rcases h₂ with _ | ⟨h, _⟩ | ⟨h, _⟩
          · exact .inr (.inr (.inl rfl))
          · cases h
          · cases h
        · rcases h₂ with _ | ⟨h, _⟩ | ⟨h, _⟩
          · exact .inr (.inr (.inr rfl))
          · cases h
          · cases h
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, .nil _⟩
    · exact ⟨_, .vis Late.a (.nil _)⟩
    · exact ⟨_, .vis Late.a (.vis Late.b (.nil _))⟩
    · exact ⟨_, .vis Late.a (.vis Late.c (.nil _))⟩

theorem not_bisim : ¬ early.Bisim late := by
  rintro ⟨R, hR, h0⟩
  obtain ⟨y, hy, h1⟩ := hR.forth h0 (Early.ab : early.step .s0 (some Mv.a) .s1)
  cases hy
  obtain ⟨x, hx, -⟩ := hR.back h1 (Late.c : late.step .s1 (some Mv.c) .s3)
  cases hx

/-- Two machines with equal traces, one of them deterministic, that are not
bisimilar. -/
theorem exists_traces_eq_not_bisim :
    ∃ (G : Game.{0}) (M N : Machine G), M.traces = N.traces ∧ N.LDet ∧ ¬ M.Bisim N :=
  ⟨G, early, late, early_traces.trans late_traces.symm, late_lDet, not_bisim⟩

end Silmaril.Proofs.Games.Abstract.Machine.Counterexample

module

public import Silmaril.Wasm.Abstract.InstanceOutcome.Defs
public import Silmaril.Games.Abstract.Machine.Thms

/-!
# Scalar Wasm instances with visible divergence: proofs

Silent host-free steps do not change the traces of the instance machine, and
its `div` observations are exactly the host-free divergences of export calls.
-/

public section

namespace Silmaril.Proofs.Wasm.Abstract.InstanceOutcome

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Game Silmaril.Wasm.Abstract
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (Thread)

variable {I : ScalarInstance} {P : Profile} {s₀ : Store Nat}

theorem run_of_lts {x y : (machine I P s₀).State} {tr : List (Move I.E I.F)}
    (h : (machine I P s₀).Run x tr y) : (omachine I P s₀).Run x tr y := by
  induction h with
  | nil => exact .nil _
  | tau h _ _ => obtain ⟨m, hm, -⟩ := h; cases hm
  | vis h _ ih =>
    obtain ⟨m, hm, ht⟩ := h
    cases hm
    exact .vis (OStep.vis ht) ih

theorem lift {f : I.F.Op} {st st' : Store Nat} {t t' : Thread} {tr : List (Move I.E I.F)}
    {z : (machine I P s₀).State} (hi : InternalP P (st, t) (st', t'))
    (h : (machine I P s₀).Run (show (machine I P s₀).State from .running f st' t') tr z) :
    ∃ z', (machine I P s₀).Run (show (machine I P s₀).State from .running f st t) tr z' := by
  cases h with
  | nil => exact ⟨_, .nil _⟩
  | tau h _ => obtain ⟨m, hm, -⟩ := h; cases hm
  | vis h r =>
    obtain ⟨m, hm, ht⟩ := h
    cases hm
    cases ht with
    | ucall run callout op =>
      exact ⟨_, .vis ⟨_, rfl, ScalarInstance.Trans.ucall (Relation.ReflTransGen.head hi run)
        callout op⟩ r⟩
    | oret run final answer =>
      exact ⟨_, .vis ⟨_, rfl, ScalarInstance.Trans.oret (Relation.ReflTransGen.head hi run)
        final answer⟩ r⟩

theorem run_to_lts {x y : (omachine I P s₀).State} {tr : List (Move I.E I.F)}
    (h : (omachine I P s₀).Run x tr y) : ∃ y', (machine I P s₀).Run x tr y' := by
  induction h with
  | nil => exact ⟨_, .nil _⟩
  | tau h _ ih =>
    cases h with
    | tau hi =>
      obtain ⟨z, hz⟩ := ih
      exact lift hi hz
  | vis h _ ih =>
    cases h with
    | vis ht =>
      obtain ⟨z, hz⟩ := ih
      exact ⟨z, .vis ⟨_, rfl, ht⟩ hz⟩

theorem traces_omachine : (omachine I P s₀).traces = (machine I P s₀).traces := by
  ext tr
  constructor
  · rintro ⟨y, h⟩
    exact run_to_lts h
  · rintro ⟨y, h⟩
    exact ⟨y, run_of_lts h⟩

/-- The configuration of a running state. -/
def cfg : (omachine I P s₀).State → Option (Store Nat × Thread)
  | .running _ st t => some (st, t)
  | _ => none

theorem tau_inv {x y : (omachine I P s₀).State} (h : (omachine I P s₀).step x none y) :
    ∃ f st t st' t', x = .running f st t ∧ y = .running f st' t' ∧
      InternalP P (st, t) (st', t') := by
  cases h with
  | tau hi => exact ⟨_, _, _, _, _, rfl, rfl, hi⟩

theorem divergesFrom_iff {x : (omachine I P s₀).State} :
    (omachine I P s₀).DivergesFrom x ↔ ∃ f st t, x = .running f st t ∧
      ∃ g : Nat → Store Nat × Thread, g 0 = (st, t) ∧ ∀ n, InternalP P (g n) (g (n + 1)) := by
  constructor
  · rintro ⟨F, h0, hF⟩
    obtain ⟨f, st, t, -, -, hx, -, -⟩ := tau_inv (h0 ▸ hF 0)
    refine ⟨f, st, t, hx, fun n => (cfg (F n)).getD (st, t), ?_, fun n => ?_⟩
    · show (cfg (F 0)).getD (st, t) = (st, t)
      rw [h0, hx]; rfl
    · obtain ⟨f₁, a, b, a', b', e₁, e₂, hi⟩ := tau_inv (hF n)
      show InternalP P ((cfg (F n)).getD (st, t)) ((cfg (F (n + 1))).getD (st, t))
      rw [e₁, e₂]
      exact hi
  · rintro ⟨f, st, t, rfl, g, h0, hg⟩
    refine ⟨fun n => .running f (g n).1 (g n).2, by simp only [h0]; rfl, fun n => ?_⟩
    exact OStep.tau (hg n)

end Silmaril.Proofs.Wasm.Abstract.InstanceOutcome

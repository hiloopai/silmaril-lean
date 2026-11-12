module

public import Silmaril.Wasm.SpecTec.Sim.Bwd.Defs

/-!
# Call-annotation equivalence, basic facts

`CodeEq` is reflexive and a congruence for `++`, labels, handlers and frames; `ConfigEq` is
reflexive. `Task.wholeStep` implies `Task.wholeStepUpTo` (`wholeStep_upTo`), and `Backward`
implies `BackwardUpTo` (`Backward.upTo`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- `CodeEq` is reflexive. -/
theorem CodeEq.refl : ∀ l : List Admin, CodeEq l l
  | [] => .nil
  | a :: l => .cons (.refl a) (CodeEq.refl l)

/-- `CodeEq` is a congruence for `++`. -/
theorem CodeEq.append {a b c d : List Admin} (h₁ : CodeEq a b) (h₂ : CodeEq c d) :
    CodeEq (a ++ c) (b ++ d) := by
  induction a generalizing b with
  | nil =>
    cases h₁
    exact h₂
  | cons x a ih =>
    cases h₁ with
    | cons hx ha => exact .cons hx (ih ha)

/-- `CodeEq` relates sequences of the same length. -/
theorem CodeEq.length_eq {a b : List Admin} (h : CodeEq a b) : a.length = b.length := by
  induction a generalizing b with
  | nil =>
    cases h
    rfl
  | cons x a ih =>
    cases h with
    | cons _ ha => exact congrArg Nat.succ (ih ha)

/-- `ConfigEq` is reflexive. -/
theorem ConfigEq.refl (c : Config H) : ConfigEq c c := ⟨rfl, rfl, CodeEq.refl _⟩

/-- `Backward` implies `BackwardUpTo`, by reflexivity. -/
theorem _root_.Silmaril.Wasm.SpecTec.Sim.Backward.upTo {env : Env} {hn : H → String}
    {P : Numerics.Profile} {host : HostSemantics H} (Bk : Backward env hn P host) :
    BackwardUpTo env hn P host where
  pure i s f is w hc hf := by
    obtain ⟨is', hw, hs⟩ := Bk.pure i s f is w hc hf
    exact ⟨is', is', CodeEq.refl _, hw, hs⟩
  read i c w hc hf := by
    obtain ⟨is', hw, hs⟩ := Bk.read i c w hc hf
    exact ⟨is', is', CodeEq.refl _, hw, hs⟩
  step i hi c w hc hf := by
    obtain ⟨c', hw, hs⟩ := Bk.step i hi c w hc hf
    exact ⟨c', c', ConfigEq.refl _, hw, hs⟩

/-- **`Task.wholeStep` implies `Task.wholeStepUpTo`**: the restatement is weaker. -/
theorem wholeStep_upTo (h : Task.wholeStep) : Task.wholeStepUpTo := by
  intro H hn hinj host hfin nd r
  obtain ⟨B, hf, hb⟩ := h H hn hinj host hfin nd r
  refine ⟨B, fun c c' hc hc' hs => ⟨c', ConfigEq.refl _, hf c c' hc hc' hs⟩, ?_⟩
  intro c w hc hs
  obtain ⟨c', hw, hst⟩ := hb c w hc hs
  exact ⟨c', c', ConfigEq.refl _, hw, hst⟩

end Silmaril.Wasm.SpecTec.Sim.Bwd

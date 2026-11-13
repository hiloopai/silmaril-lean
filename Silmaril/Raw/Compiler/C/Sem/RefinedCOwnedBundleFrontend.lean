module

public import Silmaril.Compiler.C.Sem.RefinedCOwnedFrontend.Defs
/-! Multiple positional owned singleton u8 pointers. Each cell denotes an exclusive
concrete byte resource. Explicit address distinctness makes their footprints
disjoint; the model makes no claim about C pointer provenance or RefinedC adequacy. -/
@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCOwnedBundleFrontend
open Silmaril.Cerberus.Assertion
open ConcreteResources
abbrev LocEnv := RefinedCOwnedFrontend.LocEnv

structure Cell where
  pointer : String
  input : Pure.Term
  output : Pure.Term
  deriving Repr, DecidableEq

structure Contract where
  parameters : List String
  locations : List String
  cells : List Cell
  requires : Pure.Formula
  ensures : Pure.Formula
  deriving Repr, DecidableEq

def Contract.pre (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    (args : List Int) (memory : C1.Memory) : Prop :=
  args = c.cells.map (fun cell => (locations cell.pointer : Int)) ∧
    (c.cells.map (fun cell => locations cell.pointer)).Nodup ∧
    (∀ cell ∈ c.cells, locations cell.pointer < 18446744073709551616) ∧
    (∀ cell ∈ c.cells, Holds ρ
      ((RefinedCOwnedByte.singleton (cell.input.eval ρ)).owned
        (locations cell.pointer) cell.input) memory) ∧ c.requires.holds ρ

def Contract.post (c : Contract) (ρ : Pure.Env) (locations : LocEnv)
    (memory : C1.Memory) : Prop :=
  (∀ cell ∈ c.cells, Holds ρ
    ((RefinedCOwnedByte.singleton (cell.output.eval ρ)).owned
      (locations cell.pointer) cell.output) memory) ∧ c.ensures.holds ρ

def Contract.obligation (c : Contract) (before after : Pure.Env) (locations : LocEnv)
    (args : List Int) (initial final : C1.Memory) : Prop :=
  c.pre before locations args initial → c.post after locations final

def Contract.leanGoal (c : Contract) (before after : Pure.Env) (locations : LocEnv)
    (args : List Int) (initial final : C1.Memory) : Prop :=
  (args = c.cells.map (fun cell => (locations cell.pointer : Int)) ∧
    (c.cells.map (fun cell => locations cell.pointer)).Nodup ∧
    (∀ cell ∈ c.cells, locations cell.pointer < 18446744073709551616) ∧
    (∀ cell ∈ c.cells, LeanGoal before
      ((RefinedCOwnedByte.singleton (cell.input.eval before)).owned
        (locations cell.pointer) cell.input) initial) ∧ c.requires.leanGoal before) →
  (∀ cell ∈ c.cells, LeanGoal after
    ((RefinedCOwnedByte.singleton (cell.output.eval after)).owned
      (locations cell.pointer) cell.output) final) ∧ c.ensures.leanGoal after

theorem Contract.leanGoal_correct (c : Contract) (before after : Pure.Env)
    (locations : LocEnv) (args : List Int) (initial final : C1.Memory) :
    c.leanGoal before after locations args initial final ↔
      c.obligation before after locations args initial final := by
  simp only [leanGoal, obligation, pre, post, ConcreteResources.leanGoal_correct,
    Pure.Formula.leanGoal_correct]

/-- The earlier one-pointer contract embeds without changing its meaning. -/
def Contract.ofSingle (c : RefinedCOwnedFrontend.Contract) : Contract :=
  ⟨c.parameters, c.locations, [⟨c.pointer, c.input, c.output⟩], c.requires, c.ensures⟩

theorem Contract.ofSingle_pre (c : RefinedCOwnedFrontend.Contract) (ρ : Pure.Env)
    (locations : LocEnv) (args : List Int) (memory : C1.Memory) :
    (ofSingle c).pre ρ locations args memory ↔ c.pre ρ locations args memory := by
  simp [ofSingle, pre, RefinedCOwnedFrontend.Contract.pre]

theorem Contract.ofSingle_post (c : RefinedCOwnedFrontend.Contract) (ρ : Pure.Env)
    (locations : LocEnv) (memory : C1.Memory) :
    (ofSingle c).post ρ locations memory ↔ c.post ρ locations memory := by
  simp [ofSingle, post, RefinedCOwnedFrontend.Contract.post]

theorem Contract.ofSingle_goal (c : RefinedCOwnedFrontend.Contract) (before after : Pure.Env)
    (locations : LocEnv) (args : List Int) (initial final : C1.Memory) :
    (ofSingle c).leanGoal before after locations args initial final ↔
      c.leanGoal before after locations args initial final := by
  rw [Contract.leanGoal_correct, RefinedCOwnedFrontend.Contract.leanGoal_correct]
  simp only [obligation, RefinedCOwnedFrontend.Contract.obligation, ofSingle_pre, ofSingle_post]

end Silmaril.Compile.C.Sem.RefinedCOwnedBundleFrontend

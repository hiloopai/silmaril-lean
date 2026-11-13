import Silmaril.Cerberus.Institution.Thms

open Silmaril.Cerberus.Institution
open Silmaril.Cerberus.Core.Dynamics

-- A terminal machine is terminating even with zero execution fuel.
example (program : Program) (labels : Labels) (outcome : Outcome) :
    Satisfies ⟨program, labels, {control := .halt outcome}⟩ terminates :=
  terminal_terminates _ outcome rfl

-- Universal safety detects UB already present at startup; no runner is needed.
example (program : Program) (labels : Labels) (location : Silmaril.Cerberus.Loc)
    (ub : Silmaril.Cerberus.UndefinedBehaviour) :
    ¬ Satisfies ⟨program, labels, {control := .halt (.ub location ub)}⟩ noUndefinedBehaviour := by
  intro safe
  exact safe _ (initial_realises _) location ub rfl

-- A vocabulary extension retains the meaning of an existing sentence.
example (left right : Signature) (inclusion : left ⊆ right)
    (model : (room right).Mod) (sentence : (room left).Sen) :
    (room right).Sat model ((inst.map (CategoryTheory.homOfLE inclusion)).sen sentence) ↔
      (room left).Sat model sentence :=
  satisfaction (CategoryTheory.homOfLE inclusion) model sentence

#print axioms run_realises
#print axioms terminal_terminates
#print axioms satisfies_of_refines

module

public import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Sequences.Thms
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.DataElab.NamedFunctions.FixedPoint

public section

namespace Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions

open Data Data.Tagged

universe u

namespace Definition

variable {d : Definition.{u}} {policy : Unspecified.{u}}

@[simp] theorem eval_zero (d : Definition.{u}) (policy : Unspecified.{u}) :
    d.eval policy 0 (Nat.zero_le _) = d.base := by rw [Definition.eval]

@[simp] theorem eval_succ {i : Nat} (hi : i < d.steps.length) :
    d.eval policy (i + 1) hi = d.steps[i].apply policy (d.eval policy i (Nat.le_of_lt hi)) := by
  rw [Definition.eval]

@[simp] theorem graph_domain (d : Definition.{u}) (policy : Unspecified.{u}) :
    (d.graph policy).domain = d.domain :=
  Proofs.graph_domain d policy

theorem graph_lookup {i : Nat} (hi : i ≤ d.steps.length) :
    (d.graph policy).lookup (.integer i) = some (d.eval policy i hi) :=
  Proofs.graph_lookup hi

theorem graph_apply {i : Nat} (hi : i ≤ d.steps.length) :
    (Value.function (d.graph policy)).apply policy (.integer i) = d.eval policy i hi :=
  Value.apply_function _ (Graph.lookup_eq_some.mp (d.graph_lookup hi))

theorem graph_fixedPoint (d : Definition.{u}) (policy : Unspecified.{u}) :
    d.FixedPoint policy (.function (d.graph policy)) :=
  Proofs.graph_fixedPoint d policy

theorem eq_of_fixedPoint {candidate : Value.{u}} (h : d.FixedPoint policy candidate) :
    candidate = .function (d.graph policy) :=
  Proofs.eq_of_fixedPoint h

theorem existsUnique_fixedPoint (d : Definition.{u}) (policy : Unspecified.{u}) :
    ∃! candidate, d.FixedPoint policy candidate :=
  ⟨_, d.graph_fixedPoint policy, fun _ h => d.eq_of_fixedPoint h⟩

/-- The reference CHOOSE abbreviation denotes the constructed graph for any
model choice policy, since its predicate has exactly one witness. -/
theorem choose_eq (choice : ChoicePolicy Value.{u}) (d : Definition.{u}) (policy : Unspecified.{u}) :
    choice.choose (d.FixedPoint policy) = .function (d.graph policy) :=
  d.eq_of_fixedPoint (choice.witness ⟨_, d.graph_fixedPoint policy⟩)

end Definition

theorem vmem_rhs_domain (policy : Unspecified.{u}) (sequence : SequencePolicy.{u})
    (wmem : Value.{u}) (entries : List Value.{u}) (candidate : Value.{u}) :
    (Value.function ((vmemDefinition policy wmem entries).rhs policy candidate)).domain policy =
      Value.interval policy (.integer 0) (Value.len sequence (.tuple entries)) :=
  Proofs.vmem_rhs_domain policy sequence wmem entries candidate

theorem vmem_rhs_zero (policy : Unspecified.{u}) (wmem : Value.{u})
    (entries : List Value.{u}) (candidate : Value.{u}) :
    (Value.function ((vmemDefinition policy wmem entries).rhs policy candidate)).apply policy
      (.integer 0) = wmem :=
  Proofs.vmem_rhs_zero policy wmem entries candidate

open Classical in
theorem vmem_rhs_succ (policy : Unspecified.{u}) (wmem : Value.{u})
    (entries : List Value.{u}) (candidate : Value.{u}) {i : Nat} (hi : i < entries.length) :
    let key : Int := ↑(i + 1)
    let request := ((Value.tuple entries).apply policy (.integer key)).apply policy (.integer 2)
    let previous := candidate.apply policy (.integer (key - 1))
    (Value.function ((vmemDefinition policy wmem entries).rhs policy candidate)).apply policy
        (.integer key) =
      if request.apply policy (.string "op") = .string "Rd" then previous
      else previous.updatePath policy [request.apply policy (.string "adr")]
        (fun _ => request.apply policy (.string "val")) :=
  Proofs.vmem_rhs_succ policy wmem entries candidate hi

/-- Interpret `LET f[...] == ... IN f[Len(memQ)]` using the book's definition
of the local name. The sequence is represented by its exact tuple value. -/
theorem vmem_eq_choose_apply_len (choice : ChoicePolicy Value.{u}) (policy : Unspecified.{u})
    (sequence : SequencePolicy.{u}) (wmem : Value.{u}) (entries : List Value.{u}) :
    vmem policy wmem entries =
      (choice.choose ((vmemDefinition policy wmem entries).FixedPoint policy)).apply policy
        (Value.len sequence (.tuple entries)) := by
  rw [Definition.choose_eq, Value.len_tuple]
  rfl

end Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions

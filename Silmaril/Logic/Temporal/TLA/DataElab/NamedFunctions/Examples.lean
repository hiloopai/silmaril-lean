module

import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Thms

namespace Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions

open Data.Tagged

private def invalid : Unspecified.{0} := fun _ _ => .integer 999

private noncomputable def memory : Graph.{0} := .tuple [.integer 0, .integer 42]

private noncomputable def readRequest : Value.{0} :=
  .record ["op", "adr"] fun name => if name = "op" then .string "Rd" else .integer 1

private noncomputable def writeRequest (n : Int) : Value.{0} :=
  .record ["op", "adr", "val"] fun name =>
    if name = "op" then .string "Wr" else if name = "adr" then .integer 1 else .integer n

private noncomputable def entry (request : Value.{0}) : Value.{0} :=
  .tuple [.integer 100, request]

private theorem entry_request (request : Value.{0}) : (entry request).apply invalid (.integer 2) = request :=
  Value.apply_function _ (Graph.lookup_eq_some.mp
    (Graph.lookup_tuple (i := 1) [.integer 100, request] (by simp)))

private theorem read_step : vmemStep invalid (entry readRequest) = .keep := by
  have hop : readRequest.apply invalid (.string "op") = .string "Rd" :=
    Value.apply_function _ (Graph.lookup_eq_some.mp (Graph.lookup_record _ (by simp)))
  dsimp only [vmemStep]
  rw [entry_request, hop, ite_eq_left rfl]

private theorem write_step (n : Int) :
    vmemStep invalid (entry (writeRequest n)) = .write (.integer 1) (.integer n) := by
  have hop : (writeRequest n).apply invalid (.string "op") = .string "Wr" := by
    apply Value.apply_function
    exact Graph.lookup_eq_some.mp (Graph.lookup_record _ (by simp))
  have hadr : (writeRequest n).apply invalid (.string "adr") = .integer 1 := by
    apply Value.apply_function
    exact Graph.lookup_eq_some.mp (Graph.lookup_record _ (by simp))
  have hval : (writeRequest n).apply invalid (.string "val") = .integer n := by
    apply Value.apply_function
    exact Graph.lookup_eq_some.mp (Graph.lookup_record _ (by simp))
  have hne : (Value.string.{0} "Wr") ≠ .string "Rd" :=
    Value.string_injective.ne (by decide)
  dsimp only [vmemStep]
  rw [entry_request, hop, ite_eq_right hne, hadr, hval]

-- An empty sequence gives the singleton local graph whose only result is wmem.
example : vmem invalid (.function memory) [] = .function memory := by
  rw [vmem, Definition.graph_apply (by simp [vmemDefinition])]
  change (vmemDefinition invalid (.function memory) []).eval invalid 0 (Nat.zero_le _) = _
  rw [Definition.eval_zero]
  rfl

private noncomputable def entries : List Value.{0} :=
  [entry (writeRequest 7), entry readRequest, entry (writeRequest 9), entry readRequest]

-- The final read leaves the last queued write in place. The sibling key survives both writes.
example : vmem invalid (.function memory) entries =
    .function ((memory.update (.integer 1) (.integer 7)).update (.integer 1) (.integer 9)) := by
  have hd : vmemDefinition invalid (.function memory) entries =
      ⟨.function memory, [.write (.integer 1) (.integer 7), .keep, .write (.integer 1) (.integer 9), .keep]⟩ := by
    simp [vmemDefinition, entries, write_step, read_step]
  rw [vmem, Definition.graph_apply (by simp [vmemDefinition])]
  change (vmemDefinition invalid (.function memory) entries).eval invalid 4 (by simp [hd]) = _
  simp only [hd, Definition.eval_zero, Definition.eval_succ, List.getElem_cons_succ, List.getElem_cons_zero,
    Step.apply, Value.update_function]

-- Equal cardinality does not suffice: a tuple graph starts at 1, while f starts at 0.
example : ¬ (vmemDefinition invalid (.function memory) []).FixedPoint invalid
    (.tuple [.function memory]) := by
  intro h
  have hd := congrArg Graph.domain (Value.function_injective (Definition.eq_of_fixedPoint h))
  rw [Graph.domain_tuple, Definition.graph_domain] at hd
  have hz : (vmemDefinition invalid (.function memory) []).domain.mem (.integer 0) := by
    simp [Definition.domain, vmemDefinition, SetData.integer_mem_intRange]
  rw [← hd] at hz
  simp [SetData.integer_mem_intRange] at hz

end Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions

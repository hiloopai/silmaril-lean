module

public import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Sequences.Thms
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Thms

public section

namespace Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Proofs

open Data Data.Tagged

universe u

variable {d : Definition.{u}} {policy : Unspecified.{u}} {i : Nat}

private theorem mem_domain (hi : i ≤ d.steps.length) : d.domain.mem (.integer i) := by
  rw [Definition.domain, SetData.integer_mem_intRange]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hi⟩

private theorem index_of_mem {key : Value.{u}} (hk : d.domain.mem key) :
    ∃ i : Nat, key = .integer i ∧ i ≤ d.steps.length := by
  obtain ⟨k, rfl, h0, hn⟩ := (SetData.mem_intRange 0 (↑d.steps.length)).mp hk
  exact ⟨k.toNat, congrArg Value.integer (Int.toNat_of_nonneg h0).symm, by omega⟩

private theorem graphOf_lookup (body : (i : Nat) → i ≤ d.steps.length → Value.{u})
    (hi : i ≤ d.steps.length) :
    (d.graphOf body).lookup (.integer i) = some (body i hi) := by
  rw [Definition.graphOf, Graph.lookup_ofFn (mem_domain hi)]
  simp [hi]

theorem graph_domain (d : Definition.{u}) (policy : Unspecified.{u}) :
    (d.graph policy).domain = d.domain := by
  simp only [Definition.graph, Definition.graphOf, Graph.domain_ofFn]

theorem graph_lookup (hi : i ≤ d.steps.length) :
    (d.graph policy).lookup (.integer i) = some (d.eval policy i hi) :=
  graphOf_lookup (d.eval policy) hi

private theorem rhs_domain (candidate : Value.{u}) : (d.rhs policy candidate).domain = d.domain := by
  simp only [Definition.rhs, Definition.graphOf, Graph.domain_ofFn]

private theorem rhs_lookup_zero (candidate : Value.{u}) :
    (d.rhs policy candidate).lookup (.integer (↑(0 : Nat))) = some d.base :=
  graphOf_lookup (d := d) _ (Nat.zero_le _)

private theorem rhs_lookup_succ (candidate : Value.{u}) (hi : i < d.steps.length) :
    (d.rhs policy candidate).lookup (.integer (↑(i + 1))) =
      some (d.steps[i].apply policy (candidate.apply policy (.integer i))) :=
  graphOf_lookup (d := d) _ hi

private theorem apply_graph (hi : i ≤ d.steps.length) :
    (Value.function (d.graph policy)).apply policy (.integer i) = d.eval policy i hi :=
  Value.apply_function _ (Graph.lookup_eq_some.mp (graph_lookup hi))

theorem graph_fixedPoint (d : Definition.{u}) (policy : Unspecified.{u}) :
    d.FixedPoint policy (.function (d.graph policy)) := by
  apply congrArg Value.function
  apply Graph.ext_of_domain_lookup
  · rw [graph_domain, rhs_domain]
  intro key hk
  rw [graph_domain] at hk
  obtain ⟨i, rfl, hi⟩ := index_of_mem hk
  cases i with
  | zero => rw [graph_lookup hi, rhs_lookup_zero, Definition.eval]
  | succ i =>
    have h : i < d.steps.length := hi
    rw [graph_lookup hi, rhs_lookup_succ _ h, apply_graph (Nat.le_of_lt h), Definition.eval]

theorem eq_of_fixedPoint {candidate : Value.{u}} (h : d.FixedPoint policy candidate) :
    candidate = .function (d.graph policy) := by
  have hgraph : d.rhs policy candidate = d.graph policy := by
    apply Graph.ext_of_domain_lookup
    · rw [rhs_domain, graph_domain]
    intro key hk
    rw [rhs_domain] at hk
    obtain ⟨i, rfl, hi⟩ := index_of_mem hk
    clear hk
    induction i with
    | zero => rw [rhs_lookup_zero, graph_lookup hi, Definition.eval]
    | succ i ih =>
      have hlt : i < d.steps.length := hi
      have happly : candidate.apply policy (.integer i) = d.eval policy i (Nat.le_of_lt hlt) := by
        conv => lhs; rw [show candidate = .function (d.rhs policy candidate) from h]
        apply Value.apply_function
        rw [← Graph.lookup_eq_some, ih (Nat.le_of_lt hlt)]
        exact graph_lookup (Nat.le_of_lt hlt)
      rw [rhs_lookup_succ _ hlt, happly, graph_lookup hi, Definition.eval]
  exact h.trans (congrArg Value.function hgraph)

theorem vmem_rhs_domain (policy : Unspecified.{u}) (sequence : SequencePolicy.{u})
    (wmem : Value.{u}) (entries : List Value.{u}) (candidate : Value.{u}) :
    (Value.function ((vmemDefinition policy wmem entries).rhs policy candidate)).domain policy =
      Value.interval policy (.integer 0) (Value.len sequence (.tuple entries)) := by
  simp [rhs_domain, Definition.domain, vmemDefinition]

theorem vmem_rhs_zero (policy : Unspecified.{u}) (wmem : Value.{u})
    (entries : List Value.{u}) (candidate : Value.{u}) :
    (Value.function ((vmemDefinition policy wmem entries).rhs policy candidate)).apply policy
      (.integer 0) = wmem :=
  Value.apply_function _ (Graph.lookup_eq_some.mp (rhs_lookup_zero (d := vmemDefinition policy wmem entries) candidate))

open Classical in
theorem vmem_rhs_succ (policy : Unspecified.{u}) (wmem : Value.{u})
    (entries : List Value.{u}) (candidate : Value.{u}) (hi : i < entries.length) :
    let key : Int := ↑(i + 1)
    let request := ((Value.tuple entries).apply policy (.integer key)).apply policy (.integer 2)
    let previous := candidate.apply policy (.integer (key - 1))
    (Value.function ((vmemDefinition policy wmem entries).rhs policy candidate)).apply policy
        (.integer key) =
      if request.apply policy (.string "op") = .string "Rd" then previous
      else previous.updatePath policy [request.apply policy (.string "adr")]
        (fun _ => request.apply policy (.string "val")) := by
  classical
  have hstep : i < (vmemDefinition policy wmem entries).steps.length := by
    simpa [vmemDefinition] using hi
  have hentry : (Value.tuple entries).apply policy (.integer (↑(i + 1))) = entries[i] :=
    Value.apply_function _ (Graph.lookup_eq_some.mp (Graph.lookup_tuple entries hi))
  have hpred : (↑(i + 1) : Int) - 1 = ↑i := by omega
  dsimp only
  rw [Value.apply_function _ (Graph.lookup_eq_some.mp (rhs_lookup_succ candidate hstep)), hentry, hpred]
  simp only [vmemDefinition, List.getElem_map, vmemStep, Value.updatePath_single]
  split <;> rfl

end Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Proofs

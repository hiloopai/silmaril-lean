module

public import Silmaril.Compiler.Native.Optimize.Validation.Acceptance.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Acceptance
open Silmaril.Compile
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem expr_beq (left right : Expr) : (left == right) = true ↔ left = right := by
  change instBEqExpr.beq left right = true ↔ left = right
  cases left <;> cases right <;> simp [instBEqExpr.beq]

theorem effect_beq (left right : Effect) : (left == right) = true ↔ left = right := by
  change instBEqEffect.beq left right = true ↔ left = right
  cases left <;> cases right <;> simp [instBEqEffect.beq]

theorem term_beq (left right : Term) : (left == right) = true ↔ left = right := by
  change instBEqTerm.beq left right = true ↔ left = right
  cases left <;> cases right <;> simp [instBEqTerm.beq]

instance : LawfulBEq Expr where
  eq_of_beq := fun equal => (expr_beq _ _).mp equal
  rfl := (expr_beq _ _).mpr rfl

instance : LawfulBEq Effect where
  eq_of_beq := fun equal => (effect_beq _ _).mp equal
  rfl := (effect_beq _ _).mpr rfl

instance : LawfulBEq Term where
  eq_of_beq := fun equal => (term_beq _ _).mp equal
  rfl := (term_beq _ _).mpr rfl

theorem output_beq (left right : Term × List Nat) : (left == right) = true ↔ left = right := by
  exact beq_iff_eq

theorem effects_beq (left right : Array Effect) : (left == right) = true ↔ left = right := by
  exact beq_iff_eq

/-- Exact unfolding of the current checker, retaining its guard/slot order. -/
theorem check_run (freshBase : Nat) (source candidate : Mir.Block) :
    check freshBase source candidate =
      if source.instrs.size > 4096 || candidate.instrs.size > 8192 then false
      else if !(candidate.instrs.all fun i => (defs i).all fun r =>
          freshBase ≤ r || (observedRegs source).contains r) then false
      else if (candidateRun source candidate).2.nodes.any Expr.isPartialLeaf
          (sourceRun source).2.nodes.size then false
      else if (sourceRun source).1 != (candidateRun source candidate).1 ||
          (sourceRun source).2.effects != (candidateRun source candidate).2.effects then false
      else (sourceSlotRun source candidate).1 == (candidateSlotRun source candidate).1 := by
  rfl

theorem accepted_iff (freshBase : Nat) (source candidate : Mir.Block) :
    Accepted freshBase source candidate ↔
      source.instrs.size ≤ 4096 ∧ candidate.instrs.size ≤ 8192 ∧
      (candidate.instrs.all fun i => (defs i).all fun r =>
        freshBase ≤ r || (observedRegs source).contains r) = true ∧
      (candidateRun source candidate).2.nodes.any Expr.isPartialLeaf
        (sourceRun source).2.nodes.size = false ∧
      (sourceRun source).1.1 = (candidateRun source candidate).1.1 ∧
      (sourceRun source).1.2 = (candidateRun source candidate).1.2 ∧
      (sourceRun source).2.effects = (candidateRun source candidate).2.effects ∧
      (sourceSlotRun source candidate).1 = (candidateSlotRun source candidate).1 := by
  constructor
  · intro actual
    exact ⟨actual.source_size, actual.candidate_size, actual.writes, actual.partialLeaves,
      actual.term, actual.observed, actual.effects, actual.slots⟩
  · rintro ⟨sourceSize, candidateSize, writes, guard, term, observed, effects, slots⟩
    exact ⟨sourceSize, candidateSize, writes, guard, term, observed, effects, slots⟩

theorem check_eq_true_iff (freshBase : Nat) (source candidate : Mir.Block) :
    check freshBase source candidate = true ↔ Accepted freshBase source candidate := by
  rw [check_run, accepted_iff]
  simp [Prod.ext_iff, and_assoc]
  intro _ _ _ _ _ _ _
  constructor
  · intro writes index bounded reg defined
    by_cases fresh : freshBase ≤ reg
    · exact .inl fresh
    · exact .inr (writes index bounded reg defined (by omega))
  · intro writes index bounded reg defined below
    rcases writes index bounded reg defined with fresh | old
    · omega
    · exact old

/-- The actual retained guard excludes every candidate-added partial leaf at
the final block state, before slot comparisons can extend that DAG further. -/
theorem no_new_partial (freshBase : Nat) (source candidate : Mir.Block)
    (accepted : Accepted freshBase source candidate) (index : Nat)
    (lower : (sourceRun source).2.nodes.size ≤ index)
    (bounded : index < (candidateRun source candidate).2.nodes.size) :
    Expr.isPartialLeaf (candidateRun source candidate).2.nodes[index] = false := by
  apply Bool.eq_false_iff.mpr
  intro isPartial
  apply (Bool.eq_false_iff.mp accepted.partialLeaves)
  exact Array.any_iff_exists.mpr ⟨index, bounded, lower, bounded, isPartial⟩

/-- Every checked candidate write is fresh or names an actual source output. -/
theorem candidate_write (freshBase : Nat) (source candidate : Mir.Block)
    (accepted : Accepted freshBase source candidate) (instruction : Mir.Instr)
    (member : instruction ∈ candidate.instrs) (reg : Nat) (defined : reg ∈ defs instruction) :
    freshBase ≤ reg ∨ reg ∈ observedRegs source := by
  have instructionOkay := Array.all_eq_true_iff_forall_mem.mp accepted.writes instruction member
  have regOkay := List.all_eq_true.mp instructionOkay reg defined
  simpa using regOkay

end Silmaril.Compiler.Native.Optimize.Validation.Acceptance

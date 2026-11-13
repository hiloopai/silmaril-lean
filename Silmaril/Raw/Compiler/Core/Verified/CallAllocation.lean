module

public import Silmaril.Compiler.Core.Verified.Locals.Defs
/-! # Argument allocation is not reclaimed by caller cleanup

A parameter-call continuation needs a decreasing allocation reserve. The Core
allocator reports exhaustion as an error, and killing the argument does not restore
the allocation frontier. In particular a finite reserve cannot be invariant under
arbitrarily many calls along a CFG back edge.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.CallAllocation

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Mem.Concrete

/-- Failed argument allocation is an error, rather than a source UB escape. -/
theorem exhausted (tags : Tags) (ann : List Annot) (m : State)
    (h : nextIntAddress m ≤ 0) :
    allocateTyped tags m 4 (intType ann) = .error (.invalid "allocation exhausted") := by
  unfold nextIntAddress at h
  simp only [allocateTyped, layout_intType, bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right (by decide), ite_eq_left h]
  rfl

/-- The caller's `kill` does not replenish address space. -/
theorem kill_frontier (m : State) (id : Int) :
    (Locals.killed m id).lastAddress = m.lastAddress := rfl

theorem created_frontier (pref : Prefix) (ann : List Annot) (m : State) :
    (Actions.created pref ann m).lastAddress = nextIntAddress m := by
  unfold Actions.created
  rw [Locals.updateLastAllocation_lastAddress]

/-- A concrete two-allocation counterexample: the first argument fits, but killing
it still leaves no room for the next one. The witness has no dead identifiers. -/
theorem cleanup_does_not_replenish (tags : Tags) :
    let m : State := {lastAddress := 8}
    let after := Locals.killed (Actions.created (.other "argument") [] m) m.nextId
    0 < nextIntAddress m ∧ m.dead = [] ∧
      after.lastAddress = 4 ∧
      allocateTyped tags after 4 (intType []) = .error (.invalid "allocation exhausted") := by
  dsimp only
  have last : (Locals.killed (Actions.created (.other "argument") []
      {lastAddress := 8}) 0).lastAddress = 4 := by
    rw [kill_frontier, created_frontier]
    decide
  refine ⟨by decide, rfl, last, exhausted tags [] _ ?_⟩
  simp only [nextIntAddress, last]
  decide

end Silmaril.Compile.Core.Verified.CallAllocation

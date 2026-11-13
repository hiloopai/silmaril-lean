module

public import Silmaril.Compiler.Native.Optimize.Validation.Leaf.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Leaf
open Silmaril.Machine

/-- Empty checker roots do not constrain the external address interpretation. -/
theorem initial_rooted (frame : Lir.Frame Nat) (address : String → Nat → Option Lir.Word) :
    Roots.Rooted {} frame (initialMeaning frame address) := by
  constructor
  · intro index expression found
    simp at found
  · intro index expression found
    simp at found
  · intro root member
    cases member
  · intro root member
    cases member
  · intro reg
    rfl
  · intro slot
    rfl

theorem partial_normalize (nodes : Array Expr) (raw : Expr) (partialLeaf : raw.isPartialLeaf = true) :
    normalize nodes raw = raw := by
  cases raw <;> simp_all [Expr.isPartialLeaf, normalize]

theorem partial_scoped (bound : Nat) (raw : Expr) (partialLeaf : raw.isPartialLeaf = true) :
    Intern.ReferencesBelow bound raw := by
  cases raw <;> simp_all [Expr.isPartialLeaf, Intern.ReferencesBelow]

/-- An actual guarded intern of any partial leaf must reuse a total retained
node. This includes input registers, slots and unresolved-address leaves alike. -/
theorem intern_partial_defined (state : State) (meaning : Interpretation)
    (coherent : Intern.Coherent state.nodes meaning) (total : Total.TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size) (raw : Expr)
    (partialLeaf : raw.isPartialLeaf = true)
    (guarded : Candidate.Guarded sourceSize ((intern raw).run state).2.nodes) :
    ∃ word, raw.eval meaning = some word := by
  have atIndex : ((intern raw).run state).2.nodes[((intern raw).run state).1]? = some raw := by
    simpa only [partial_normalize state.nodes raw partialLeaf] using (Intern.returned_index state raw).2
  have retained : ((intern raw).run state).1 < sourceSize := guarded _ _ atIndex partialLeaf
  have before : ((intern raw).run state).1 < state.nodes.size := Nat.lt_of_lt_of_le retained old
  have oldNode : state.nodes[((intern raw).run state).1]? = some raw :=
    (Intern.old_node state raw before).symm.trans atIndex
  obtain ⟨word, defined⟩ := total _ before
  exact ⟨word, (coherent _ _ oldNode).symm.trans defined⟩

/-- Construct the genuine rooted/total intern result from retained-leaf
success. No candidate execution or successful target read is supplied. -/
theorem intern_partial_success (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (rooted : Roots.Rooted state frame meaning) (total : Total.TotalNodes state.nodes meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size) (raw : Expr)
    (partialLeaf : raw.isPartialLeaf = true)
    (guarded : Candidate.Guarded sourceSize ((intern raw).run state).2.nodes) :
    ∃ word newMeaning, Roots.ReadResult state ((intern raw).run state).2 frame (some word)
      ((intern raw).run state).1 meaning newMeaning ∧ Total.TotalNodes ((intern raw).run state).2.nodes newMeaning := by
  obtain ⟨word, defined⟩ := intern_partial_defined state meaning rooted.coherent total sourceSize old raw partialLeaf guarded
  obtain ⟨newMeaning, result, afterTotal⟩ := Total.intern_sound state frame meaning rooted total raw
    (partial_scoped state.nodes.size raw partialLeaf) word defined
  exact ⟨word, newMeaning, result, afterTotal⟩

/-- The actual checker seed retains the successful source DAG while resetting
its register and slot roots to the original partial incoming frame. -/
theorem seed_rooted (frame sourceFrame : Lir.Frame Nat) (address : String → Nat → Option Lir.Word)
    (sourceState : State) (meaning : Interpretation)
    (source : Roots.OpResult {} sourceState sourceFrame (initialMeaning frame address) meaning) :
    Roots.Rooted { nodes := sourceState.nodes } frame meaning := by
  refine ⟨source.rooted.wellScoped, source.rooted.coherent, ?_, ?_, ?_, ?_⟩
  · intro root member
    cases member
  · intro root member
    cases member
  · intro reg
    exact congrFun source.extension.input reg
  · intro slot
    exact congrFun source.extension.slot slot

end Silmaril.Compiler.Native.Optimize.Validation.Leaf

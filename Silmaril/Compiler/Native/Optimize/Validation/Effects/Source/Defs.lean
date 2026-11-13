module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Load.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Leaf.Thms
/-! Source symbolic state carries real ordered effects, current memory and the
actual source load results. No candidate execution or total input frame. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Source
open Silmaril.Machine Silmaril.Compile

structure Result (before after : State) (frame : Lir.Frame Nat)
    (oldMeaning newMeaning : Interpretation) : Prop where
  rooted : Roots.Rooted after frame newMeaning
  total : Total.TotalNodes after.nodes newMeaning
  loads : LoadsScoped after.nodes after.effects.size
  extension : PrefixExtends before.nodes.size before.effects.size oldMeaning newMeaning
  grows : before.nodes.size ≤ after.nodes.size

def Safe {α : Type} (action : StateM State α) : Prop :=
  ∀ state, LoadsScoped state.nodes state.effects.size →
    LoadsScoped (action.run state).2.nodes (action.run state).2.effects.size

def EffectsScoped (state : State) : Prop :=
  ∀ effect ∈ state.effects.toList, EffectReferencesBelow state.nodes.size effect

def LoadResults (effects : Array Effect) (words : List (Option Lir.Word)) (meaning : Interpretation) : Prop :=
  ∀ event width ext base offset, effects[event]? = some (.load width ext base offset) →
    meaning.load event = (words[event]?).getD none

/-- The external address interpretation is fixed at source entry, independently
of the actual partial input frame and evolving real memory/load trace. -/
structure InvariantWith (address : String → Nat → Option Lir.Word) (initialFrame : Lir.Frame Nat) (initialMemory : Lir.Memory)
    (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (words : List (Option Lir.Word)) (meaning : Interpretation) : Prop where
  rooted : Roots.Rooted state frame meaning
  total : Total.TotalNodes state.nodes meaning
  loads : LoadsScoped state.nodes state.effects.size
  effects : EffectsScoped state
  inputs : PrefixExtends 0 0 (Leaf.initialMeaning initialFrame address) meaning
  executed : runEffects meaning state.effects.toList initialMemory = some (words, memory)
  count : words.length = state.effects.size
  loadResults : LoadResults state.effects words meaning

/-- Existing users retain exactly the original absent-address interpretation. -/
abbrev Invariant (initialFrame : Lir.Frame Nat) (initialMemory : Lir.Memory)
    (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (words : List (Option Lir.Word)) (meaning : Interpretation) : Prop :=
  InvariantWith (fun _ _ => none) initialFrame initialMemory state frame memory words meaning

end Silmaril.Compiler.Native.Optimize.Validation.Effects.Source

@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Source
open Silmaril.Machine

structure BlockResultWith (address : String → Nat → Option Lir.Word) (initialFrame : Lir.Frame Nat) (initialMemory : Lir.Memory)
    (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory) (words : List (Option Lir.Word))
    (term : Term) (indices : List Nat) (exit : BlockExit) (values : List Lir.Word) (meaning : Interpretation) : Prop where
  invariant : InvariantWith address initialFrame initialMemory state frame memory words meaning
  termScoped : Observation.TermScoped state.nodes.size term
  selected : Observation.termExit meaning term = some exit
  observedBounded : ∀ index ∈ indices, index < state.nodes.size
  observed : indices.mapM meaning.value = some values

/-- The original absent-address source block interface remains definitionally
identical. The generic form retains the source's fixed external resolver. -/
abbrev BlockResult (initialFrame : Lir.Frame Nat) (initialMemory : Lir.Memory)
    (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory) (words : List (Option Lir.Word))
    (term : Term) (indices : List Nat) (exit : BlockExit) (values : List Lir.Word) (meaning : Interpretation) : Prop :=
  BlockResultWith (fun _ _ => none) initialFrame initialMemory state frame memory words term indices exit values meaning

end Silmaril.Compiler.Native.Optimize.Validation.Effects.Source

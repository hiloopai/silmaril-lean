module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Source.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Candidate.Thms
/-! Candidate effect prefixes are read against the actual complete source
trace and its fixed final ghost load interpretation. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Candidate
open Silmaril.Machine Silmaril.Compile

def EffectPrefix (before after : Array Effect) : Prop :=
  ∃ suffix : List Effect, after.toList = before.toList ++ suffix

def EffectGrowing {α : Type} (action : StateM State α) : Prop :=
  ∀ state, EffectPrefix state.effects (action.run state).2.effects

/-- Ordered concrete event execution in relational form, with real memory
transitions and result words at every exact symbolic effect index. -/
inductive Replay (meaning : Interpretation) : List Effect → Lir.Memory →
    List (Option Lir.Word) → Lir.Memory → Prop
  | nil (memory) : Replay meaning [] memory [] memory
  | cons (effect : Effect) (rest : List Effect) (event : Event) (word : Option Lir.Word)
      (words : List (Option Lir.Word)) (memory middle final : Lir.Memory)
      (concrete : concreteEffect meaning effect = some event)
      (executed : event.exec memory = some (word, middle))
      (later : Replay meaning rest middle words final) :
      Replay meaning (effect :: rest) memory (word :: words) final

/-- The complete successful source trace and the actually consumed candidate
prefix share the same initial memory and fixed load-result interpretation. -/
structure Trace (source state : State) (meaning : Interpretation)
    (initialMemory memory finalMemory : Lir.Memory)
    (sourceWords words : List (Option Lir.Word)) : Prop where
  prefixEffects : EffectPrefix state.effects source.effects
  references : Source.EffectsScoped source
  sourceRun : runEffects meaning source.effects.toList initialMemory = some (sourceWords, finalMemory)
  currentRun : runEffects meaning state.effects.toList initialMemory = some (words, memory)
  loadResults : Source.LoadResults source.effects sourceWords meaning

/-- Candidate node-value extensions keep the complete source-final ghost load
map fixed. Source prefix extension is used only while deriving that map. -/
structure Result (before after : State) (frame : Lir.Frame Nat)
    (oldMeaning newMeaning : Interpretation) : Prop where
  rooted : Roots.Rooted after frame newMeaning
  total : Total.TotalNodes after.nodes newMeaning
  extension : Roots.Extends before.nodes.size oldMeaning newMeaning
  grows : before.nodes.size ≤ after.nodes.size


/-- Candidate block observations are interpreted by a rooted total final DAG;
the result permits actual memory effects rather than requiring an empty trace. -/
structure BlockResult (before after : State) (frame : Lir.Frame Nat)
    (term : Term) (indices : List Nat) (exit : BlockExit) (values : List Lir.Word)
    (oldMeaning newMeaning : Interpretation) : Prop where
  result : Result before after frame oldMeaning newMeaning
  termScoped : Observation.TermScoped after.nodes.size term
  selected : Observation.termExit newMeaning term = some exit
  observedBounded : ∀ index ∈ indices, index < after.nodes.size
  observed : indices.mapM newMeaning.value = some values

end Silmaril.Compiler.Native.Optimize.Validation.Effects.Candidate

module

public import Silmaril.Cerberus.Core.Administrative.Thms
public import Silmaril.Compiler.Core.Source.PureEval.Defs
/-! Actual administrative traces of the existing big-step pure evaluator.
The continuation hypotheses describe scheduling predicates, never execution or
adequacy. Pure expression frames preserve them structurally. -/
@[expose] public section
namespace Silmaril.Compiler.Core.Source.PureAdministrative
open Silmaril.Cerberus.Core
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

def FramesPlain (frames : List Frame) : Prop :=
  controlHasCCall (.value .unit) frames = false ∧ activeCall (.value .unit) frames = false

def NoProcedure : Prim → Prop
  | .procedure _ => False
  | _ => True

def Sound (file : Program) (tags : Mem.Concrete.Tags) (environment : Env) :
    PE ⊕ List PE → Val ⊕ List Val → Prop
  | .inl expression, .inl value => ∀ labels frames memory, FramesPlain frames →
      PureEval.tagsOf file memory = tags → Administrative.Path file labels
        ⟨.pureExpr expression environment, frames, memory⟩ ⟨.value value, frames, memory⟩
  | .inr expressions, .inr values => ∀ labels operator acc frames memory,
      NoProcedure operator → FramesPlain frames → PureEval.tagsOf file memory = tags →
      Administrative.Path file labels (PureEval.argState operator acc expressions environment frames memory)
        ⟨.apply operator (acc ++ values), frames, memory⟩
  | _, _ => True

end Silmaril.Compiler.Core.Source.PureAdministrative

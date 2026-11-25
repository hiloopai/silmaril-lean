module

public import Silmaril.Parse.DecodeGraph.ByteParse.Defs
import Silmaril.Proofs.Parse.DecodeGraph.ByteParse

public section

namespace Silmaril.Parse.DecodeGraph

variable {Context Buffer : Type*}

theorem soundFor_ofParser {Value : Type} {grammar : ByteParse.Bytes → Value → Prop}
    {parser : ByteParse.Parser Value} :
    SoundFor .byteArray (ofParser parser) (ofGrammar fun _ => grammar) ↔ ByteParse.Sound grammar parser :=
  Proofs.soundFor_ofParser

theorem completeFor_ofParser {Value : Type} {grammar : ByteParse.Bytes → Value → Prop}
    {parser : ByteParse.Parser Value} :
    CompleteFor .byteArray (ofParser parser) (ofGrammar fun _ => grammar) ↔ ByteParse.Complete grammar parser :=
  Proofs.completeFor_ofParser

theorem successes_deterministic {Value : Type} (run : Context → Buffer → Nat → Nat → ByteParse.Res Value) :
    Deterministic (successes run) := Proofs.successes_deterministic run

theorem pure_zero_success {Value : Type} (value : Value) (input : Input Unit ByteArray) :
    (input, (value, input.pos)) ∈ ofParser (pure value) := rfl

theorem positive_ofGrammar {Value : Type} {grammar : Context → ByteParse.Bytes → Value → Prop}
    (nonempty : ∀ ctx, ByteParse.NonEmpty (grammar ctx)) : Positive (ofGrammar grammar) :=
  Proofs.positive_ofGrammar nonempty

end Silmaril.Parse.DecodeGraph

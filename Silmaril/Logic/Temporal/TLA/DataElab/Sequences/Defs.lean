module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Sequences.Thms
public import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Tagged

/-! A signature-only interpretation of the standard operators used by the sequence and named-function source profiles. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Sequences

open Resolution Data.Tagged
open DataElab.Tagged (NumericPrimitive Policy)

universe u

@[expose] public section

/-- Revision of the standard-module sources that this profile identifies. -/
def revision : String := "bc1b506bdcad80bb518bf3776a9161c34ff0fc4c"

def naturalsId : ModuleId := "tlaplus/" ++ revision ++ "/Naturals"
def sequencesId : ModuleId := "tlaplus/" ++ revision ++ "/Sequences"

abbrev Operator := Sum NumericPrimitive SequenceOp

def Operator.arity (op : Operator) : Nat :=
  op.elim NumericPrimitive.arity SequenceOp.arity

/-- Names and denotations in each signature, in declaration-ID order. -/
def modules : List (ModuleId × String × List (Name × Operator)) :=
  [(naturalsId, "Naturals",
      [(.ident "Nat", .inl .naturals), (.symbol .infix "<", .inl .lt),
       (.symbol .infix "\\leq", .inl .le), (.symbol .infix "..", .inl .interval),
       (.symbol .infix "-", .inl .sub)]),
    (sequencesId, "Sequences",
      [(.ident "Seq", .inr .seq), (.ident "Len", .inr .len), (.ident "Append", .inr .append),
       (.ident "Head", .inr .head), (.ident "Tail", .inr .tail)])]

/-- The client links its imports to these identities after verifying the
standard-library distribution. The signature exports only the admitted
operators. Sequences' LOCAL INSTANCE of Naturals supplies no exports. -/
def inputs : List (ModuleId × ModuleInput) :=
  modules.map fun (id, name, operators) =>
    (id, .signature name [] (operators.map fun (op, interpretation) =>
      .operator op (List.replicate interpretation.arity .expression)))

def operatorAt : BindingId → Option Operator
  | .declared ⟨id, [.member index]⟩ => do
    let (_, operators) ← modules.lookup id
    return (← operators[index]?).2
  | _ => none

def signature : ExternalSignature := fun id => (operatorAt id).map Operator.arity

end

/-- Every admitted argument contributes to the result and may be action level. -/
public def levels : Levels.ExternalLevels :=
  modules.flatMap fun (id, _, operators) =>
    operators.zipIdx.map fun ((_, op), index) =>
      (.declared ⟨id, [.member index]⟩, ⟨.constant, List.replicate op.arity ⟨.action, true⟩⟩)

private noncomputable def run (invalid : SequencePolicy.{u}) :
    SequenceOp → List Value.{u} → Option Value.{u}
  | .seq, [s] => some (s.seq invalid)
  | .len, [s] => some (s.len invalid)
  | .append, [s, e] => some (s.append invalid e)
  | .head, [s] => some (s.head invalid)
  | .tail, [s] => some (s.tail invalid)
  | _, _ => none

private theorem run_sound (invalid : SequencePolicy.{u}) (op : SequenceOp)
    (args : List Value.{u}) (h : args.length = op.arity) :
    run invalid op args = some ((run invalid op args).getD (.set .empty)) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    cases op <;> simp [SequenceOp.arity, run] at *

public section

/-- Interpret the admitted operators using the fixed numeric and sequence policies. -/
noncomputable def primitive (policy : Policy.{u}) (invalid : SequencePolicy.{u}) :
    (op : Operator) → Primitive Value.{u} op.arity
  | .inl op => policy.primitive op
  | .inr op =>
    { apply := fun args => (run invalid op args).getD (.set .empty)
      spec := fun args result => run invalid op args = some result
      sound := run_sound invalid op }

private noncomputable def interpret (policy : Policy.{u}) (invalid : SequencePolicy.{u})
    (arity : Nat) :
    (op : Option Operator) → op.map Operator.arity = some arity → Primitive Value.{u} arity
  | none, admitted => by simp at admitted
  | some op, admitted => (Option.some.inj admitted) ▸ primitive policy invalid op

noncomputable def external (policy : Policy.{u}) (invalid : SequencePolicy.{u}) :
    ExternalInterpretation Value.{u} signature :=
  fun id arity => interpret policy invalid arity (operatorAt id)

end
end Silmaril.Logic.Temporal.TLA.DataElab.Sequences

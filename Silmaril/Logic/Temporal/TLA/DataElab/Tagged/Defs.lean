module

public import Silmaril.Logic.Temporal.TLA.DataElab.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Scalars.Thms

/-! Tagged value interpretations for DataElab and the numeric source fragment. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Tagged

open Resolution Data.Tagged

universe u

@[expose] public section

inductive SetOperation where
  | separation | image
  deriving DecidableEq, Repr

/-- Fix these policies across all valuations. For an unrecognized set bound,
`invalidSet` receives the operation and bound. The choice policy separately
supplies a value when a predicate has no witness. -/
structure Policy where
  numeric : Unspecified.{u}
  invalidSet : SetOperation → Value.{u} → Value.{u}
  invalidBoolean : BooleanContext → List Value.{u} → Value.{u}
  choice : Data.ChoicePolicy Value.{u}

/-- Reuse the tagged set operations on recognized bounds. -/
noncomputable def Policy.operations (policy : Policy.{u}) : DataOperations Value.{u} where
  numeral := fun n => Value.integer (Int.ofNat n)
  mem := Value.mem
  enum := fun values => Value.set (SetData.enum values)
  sep := fun bound p =>
    match bound.asSet with
    | some s => Value.set (s.sep p)
    | none => policy.invalidSet .separation bound
  image := fun bound f =>
    match bound.asSet with
    | some s => Value.set (s.image f)
    | none => policy.invalidSet .image bound
  choice := policy.choice

/-- Use tagged TRUE and FALSE and equality to tagged TRUE in predicate positions. -/
def Policy.booleans (policy : Policy.{u}) : Booleans Value.{u} where
  trueValue := Value.boolean true
  falseValue := Value.boolean false
  holds := Value.isTrue
  holds_true := rfl
  not_holds_false := fun h => Bool.false_ne_true ((Value.isTrue_boolean false).mp h)
  invalid := policy.invalidBoolean

inductive NumericPrimitive where
  | interval | add | sub | modulo | le | lt | naturals | integers
  deriving DecidableEq, Repr

def NumericPrimitive.arity : NumericPrimitive → Nat
  | .naturals | .integers => 0
  | .interval | .add | .sub | .modulo | .le | .lt => 2

/-- The caller selects the admitted declarations by resolved identity. -/
def numericSignature (table : BindingId → Option NumericPrimitive) : ExternalSignature :=
  fun id => (table id).map NumericPrimitive.arity

end

private def integerBinary (run : Value.{u} → Value.{u} → Value.{u})
    (law : Int → Int → Value.{u} → Prop)
    (sound : ∀ a b, law a b (run (Value.integer a) (Value.integer b))) :
    Primitive Value.{u} 2 where
  apply
    | [a, b] => run a b
    | _ => Value.set SetData.empty
  spec args result := ∀ a b, args = [Value.integer a, Value.integer b] → law a b result
  sound := by
    intro args _ a b h
    cases h
    exact sound a b

private def constant (value : Value.{u}) : Primitive Value.{u} 0 where
  apply := fun _ => value
  spec := fun _ result => result = value
  sound := fun _ _ => rfl

public section

/-- Reuse the tagged operators and their integer contracts. Checked calls
supply exactly the indicated arity. The modulo equation assumes a positive
divisor. -/
noncomputable def Policy.primitive (policy : Policy.{u}) :
    (op : NumericPrimitive) → Primitive Value.{u} op.arity
  | .interval => integerBinary (Value.interval policy.numeric)
      (fun lo hi result => result = Value.set (SetData.intRange lo hi))
      (Value.interval_integer policy.numeric)
  | .add => integerBinary (Value.add policy.numeric)
      (fun a b result => result = Value.integer (a + b)) (Value.add_integer policy.numeric)
  | .sub => integerBinary (Value.sub policy.numeric)
      (fun a b result => result = Value.integer (a - b)) (Value.sub_integer policy.numeric)
  | .modulo => integerBinary (Value.modulo policy.numeric)
      (fun a b result => 0 < b → result = Value.integer (a % b)) (Value.modulo_integer policy.numeric)
  | .le => integerBinary (Value.le policy.numeric)
      (fun a b result => result = Value.ofProp (a ≤ b)) (Value.le_integer policy.numeric)
  | .lt => integerBinary (Value.lt policy.numeric)
      (fun a b result => result.isTrue ↔ a < b) (Value.lt_integer policy.numeric)
  | .naturals => constant (Value.set SetData.naturals)
  | .integers => constant (Value.set SetData.integers)

private noncomputable def interpretNumeric (policy : Policy.{u}) (arity : Nat) :
    (op : Option NumericPrimitive) →
      op.map NumericPrimitive.arity = some arity → Primitive Value.{u} arity
  | none, admitted => by simp at admitted
  | some op, admitted => (Option.some.inj admitted) ▸ policy.primitive op

/-- Interpret exactly the IDs selected by the caller's table. Lowering still
checks the resolved declaration's kind and slots before reaching this table. -/
noncomputable def Policy.external (policy : Policy.{u})
    (table : BindingId → Option NumericPrimitive) :
    ExternalInterpretation Value.{u} (numericSignature table) :=
  fun id arity => interpretNumeric policy arity (table id)

end

end Silmaril.Logic.Temporal.TLA.DataElab.Tagged

module

public import Silmaril.Languages.Python.Core.Closure.Call.Defs

/-! # Prepare and bind checked variadic positional calls

The frontend supplies only ordinary operands and starred operands in the
closure value profile. This interface carries the state reached by each
operand read, including a failed read. A separate frame binder consumes
the fully evaluated positional list.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Core.Closure.Call

inductive PositionalOperand (Operand : Type) where
  | single (operand : Operand)
  | starred (operand : Operand)

inductive PositionalInputFailure where
  | operand (failure : Failure)
  | notIterable
  deriving DecidableEq, Repr

/-- A checked operand can update the caller state, including on failure. -/
abbrev ReadOperand (Operand State : Type) := Operand → State → Except Failure Value × State

/-- The closure profile has scalar tuples and the known noniterable
values None, integers, Booleans and plain functions. Other Python
iterables require a frontend and value profile that represent them. -/
def expandPositional : Value → Except PositionalInputFailure (List Value)
  | .tuple items => .ok (items.map Value.ofScalar)
  | .none | .int _ | .bool _ | .function _ => .error .notIterable

def PositionalOperand.evaluate {Operand State : Type} (read : ReadOperand Operand State)
    (part : PositionalOperand Operand) (state : State) :
    Except PositionalInputFailure (List Value) × State :=
  match part with
  | .single operand =>
    let (result, reached) := read operand state
    ((result.map (fun value => [value])).mapError .operand, reached)
  | .starred operand =>
    let (result, reached) := read operand state
    ((result.mapError .operand).bind expandPositional, reached)

def collectPositionals {Operand State : Type} (read : ReadOperand Operand State) :
    List (PositionalOperand Operand) → State → Except PositionalInputFailure (List Value) × State
  | [], state => (.ok [], state)
  | part :: rest, state =>
    let (head, reached) := part.evaluate read state
    match head with
    | .error failure => (.error failure, reached)
    | .ok values =>
      let (tail, final) := collectPositionals read rest reached
      (tail.map (values ++ ·), final)

/-- The next operand reads exactly the state reached by the previous
part. A failed part contributes its state and has no tail premise. -/
inductive CollectsPositionals {Operand State : Type} (read : ReadOperand Operand State) :
    List (PositionalOperand Operand) → State → Except PositionalInputFailure (List Value) × State → Prop where
  | nil (state : State) : CollectsPositionals read [] state (.ok [], state)
  | stop {head tail state reached failure}
      (evaluated : head.evaluate read state = (.error failure, reached)) :
      CollectsPositionals read (head :: tail) state (.error failure, reached)
  | next {head tail state reached final values result}
      (evaluated : head.evaluate read state = (.ok values, reached))
      (remaining : CollectsPositionals read tail reached (result, final)) :
      CollectsPositionals read (head :: tail) state (result.map (values ++ ·), final)

/-- Resolve the current callee before reading any operands. Dispatch and
arity checks receive the resulting descriptor and the completed list. -/
def preparePositionalCall {Operand State : Type} (read : ReadOperand Operand State) (callee : Operand)
    (arguments : List (PositionalOperand Operand)) (state : State) :
    Except PositionalInputFailure (Value × List Value) × State :=
  let (selected, reached) := read callee state
  match selected with
  | .error failure => (.error (.operand failure), reached)
  | .ok value =>
    let (supplied, final) := collectPositionals read arguments reached
    (supplied.map (value, ·), final)

/-- The variadic tuple uses an ordinary local or owned cell, distinct
from the fixed positional destinations. -/
structure VariadicParameters (layout : Layout) where
  fixed : Parameters layout
  rest : ParameterSlot layout
  restDistinct : rest ∉ fixed.slots

namespace VariadicParameters

variable {layout : Layout}

/-- Appending the rest slot lets the existing positional binder perform
all frame and heap writes, in declaration order. -/
def destinations (parameters : VariadicParameters layout) : Parameters layout :=
  ⟨parameters.fixed.slots ++ [parameters.rest],
    List.nodup_append.mpr ⟨parameters.fixed.distinct, by simp,
      fun _ present _ tail equal =>
        parameters.restDistinct ((equal.trans (List.mem_singleton.mp tail)) ▸ present)⟩⟩

/-- Recover a fixed prefix and its distinct final rest slot from the
checked declaration-order destinations. -/
def ofDestinations (parameters : Parameters layout) :
    Option { signature : VariadicParameters layout // signature.destinations = parameters } := do
  match found : parameters.slots.getLast? with
  | none => none
  | some rest =>
    have split : parameters.slots.dropLast ++ [rest] = parameters.slots := by
      obtain ⟨prefixSlots, exactSlots⟩ := List.getLast?_eq_some_iff.mp found
      simp [exactSlots]
    have distinct := List.nodup_append.mp (split.symm ▸ parameters.distinct :
      (parameters.slots.dropLast ++ [rest]).Nodup)
    let signature : VariadicParameters layout :=
      ⟨⟨parameters.slots.dropLast, distinct.1⟩, rest, fun present => distinct.2.2 rest present rest (by simp) rfl⟩
    return ⟨signature, by
      cases parameters
      simp only [destinations, signature, Parameters.mk.injEq]
      exact split⟩

/-- The fixed prefix is copied as supplied. The overflow list is stored as
one exact scalar tuple, including the empty tuple. -/
def complete (parameters : VariadicParameters layout) (supplied : List Value) :
    Except Failure (List Value) :=
  let count := parameters.fixed.slots.length
  if supplied.length < count then
    .error (.defined (.positionalArity count supplied.length))
  else
    match (supplied.drop count).mapM Value.scalar? with
    | none => .error .unsupportedTupleElement
    | some rest => .ok (supplied.take count ++ [.tuple rest])

def bind (parameters : VariadicParameters layout) (supplied : List Value)
    (before : Environment layout) : Except Failure (Environment layout) :=
  (parameters.complete supplied).bind fun values => bindPositional parameters.destinations values before

/-- The caller and its reached heap enter by the existing closure
protocol, after capture validation and successful collection. -/
def enter {Continuation : Layout → Type} (fn : Function)
    (parameters : VariadicParameters fn.code.layout) (supplied : List Value) (heap : Heap)
    (caller : Saved Continuation) (stack : List (Saved Continuation)) :
    Except Failure (Entered Continuation fn.code.layout) :=
  match firstDangling fn heap with
  | some identity => .error (.danglingCell identity)
  | none =>
    (parameters.complete supplied).bind fun values =>
      Call.enter fn parameters.destinations values heap caller stack

end VariadicParameters
end Silmaril.Languages.Python.Core.Closure.Call

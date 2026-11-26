module

public import Silmaril.Languages.Python.Core.Closure.Defs
public import Silmaril.Languages.Python.Core.Module.ListObject.Defs

/-! # Closed callables for explicitly seeded module entry -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module.SeededCall

open Core.Closure (RuntimeError)

inductive ExceptionClass where
  | assertionError
  | nameError
  | unboundLocalError
  | typeError
  | zeroDivisionError
  deriving DecidableEq, Repr

inductive AssertionArgument where
  | empty
  | text (message : String)
  | integerPair (left right : Int)
  | booleanPair (left right : Bool)
  deriving DecidableEq, Repr

inductive Raised where
  | assertionError (argument : AssertionArgument)
  | runtime (error : RuntimeError)
  deriving DecidableEq, Repr

def Raised.classify : Raised → ExceptionClass
  | .assertionError _ | .runtime .assertionError => .assertionError
  | .runtime (.unboundLocal _) | .runtime (.unboundOwned _) => .unboundLocalError
  | .runtime (.unboundCapture _) | .runtime (.nameError _) => .nameError
  | .runtime (.positionalArity ..) | .runtime .notCallable | .runtime .additionTypeError
  | .runtime .multiplicationTypeError | .runtime .unpackNonIterable => .typeError
  | .runtime (.arithmetic .zeroDivisionError) => .zeroDivisionError

def ExceptionClass.catches (expected actual : ExceptionClass) : Prop :=
  expected = actual ∨ (expected = .nameError ∧ actual = .unboundLocalError)

instance (expected actual : ExceptionClass) : Decidable (expected.catches actual) := by
  unfold ExceptionClass.catches
  infer_instance

inductive Helper where
  | assertEqual
  | assertIs
  | assertIsNot
  | assertRaises (onReturn : AssertionArgument)
  deriving DecidableEq, Repr

inductive Builtin where
  | int
  | bool
  | callable
  | len
  | list
  | tuple
  | isinstance
  deriving DecidableEq, Repr

inductive Value where
  | int (value : Int)
  | bool (value : Bool)
  | none
  | listObject (object : Core.Module.ListObject)
  | returnedTuple (items : List Core.Module.Value)
  | exceptionClass (kind : ExceptionClass)
  | helper (descriptor : Helper)
  | builtin (descriptor : Builtin)
  | function (closure : Core.Closure.Function)
  deriving DecidableEq, Repr

inductive Failure where
  | raised (error : Raised)
  | unsupported
  deriving DecidableEq, Repr

abbrev Result := Except Failure Value
abbrev Bindings := List (String × Value)

def lookupBinding (bindings : Bindings) (name : String) : Option Value :=
  bindings.findSome? fun (key, value) => if name = key then some value else none

structure Namespace where
  moduleGlobals : Bindings
  builtins : Bindings

def Namespace.empty : Namespace := ⟨[], []⟩

/-- Global reads look in the module first. A present `None` is a binding. -/
def Namespace.lookupGlobal (space : Namespace) (name : String) : Option Value :=
  (lookupBinding space.moduleGlobals name).orElse (fun _ => lookupBinding space.builtins name)

def Namespace.bindGlobal (space : Namespace) (name : String) (value : Value) : Namespace :=
  { space with moduleGlobals := (name, value) :: space.moduleGlobals.filter (fun binding => binding.1 != name) }

/-- Lexical resolution makes the local/global choice before execution. -/
inductive Operand (slots : Nat) where
  | literal (value : Value)
  | local (slot : Fin slots)
  | global (name : String)
  | unsupported

abbrev Locals (slots : Nat) := Vector (Option Value) slots

def Operand.eval {slots : Nat} (space : Namespace) (locals : Locals slots) : Operand slots → Result
  | .literal value => .ok value
  | .local slot =>
    (locals.get slot).elim (.error (.raised (.runtime (.unboundLocal slot.val)))) .ok
  | .global name =>
    (space.lookupGlobal name).elim (.error (.raised (.runtime (.nameError name)))) .ok
  | .unsupported => .error .unsupported

structure Expectation where
  expected : ExceptionClass
  onReturn : AssertionArgument

def Expectation.deliver (expectation : Expectation) : Result → Result
  | .ok _ => .error (.raised (.assertionError expectation.onReturn))
  | .error (.raised error) =>
    if expectation.expected.catches error.classify then .ok .none else .error (.raised error)
  | .error .unsupported => .error .unsupported

inductive Delivers (expectation : Expectation) : Result → Result → Prop where
  | returned (value : Value) : Delivers expectation (.ok value)
      (.error (.raised (.assertionError expectation.onReturn)))
  | caught (error : Raised) (accepted : expectation.expected.catches error.classify) :
      Delivers expectation (.error (.raised error)) (.ok .none)
  | uncaught (error : Raised) (different : ¬ expectation.expected.catches error.classify) :
      Delivers expectation (.error (.raised error)) (.error (.raised error))
  | unsupported : Delivers expectation (.error .unsupported) (.error .unsupported)

/-- Exact Booleans refer to the two canonical Python singleton objects. -/
inductive BoolIdentity where
  | falseObject
  | trueObject
  deriving DecidableEq

def BoolIdentity.ofBool : Bool → BoolIdentity
  | false => .falseObject
  | true => .trueObject

/-- Only the stock `len` object and exact integers are probed. -/
inductive CallableProbe where
  | len
  | integer

def CallableProbe.result : CallableProbe → Bool
  | .len => true
  | .integer => false

/-- The three value and stock type pairs used by the restricted instance check. -/
inductive InstanceProbe where
  | boolAgainstBool
  | boolAgainstInt
  | intAgainstBool

def InstanceProbe.result : InstanceProbe → Bool
  | .boolAgainstBool | .boolAgainstInt => true
  | .intAgainstBool => false

/-- Decoding identifies the admitted typed call shapes. In particular,
calling an exception class would construct an object outside this profile. -/
inductive Request (arity : Nat) where
  | compare (left right : Int)
  | intFromBool (value : Bool)
  | callable (probe : CallableProbe)
  | isinstance (probe : InstanceProbe)
  | boolIdentity (left right : Bool)
  | distinctIntBool
  | expect (expectation : Expectation) (callback : Value) (arguments : List Value)
      (shorter : arguments.length < arity)
  | nonCallable
  | unsupported

def Request.decode (callee : Value) (arguments : List Value) : Request arguments.length :=
  match callee, arguments with
  | .helper .assertEqual, [.int left, .int right] => .compare left right
  | .builtin .int, [.bool value] => .intFromBool value
  | .builtin .callable, [.builtin .len] => .callable .len
  | .builtin .callable, [.int _] => .callable .integer
  | .builtin .isinstance, [.bool _, .builtin .bool] => .isinstance .boolAgainstBool
  | .builtin .isinstance, [.bool _, .builtin .int] => .isinstance .boolAgainstInt
  | .builtin .isinstance, [.int _, .builtin .bool] => .isinstance .intAgainstBool
  | .helper .assertIs, [.bool left, .bool right] => .boolIdentity left right
  | .helper .assertIsNot, [.int _, .bool _] | .helper .assertIsNot, [.bool _, .int _] => .distinctIntBool
  | .helper (.assertRaises onReturn), .exceptionClass expected :: callback :: arguments =>
    .expect ⟨expected, onReturn⟩ callback arguments (by simp only [List.length_cons]; omega)
  | .none, _ | .int _, _ | .bool _, _ | .listObject _, _ | .returnedTuple _, _ => .nonCallable
  | _, _ => .unsupported

/-- Invoking an expectation calls the supplied closed callable using the
same dispatcher as a direct call. -/
def invoke (callee : Value) (arguments : List Value) : Result :=
  match Request.decode callee arguments with
  | .compare left right =>
    if left = right then .ok .none else .error (.raised (.assertionError (.integerPair left right)))
  | .intFromBool value => .ok (.int (Int.ofNat value.toNat))
  | .callable probe => .ok (.bool probe.result)
  | .isinstance probe => .ok (.bool probe.result)
  | .boolIdentity left right =>
    if BoolIdentity.ofBool left = BoolIdentity.ofBool right then .ok .none
    else .error (.raised (.assertionError (.booleanPair left right)))
  | .distinctIntBool => .ok .none
  | .expect expectation callback args _shorter =>
    expectation.deliver (invoke callback args)
  | .nonCallable => .error (.raised (.runtime .notCallable))
  | .unsupported => .error .unsupported
termination_by arguments.length

inductive Executes : {arity : Nat} → Request arity → Result → Prop where
  | equal {arity : Nat} (left right : Int) (same : left = right) :
      Executes (arity := arity) (.compare left right) (.ok .none)
  | unequal {arity : Nat} (left right : Int) (different : left ≠ right) :
      Executes (arity := arity) (.compare left right) (.error (.raised (.assertionError (.integerPair left right))))
  | intFromBool {arity : Nat} (value : Bool) :
      Executes (arity := arity) (.intFromBool value) (.ok (.int (Int.ofNat value.toNat)))
  | callable {arity : Nat} (probe : CallableProbe) :
      Executes (arity := arity) (.callable probe) (.ok (.bool probe.result))
  | isinstance {arity : Nat} (probe : InstanceProbe) :
      Executes (arity := arity) (.isinstance probe) (.ok (.bool probe.result))
  | sameBool {arity : Nat} (left right : Bool)
      (same : BoolIdentity.ofBool left = BoolIdentity.ofBool right) :
      Executes (arity := arity) (.boolIdentity left right) (.ok .none)
  | distinctBool {arity : Nat} (left right : Bool)
      (different : BoolIdentity.ofBool left ≠ BoolIdentity.ofBool right) :
      Executes (arity := arity) (.boolIdentity left right)
        (.error (.raised (.assertionError (.booleanPair left right))))
  | distinctIntBool {arity : Nat} : Executes (arity := arity) .distinctIntBool (.ok .none)
  | expected {arity : Nat} {expectation : Expectation} {callback : Value} {arguments : List Value}
      {shorter : arguments.length < arity} {inner outer : Result} :
      Executes (Request.decode callback arguments) inner → Delivers expectation inner outer →
      Executes (.expect expectation callback arguments shorter) outer
  | nonCallable {arity : Nat} : Executes (arity := arity) .nonCallable (.error (.raised (.runtime .notCallable)))
  | unsupported {arity : Nat} : Executes (arity := arity) .unsupported (.error .unsupported)

def Operand.evalList {slots : Nat} (space : Namespace) (locals : Locals slots) :
    List (Operand slots) → Except Failure (List Value)
  | [] => .ok []
  | operand :: rest =>
    (operand.eval space locals).bind fun value => (evalList space locals rest).map (value :: ·)

def resolveCall {slots : Nat} (space : Namespace) (locals : Locals slots)
    (callee : Operand slots) (arguments : List (Operand slots)) :
    Except Failure (Value × List Value) :=
  (callee.eval space locals).bind fun function =>
    (Operand.evalList space locals arguments).map (function, ·)

/-- Resolve the callable, then resolve positional operands in order. Calls
and their supported callback do not write either namespace. -/
def run {slots : Nat} (space : Namespace) (locals : Locals slots)
    (callee : Operand slots) (arguments : List (Operand slots)) : Result :=
  (resolveCall space locals callee arguments).bind fun (function, values) => invoke function values

end Silmaril.Languages.Python.Core.Module.SeededCall

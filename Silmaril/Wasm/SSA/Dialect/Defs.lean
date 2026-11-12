module

public import Silmaril.Wasm.SSA.Fragment.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Defs

/-!
# The Wasm dialect of lambda-SSA

Lambda-SSA (`Silmaril.Isotope.LambdaSSA`) instantiated with Wasm integer values
as atoms and three kinds of primitive:

* `Prim.op o` applies a value operator to a tuple of atoms and returns its
  result atom. It is used for operators that cannot trap; a trap of `o` has
  no transition (stuck).
* `Prim.opT o` is the trapping form: `inl result` or `inr ()` on a trap. The
  translation cases on it, sending `inr` to the trap exit.
* `Prim.truthy` tests an `i32` condition, returning `inl ()` (non-zero) or
  `inr ()` (zero).

Arguments are right-nested tuples of atoms ending in `()` (`encodeList`).
The instruction state is `Unit`: the fragment has no memory, so every
primitive is a pure, deterministic partial function (`Prim.run`).

An SSA function (`SFunc`) is a region whose free variables are the
parameters (parameter `i` of `p` is variable `p - 1 - i`). It leaves through
external label `0` (return, with `()` or the result atom) or `1` (trap).
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm (IntType)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)

/-- Primitive instructions of the dialect. -/
inductive Prim where
  | op (o : Op)
  | opT (o : Op)
  | truthy
  deriving DecidableEq, Repr

/-- Dialect values. -/
abbrev SVal := Value WVal

/-- A list of atoms as a right-nested tuple ending in `()`. -/
def encodeList : List WVal → SVal
  | [] => .unit
  | a :: as => .pair (.atom a) (encodeList as)

/-- Read back a tuple of atoms. -/
def decodeList : SVal → Option (List WVal)
  | .unit => some []
  | .pair (.atom a) r => (decodeList r).map (a :: ·)
  | _ => none

/-- Run a primitive. -/
def Prim.run : Prim → SVal → Option SVal
  | .op o, v =>
      match (decodeList v).bind o.eval with
      | some (.val w) => some (.atom w)
      | _ => none
  | .opT o, v =>
      match (decodeList v).bind o.eval with
      | some (.val w) => some (.inl (.atom w))
      | some .trap => some (.inr .unit)
      | none => none
  | .truthy, .atom w => w.truthy.map fun b => if b then .inl .unit else .inr .unit
  | .truthy, _ => none

/-- The instruction relation the lambda-SSA semantics is run with. -/
def instr (p : Prim) (v : SVal) (_ : Unit) (v' : SVal) (_ : Unit) : Prop :=
  p.run v = some v'

/-- An SSA function. -/
structure SFunc where
  params : List IntType
  result : Option IntType
  body : Region Prim

/-- The environment of a call: parameter `i` of `p` is variable `p - 1 - i`. -/
def argEnv (args : List WVal) : Silmaril.Isotope.LambdaSSA.Semantics.Env WVal :=
  fun j => match args.reverse[j]? with
    | some a => .atom a
    | none => .unit

/-- The call outcome of an exit: label `0` returns, label `1` traps. -/
def decodeOut : Nat → SVal → Option FOut
  | 0, .unit => some (.ret none)
  | 0, .atom w => some (.ret (some w))
  | 1, .unit => some .trap
  | _, _ => none

/-- Terminating runs of an SSA function, on arguments of the parameter types. -/
def SFunc.Run (f : SFunc) (args : List WVal) (o : FOut) : Prop :=
  args.map WVal.type = f.params ∧
    ∃ l v, Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval instr (argEnv args) f.body () l v () ∧
      decodeOut l v = some o

end Silmaril.Wasm.SSA

module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Defs
public import Silmaril.Machine.OfLambdaSSA.Defs
/-! Sound abstract information and an explicit typed pure total fragment for the
actual lambda-SSA arithmetic folding traversal. These predicates constrain
syntax and input environments; none requires a successful execution. -/
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Machine.RTL (Opcode CallOracle packValues)
open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.Lir (Word)

/-- Pure total opcodes actually admitted by the native arithmetic adapter. -/
def ArithmeticOpcode : Old.Opcode → Prop
  | .const _ | .move | .unary _ => True
  | .binary op => (newBinary op).isSome = true
  | _ => False

/-- The abstract analysis describes only components it knows. -/
def Models : Abstract → Value Word → Prop
  | .unknown, _ => True
  | .word w, value => value = .atom w
  | .unit, value => value = .unit
  | .pair left right, value => ∃ a b, value = .pair a b ∧ Models left a ∧ Models right b

/-- Unlisted variables may contain arbitrary values. -/
def EnvironmentModels (known : List Abstract) (env : Semantics.Env Word) : Prop :=
  ∀ index, Models (known.getD index .unknown) (env index)

/-- Each declared variable has its existing RTL fragment shape. -/
def ShapeEnvironment (context : List Shape) (env : Semantics.Env Word) : Prop :=
  ∀ (index : Nat) (shape : Shape), context[index]? = some shape → ∃ words, shape.Holds (env index) words


end Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding

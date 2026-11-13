module

public import Silmaril.Compiler.Native.Correctness.AdditionFocused.Thms
public import Silmaril.Compiler.Core.ReturnControl.Thms
public import Silmaril.Compiler.Native.Correctness.Institution.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionMain
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Native.Correctness.AdditionSource
open Construction

/-- Actual function-level saved return label from the proved Functions output. -/
def savedReturn : Effect :=
  Functions.returnSave (some (Literal42.sym 1 "main")) (Literal42.sym 1 "main") returnLabel
    (fresh 107) .unknown intType (.loaded .integer)

/-- Actual procedure body in the elaborated file, including the saved return. -/
def procedureBody (left right : Int) : Effect :=
  strongSequence (wildcard .unit) (coreBody left right) savedReturn

abbrev semanticFile (left right : Int) := (bindings left right).toFile

/-- The enum transport document of the independently fixed source. -/
def sourceDocument (left right : Int) := document (source left right) (bindings left right)

def expectedExit (left right : Int) : Silmaril.Compile.Core.Spec.Obs :=
  .exit ((left + right) % 256).toNat []

def specification (left right : Int) : Set Observation :=
  {observation | observe observation = expectedExit left right}

end Silmaril.Compiler.Native.Correctness.AdditionMain

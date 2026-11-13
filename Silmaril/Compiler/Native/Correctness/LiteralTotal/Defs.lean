module

public import Silmaril.Compiler.Native.Correctness.Literal.Defs
public import Silmaril.Compiler.Core.ElaborationTotal.Defs
/-! A checked literal input domain for the native source institution. Its
predicate inspects source syntax, freshness, integer bounds and runtime syntax;
no successful elaboration or behavior is assumed. It states no native validity.
-/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralTotal
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Core.ElaborationProcess
open Construction

/-- The completed process result specified by a signed integer main return. -/
def expectedExit (number : Int) : Silmaril.Compile.Core.Spec.Obs :=
  .exit (number % 256).toNat []

/-- A sentence in the existing projected native source institution. It fixes
only the observed return status and empty output, not a concrete native state. -/
def specification (number : Int) : Set Observation :=
  {observation | observe observation = expectedExit number}

/-- The actual literal-main syntax and explicit inputs accepted by the universal
Core theorem. Runtime recognition checks the assembled semantic file's syntax,
including the conversion callees. It does not inspect execution or native output.
Target/runtime adequacy for C and agreement with System V remain separate. -/
def domain (number : Int) (source : Source) : Prop :=
  ∃ literal : LiteralMain,
    literal.number = number ∧ source.program = literal.program ∧
    source.elaboration.freshness.next + 2 ≤ source.elaboration.freshness.maximum ∧
    Silmaril.Compile.Core.Verified.ConvInt.IsInt literal.number ∧
    ∃ (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure),
      Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1)
        source.elaboration.runtime.stdlib = some (conversion, .function resultType parameters body) ∧
      Silmaril.Compile.Core.Verified.ConvInt.isConvLoadedInt
        (literal.bindings source.elaboration.runtime source.elaboration.freshness conversion).toFile
        conversion = true

end Silmaril.Compiler.Native.Correctness.LiteralTotal

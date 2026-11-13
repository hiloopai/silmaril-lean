module

public import Silmaril.Compiler.Native.Correctness.Defs
public import Silmaril.Compiler.Core.ElaborationProcess.Defs
/-! A syntactic domain for actual elaboration coverage. This domain checks
source shape, freshness availability and first-match runtime syntax, never an
elaboration result or native compiler output. Runtime semantic adequacy and
agreement with native System V remain additional obligations; this is not a
claimed native machine-refinement domain. -/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.Literal
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Silmaril.Compiler.Core.ElaborationProcess
open Construction

/-- Actual zero-argument signed-int literal-main syntax with sufficient fresh
indices and the runtime lookup needed by Functions.elaborate. The signed-int
range is stated independently of the elaborator's acceptance. No expected Core
body, accepted output or source/native agreement is assumed. -/
def elaborationDomain (source : Source) : Prop :=
  ∃ literal : LiteralMain,
    source.program = literal.program ∧
    source.elaboration.freshness.next + 2 ≤ source.elaboration.freshness.maximum ∧
    Silmaril.Compile.Core.Verified.ConvInt.IsInt literal.number ∧
    ∃ (conversion : Sym) (resultType : BaseType) (parameters : List (Sym × BaseType)) (body : Pure),
      Runtime.firstMatching (fun binding => Runtime.hasName "conv_loaded_int" binding.1)
        source.elaboration.runtime.stdlib = some (conversion, .function resultType parameters body)

end Silmaril.Compiler.Native.Correctness.Literal

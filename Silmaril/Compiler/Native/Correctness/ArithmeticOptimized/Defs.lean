module

public import Silmaril.Compiler.Native.Correctness.ArithmeticInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.Open.Cleanup.Defs
/-! Actual optimizeWith after independently bounded recursive arithmetic lowering.
Every real stage gate, including enabled LambdaSSA selection, remains intact.
This interprets the resulting Artifact under explicit native OpenFrame meanings. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.ArithmeticOptimized
open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Compiler.Native.Semantics Silmaril.Compiler.Native.Optimize

/-- The exact singleton optimizer/extraction used before native emission. -/
def optimizeArtifact (cfg : Config) (input : Artifact) : Artifact :=
  { input with mir := (optimizeWith cfg #[input.mir])[0]! }

def artifact (cfg : Config) (expression : Expression) : Artifact :=
  optimizeArtifact cfg (ArithmeticLower.artifact expression)

def invocation (cfg : Config) (expression : Expression) (memory : Lir.Memory) : OpenFrame.Invocation :=
  { ArithmeticOpenFrame.invocation expression memory with
    function := Open.Cleanup.optimizeFunc cfg (ArithmeticLower.function expression) }

def target (cfg : Config) (program : ArithmeticInstitution.Program) : ArithmeticInstitution.Target :=
  { ArithmeticInstitution.expected program with
    artifact := artifact cfg program.expression }

/-- Actual unoptimized lowering followed by actual optimizeWith and singleton
extraction. Lowering errors remain errors; no guard or replacement is added. -/
def run (context : ArithmeticInstitution.Context) (cfg : Config) (program : ArithmeticInstitution.Program) :
    Option ArithmeticInstitution.Target :=
  (ArithmeticInstitution.run context program).map fun output =>
    { output with artifact := optimizeArtifact cfg output.artifact }

namespace Hets
/-- The same independent source/target logic endpoints, at the actual optimized model. -/
def optimizedPath (context : ArithmeticInstitution.Context) := ArithmeticInstitution.Hets.loweringPath context
end Hets
end Silmaril.Compiler.Native.Correctness.ArithmeticOptimized

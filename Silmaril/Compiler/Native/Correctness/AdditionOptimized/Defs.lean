module

public import Silmaril.Compiler.Native.Correctness.AdditionVersioned.Defs
public import Silmaril.Compiler.Native.Optimize.Open.Cleanup.Defs
/-! Actual optimizeWith after independently bounded addition lowering.
Every real stage gate, including enabled LambdaSSA selection, remains intact.
This interprets the resulting Artifact under explicit native OpenFrame meanings. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionOptimized
open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics Silmaril.Compiler.Native.Optimize

/-- The exact singleton optimizer/extraction used before native emission. -/
def optimizeArtifact (cfg : Config) (input : Artifact) : Artifact :=
  { input with mir := (optimizeWith cfg #[input.mir])[0]! }

def artifact (cfg : Config) (left right : Lir.Word) : Artifact :=
  optimizeArtifact cfg (AdditionLower.artifact left right)

def invocation (cfg : Config) (left right : Lir.Word) (memory : Lir.Memory) : OpenFrame.Invocation :=
  { AdditionOpenFrame.invocation left right memory with
    function := Open.Cleanup.optimizeFunc cfg (AdditionLower.function left right) }

def target (cfg : Config) (program : AdditionInstitution.Program) : AdditionInstitution.Target :=
  { AdditionInstitution.expected program with
    artifact := artifact cfg (BitVec.ofInt 64 program.left) (BitVec.ofInt 64 program.right) }

/-- Actual unoptimized lowering followed by actual optimizeWith and singleton
extraction. Lowering errors remain errors; no guard or replacement is added. -/
def run (context : AdditionInstitution.Context) (cfg : Config) (program : AdditionInstitution.Program) :
    Option AdditionInstitution.Target :=
  (AdditionInstitution.run context program).map fun output =>
    { output with artifact := optimizeArtifact cfg output.artifact }

namespace Hets
/-- The same independent source/target logic endpoints, at the actual optimized model. -/
def optimizedPath (context : AdditionInstitution.Context) := AdditionInstitution.Hets.loweringPath context
end Hets
end Silmaril.Compiler.Native.Correctness.AdditionOptimized

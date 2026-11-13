module

public import Silmaril.Compiler.Native.Correctness.AdditionInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Caller.Defs
/-! Actual local SSA versioning of bounded-addition native Artifacts.
This applies the existing versionFunc and retains all native metadata.
Cleanup passes, full optimization and machine/ABI refinement are separate. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionVersioned

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics Silmaril.Compiler.Native.Optimize

def versionArtifact (cfg : Config) (artifact : Artifact) : Artifact :=
  { artifact with mir := { artifact.mir with funcs := artifact.mir.funcs.map (versionFunc cfg) } }

def artifact (cfg : Config) (left right : Lir.Word) : Artifact :=
  versionArtifact cfg (AdditionLower.artifact left right)

def invocation (cfg : Config) (left right : Lir.Word) (memory : Lir.Memory) : OpenFrame.Invocation :=
  { AdditionOpenFrame.invocation left right memory with
    function := versionFunc cfg (AdditionLower.function left right) }

def target (cfg : Config) (program : AdditionInstitution.Program) : AdditionInstitution.Target :=
  { AdditionInstitution.expected program with
    artifact := artifact cfg (BitVec.ofInt 64 program.left) (BitVec.ofInt 64 program.right) }

/-- Actual unoptimized lowering, followed by actual local SSA versioning.
This does not invoke the four cleanup passes or Native.Driver.compile. -/
def run (context : AdditionInstitution.Context) (cfg : Config) (program : AdditionInstitution.Program) :
    Option AdditionInstitution.Target :=
  (AdditionInstitution.run context program).map fun output =>
    { output with artifact := versionArtifact cfg output.artifact }

namespace Hets
def versionedPath (context : AdditionInstitution.Context) := AdditionInstitution.Hets.loweringPath context
end Hets

end Silmaril.Compiler.Native.Correctness.AdditionVersioned

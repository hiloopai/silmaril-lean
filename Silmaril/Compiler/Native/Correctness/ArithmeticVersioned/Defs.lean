module

public import Silmaril.Compiler.Native.Correctness.ArithmeticInstitution.Defs
public import Silmaril.Compiler.Native.Optimize.Defs
/-! Actual local SSA versioning of bounded recursive-arithmetic native Artifacts.
This applies the existing versionFunc and retains all native metadata.
Cleanup passes, full optimization and machine/ABI refinement are separate. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.ArithmeticVersioned

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Compiler.Native.Semantics Silmaril.Compiler.Native.Optimize

/-- Exact independently stated ordinary round-trip prologue. -/
def versionedPrologue (base : Nat) : Mir.Block :=
  ⟨#[.addr base "__ccomp_frame" 0, .op (.move 0 base)], .jump 1⟩

def versionArtifact (cfg : Config) (artifact : Artifact) : Artifact :=
  { artifact with mir := { artifact.mir with funcs := artifact.mir.funcs.map (versionFunc cfg) } }

def artifact (cfg : Config) (expression : Expression) : Artifact :=
  versionArtifact cfg (ArithmeticLower.artifact expression)

def invocation (cfg : Config) (expression : Expression) (memory : Lir.Memory) : OpenFrame.Invocation :=
  { ArithmeticOpenFrame.invocation expression memory with
    function := versionFunc cfg (ArithmeticLower.function expression) }

def target (cfg : Config) (program : ArithmeticInstitution.Program) : ArithmeticInstitution.Target :=
  { ArithmeticInstitution.expected program with
    artifact := artifact cfg program.expression }

/-- Actual unoptimized lowering, followed by actual local SSA versioning.
This does not invoke the four cleanup passes or Native.Driver.compile. -/
def run (context : ArithmeticInstitution.Context) (cfg : Config) (program : ArithmeticInstitution.Program) :
    Option ArithmeticInstitution.Target :=
  (ArithmeticInstitution.run context program).map fun output =>
    { output with artifact := versionArtifact cfg output.artifact }

namespace Hets
def versionedPath (context : ArithmeticInstitution.Context) := ArithmeticInstitution.Hets.loweringPath context
end Hets

end Silmaril.Compiler.Native.Correctness.ArithmeticVersioned

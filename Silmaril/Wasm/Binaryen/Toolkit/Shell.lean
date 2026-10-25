module

public import Silmaril.Wasm.Binaryen.Toolkit.ByteInput
public import Silmaril.Wasm.Binaryen.Behaviour
public import Silmaril.Wasm.SingleThreaded.Exec.CheckedRun
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.Execution.Core.Exec.ValCheck

@[expose] public section

/-! # Bounded execution of a named export

The checked interpreter validates, instantiates and executes the start function
before looking up and type-checking the requested invocation. Both runs have
the explicit step budget. Exhaustion is inconclusive, never a divergence claim.
The empty initial store and import list provide no ambient host capabilities.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core SingleThreaded SingleThreaded.Exec

inductive ShellPhase where
  | initialization
  | invocation
  deriving DecidableEq, Repr

inductive ShellFailure where
  | rejected (reason : String)
  | fuelExhausted (phase : ShellPhase)
  | initializationResult (result : Result)
  | unclassified (phase : ShellPhase)
  deriving DecidableEq, Repr

structure ShellArtifact where
  module : Wasm.Module
  initialized : Config Empty
  address : Nat
  final : Config Empty
  result : Result

/-- A completed, validated initialization. A trap or escaping exception is
reported separately; neither permits calling exports afterward. -/
def initializeForShell (o : GrowOracle) (budget : Nat) (m : Wasm.Module) :
    Except ShellFailure (Config Empty) :=
  match runChecked? o budget ({} : Store Empty) m [] with
  | none => .error (.rejected "validation, imports, or concrete initialization failed")
  | some (_, false, _) => .error (.fuelExhausted .initialization)
  | some (c, true, some (.values [])) => .ok c
  | some (_, true, some r) => .error (.initializationResult r)
  | some (_, true, none) => .error (.unclassified .initialization)

def resolveShellExport (initialized : Config Empty) (name : String) :
    Except ShellFailure Nat :=
  match exportFunc? initialized.frame.module name with
  | none => .error (.rejected "requested function export is absent")
  | some address => .ok address

/-- A successful artifact contains an actual classified terminal result. Failure
retains the difference between a rejected request and an exhausted budget. -/
def shellModule (o : GrowOracle) (budget : Nat) (name : String) (args : List Val)
    (m : Wasm.Module) : Except ShellFailure ShellArtifact := do
  let initialized ← initializeForShell o budget m
  let address ← resolveShellExport initialized name
  if invokeOk? initialized.store address args then
    match runInvoke? o budget initialized.store address args with
    | none => .error (.rejected "invocation setup failed")
    | some (_, false, _) => .error (.fuelExhausted .invocation)
    | some (final, true, some result) =>
        .ok ⟨m, initialized, address, final, result⟩
    | some (_, true, none) => .error (.unclassified .invocation)
  else .error (.rejected "argument types do not match the exported function")

def shellBytes (o : GrowOracle) (budget : Nat) (name : String) (args : List Val)
    (bytes : ByteArray) : Except ShellFailure ShellArtifact := do
  let m ← (decodeInput "module" bytes).mapError ShellFailure.rejected
  shellModule o budget name args m

end Silmaril.Wasm.Binaryen.Toolkit

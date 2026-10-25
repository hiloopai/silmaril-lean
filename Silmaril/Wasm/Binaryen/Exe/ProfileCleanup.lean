module

public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Binaryen.Exe.Fold
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binaryen.Exe.Pipeline

@[expose] public section

/-! # Byte-input cleanup without numerical determinism

This separate driver uses the specification decoder, validates the original
module, performs a lowering-preserving lift and runs the existing twelve-stage
cleanup. It retains every stage's applicability checks and identity fallbacks.
Unsupported decoding/encoding is an explicit error. The original optimizer and
its pipeline, scoring, defaults and options are unchanged.
-/

namespace Silmaril.Wasm.Binaryen.Exe

/-- Runtime-only realization of the twelve-stage pipeline. The checked-DCE
implementation is already shared with the original native optimizer. Proof-side
equality with `ArbitraryProfile.cleanupWithDirectize` is in the soundness module.
Do not import the proof packager here: its inlining/typing closure contains the
four-billion-local counterexample documented in `Exe/Pipeline.lean`. -/
def profileCleanupRound (m : BModule) : BModule :=
  let m := Dce.dceChecked m
  let m := VacuumLite.vacuumLite m
  let m := PrecomputeLite.precomputeLite m
  let m := SimplifyLocalsLite.teeDrop m
  let m := rume m
  let m := AddChain.addChainChecked m
  let m := ConstBranch.constBranchChecked m
  let m := IfSwap.ifSwapChecked m
  let m := ConstSelect.constSelectChecked m
  let m := invertGuardsChecked m
  let m := simplifyGlobals m
  directize m

structure ProfileCleanupArtifact where
  source : Module
  result : Module
  bytes : ByteArray

/-- The shared checked byte boundary for runtime-only module transforms.
Correctness certificates are supplied separately in the soundness module. -/
def cleanupTransformBytes (transform : BModule → BModule) (input : ByteArray) :
    Except String ProfileCleanupArtifact := do
  let source ← (Binary.Core.Decode.decodeModule input).mapError ("cleanup: " ++ ·)
  match Validation.validate? source with
  | none => .error "cleanup: module validation failed"
  | some _ =>
    let lifted := (checkedLift source).1
    let result := (transform lifted).lower
    let bytes ← encodeModule? result
    pure ⟨source, result, ⟨bytes.toArray⟩⟩

/-- A separate exact cleanup path. Its executable does not select a numerical
profile; the accepted-output theorem holds at every same profile on both sides.
Factoring the shared byte boundary changes no checks, transformations or output. -/
def cleanupBytes (rounds : Nat) (input : ByteArray) : Except String ProfileCleanupArtifact :=
  cleanupTransformBytes (profileCleanupRound^[rounds]) input

end Silmaril.Wasm.Binaryen.Exe

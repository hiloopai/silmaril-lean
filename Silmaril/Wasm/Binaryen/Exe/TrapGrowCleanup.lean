module

public import Silmaril.Wasm.Binaryen.Exe.ModeCleanup
public import Silmaril.Wasm.Binaryen.GrowOOMLiteralRuntime

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Optimization

/-- Add a new policy without changing `ModeCleanupOptions` or its constructor. -/
structure TrapGrowOptions where
  base : ModeCleanupOptions := {}
  trapGrowthFailure : Bool := false
  deriving Repr

def TrapGrowOptions.check (options : TrapGrowOptions) : Except String Unit := do
  options.base.check
  if options.trapGrowthFailure then
    if options.base.mode != .trapInsertion then
      .error "fatal-OOM growth guard requires trap-insertion mode"
    else if options.base.selectGrowthFailure then
      .error "fatal-OOM growth guard cannot be combined with growth-failure selection"
    else
      .ok ()
  else
    .ok ()

/-- The supplied exact cleanup remains independently selectable. With the new
flag disabled this is exactly the original mode runner. When enabled, preserve
the actual grow attempt and insert its failure guard only for the fully checked
literal-delta wrapper family; every other module keeps identity fallback. -/
def optimizeTrapGrowBytesUsing
    (cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact)
    (options : TrapGrowOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  if options.trapGrowthFailure then do
    options.check
    let clean ← cleanup options.base.rounds input
    let result := (GrowOOMLiteral.optimize (checkedLift clean.result).1).lower
    let bytes ← encodeModule? result
    pure ⟨clean.source, result, ⟨bytes.toArray⟩⟩
  else
    optimizeModeBytesUsing cleanup options.base input

/-- Disabled means identical executable output and rejection behavior. -/
theorem optimizeTrapGrowBytesUsing_disabled
    (cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact)
    (options : ModeCleanupOptions) (input : ByteArray) :
    optimizeTrapGrowBytesUsing cleanup ⟨options, false⟩ input =
      optimizeModeBytesUsing cleanup options input := rfl

def optimizeTrapGrowBytes (options : TrapGrowOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  optimizeTrapGrowBytesUsing cleanupBytes options input

def optimizeCoalesceTrapGrowBytes (options : TrapGrowOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  optimizeTrapGrowBytesUsing cleanupCoalesceBytes options input

end Silmaril.Wasm.Binaryen.Exe

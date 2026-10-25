module

public import Silmaril.Wasm.Behaviour.OptimizationMode
public import Silmaril.Wasm.Binaryen.Exe.ProfileCleanup
public import Silmaril.Wasm.Binaryen.Exe.CoalesceCleanup
public import Silmaril.Wasm.Binaryen.GrowWrapperRuntime

@[expose] public section

/-! A separate byte optimizer with explicit correctness modes.

Runtime imports contain the actual transforms, not their proof packagers.
Every mode runs the same twelve-stage exact cleanup. The optional growth-failure
selection has only a refinement certificate, so exact mode rejects it before
decoding or running transformations. The original optimizer and cleanup driver
retain their defaults, options and implementations.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Optimization

structure ModeCleanupOptions where
  mode : Mode := .equivalence
  rounds : Nat := 2
  selectGrowthFailure : Bool := false
  deriving Repr

def ModeCleanupOptions.check (options : ModeCleanupOptions) : Except String Unit :=
  match options.mode, options.selectGrowthFailure with
  | .equivalence, true =>
      .error "growth-failure selection requires refinement or trap-insertion mode"
  | _, _ => .ok ()

/-- With no mode-specific rewrite, return exactly the old cleanup artifact.
The optional rewrite recognizes the entire lowered wrapper shape and retains
identity fallback on every other module. File IO is outside this function. -/
def optimizeModeBytesUsing
    (cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact)
    (options : ModeCleanupOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact := do
  options.check
  let clean ← cleanup options.rounds input
  if options.selectGrowthFailure then
    let result := (GrowWrapper.optimize (checkedLift clean.result).1).lower
    let bytes ← encodeModule? result
    pure ⟨clean.source, result, ⟨bytes.toArray⟩⟩
  else
    pure clean

/-- The original twelve-stage mode driver, with unchanged defaults and output. -/
def optimizeModeBytes (options : ModeCleanupOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  optimizeModeBytesUsing cleanupBytes options input

/-- An additive thirteen-stage mode driver. Its optional growth selection has
the same restrictions and identity fallback as the original mode driver. -/
def optimizeCoalesceModeBytes (options : ModeCleanupOptions) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  optimizeModeBytesUsing cleanupCoalesceBytes options input

/-- Any base cleanup is returned unchanged when no growth rewrite is requested. -/
theorem optimizeModeBytesUsing_no_growth
    (cleanup : Nat → ByteArray → Except String ProfileCleanupArtifact)
    (mode : Mode) (rounds : Nat) (input : ByteArray) :
    optimizeModeBytesUsing cleanup ⟨mode, rounds, false⟩ input = cleanup rounds input := by
  cases mode <;>
    simp only [optimizeModeBytesUsing, ModeCleanupOptions.check, Bool.false_eq_true,
      ↓reduceIte, bind, Except.bind] <;>
    cases cleanup rounds input <;> rfl

/-- Changing only the policy does not silently enable additional rewrites. -/
theorem optimizeModeBytes_no_growth (mode : Mode) (rounds : Nat) (input : ByteArray) :
    optimizeModeBytes ⟨mode, rounds, false⟩ input = cleanupBytes rounds input := by
  exact optimizeModeBytesUsing_no_growth cleanupBytes mode rounds input

end Silmaril.Wasm.Binaryen.Exe

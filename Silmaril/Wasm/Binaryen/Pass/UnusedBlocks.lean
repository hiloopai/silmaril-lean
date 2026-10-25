module

public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.FastChecks

@[expose] public section

/-! # Removing unused block labels and merging nested blocks

The de Bruijn IR has no textual label names. Removing an unused block label therefore
splices its body. These initial passes handle whole-function wrappers; `mergeBlocks`
keeps the outer wrapper and splices a redundant inner wrapper. The conservative check
requires no free branch target, no return, and only instructions understood by the
effect analysis. Internal branches, loops, calls, and traps are allowed.

The functions are separate from their proofs so executable imports stay light.
-/

namespace Silmaril.Wasm.Binaryen

namespace UnusedBlocks

/-- Sufficient conditions of the direct block-unwrapping simulation. -/
def eligible (body : List BExpr) : Bool :=
  (BExpr.labelsList body).isEmpty && !(effectsList body).any && !(effectsList body).branchesOut

/-- `eligible` without building the label list or the effect lists. -/
def eligibleFast (body : List BExpr) : Bool :=
  !BExpr.escL 0 body && (let f := flagsL body; !f.1 && !f.2.1)

/-- Compiled code runs `eligibleFast`. -/
@[csimp] theorem eligible_eq_fast : @eligible = @eligibleFast := by
  funext body
  simp only [eligible, eligibleFast, BExpr.labelsList_isEmpty, flagsL_eq, flagsOf, Bool.and_assoc]

/-- Remove an unused whole-function block label. Other shapes are left for later rounds. -/
def removeAt (m : BModule) (g : Nat) : BModule :=
  match m.body? g with
  | some [.block _ body] => if eligible body then m.withBody g body else m
  | _ => m

/-- Flatten a nested block into its enclosing block, retaining the outer label and type. -/
def mergeAt (m : BModule) (g : Nat) : BModule :=
  match m.body? g with
  | some [.block outer [.block _ body]] =>
      if eligible body then m.withBody g [.block outer body] else m
  | _ => m

/-- Apply the local rewrite to each defined function, preserving relative indices. -/
def sweep (step : BModule → Nat → BModule) (m : BModule) : BModule :=
  (List.range m.funcs.length).foldl step m

end UnusedBlocks

/-- Initial RemoveUnusedNames pass: splice unused whole-function block wrappers. -/
def removeUnusedNames : BModule → BModule := UnusedBlocks.sweep UnusedBlocks.removeAt

/-- Initial MergeBlocks pass: merge a whole-function block with its single inner block. -/
def mergeBlocks : BModule → BModule := UnusedBlocks.sweep UnusedBlocks.mergeAt

end Silmaril.Wasm.Binaryen

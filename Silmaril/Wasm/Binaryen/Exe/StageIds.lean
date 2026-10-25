module

@[expose] public section

/-! # Import-light identities and ordering of optimizer stages

The executable and its soundness packaging map these same ordered identifiers.
Names and phase order live here; executable transformations and their proofs remain
in their respective import closures. Experimental identifiers are separate so the
default executable need not import experimental transformations.
-/

namespace Silmaril.Wasm.Binaryen.Exe

/-- One function-level stage in the default optimizer. -/
inductive FunctionStageId where
  | dce
  | removeUnusedNames
  | mergeBlocks
  | vacuum
  | simplifyGlobals
  | directize
  | precompute
  | constBranch
  | constSelect
  | addChain
  | codeFolding
  | coalesceLocals
  | removeUnusedBrs
  | optimizeInstructions
  | simplifyLocals
  deriving DecidableEq, Repr

/-- The existing public stage names used by `--stats`. -/
def FunctionStageId.name : FunctionStageId → String
  | .dce => "dce"
  | .removeUnusedNames => "remove-unused-names"
  | .mergeBlocks => "merge-blocks"
  | .vacuum => "vacuum"
  | .simplifyGlobals => "simplify-globals"
  | .directize => "directize"
  | .precompute => "precompute"
  | .constBranch => "const-branch"
  | .constSelect => "const-select"
  | .addChain => "add-chain"
  | .codeFolding => "code-folding"
  | .coalesceLocals => "coalesce-locals"
  | .removeUnusedBrs => "remove-unused-brs"
  | .optimizeInstructions => "optimize-instructions"
  | .simplifyLocals => "simplify-locals"

/-- The single source of phase ordering for one default function-pass round. -/
def functionStageIds : List FunctionStageId :=
  [.dce, .removeUnusedNames, .mergeBlocks, .vacuum, .simplifyGlobals, .directize,
    .precompute, .constBranch, .constSelect, .addChain, .codeFolding, .coalesceLocals,
    .removeUnusedBrs, .optimizeInstructions, .simplifyLocals]

/-- An additional function-level stage enabled by `--experimental`. -/
inductive ExperimentalStageId where
  | rseLine
  deriving DecidableEq, Repr

/-- The existing experimental stage names used by `--stats`. -/
def ExperimentalStageId.name : ExperimentalStageId → String
  | .rseLine => "rse-line"

/-- Additional stages run after the default stages in each experimental round. -/
def experimentalStageIds : List ExperimentalStageId := [.rseLine]

end Silmaril.Wasm.Binaryen.Exe

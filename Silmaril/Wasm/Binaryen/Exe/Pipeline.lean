module

public import Silmaril.Wasm.Binaryen.Exe.StageIds
public import Silmaril.Wasm.Binaryen.Pass.RUME
public import Silmaril.Wasm.Binaryen.Exe.InlineExe
public import Silmaril.Wasm.Binaryen.Exe.InlineFast
public import Silmaril.Wasm.Binaryen.Exe.DCEExe
public import Silmaril.Wasm.Binaryen.Exe.DCEFast
public import Silmaril.Wasm.Binaryen.Pass.MergeBlocksAny
public import Silmaril.Wasm.Binaryen.Pass.VacuumLite
public import Silmaril.Wasm.Binaryen.Pass.SimplifyGlobals
public import Silmaril.Wasm.Binaryen.Pass.PrecomputeLite
public import Silmaril.Wasm.Binaryen.Pass.CodeFolding
public import Silmaril.Wasm.Binaryen.GcProfile
public import Silmaril.Wasm.Binaryen.Pass.CoalesceLocalsLite
public import Silmaril.Wasm.Binaryen.Pass.RemoveUnusedBrs
public import Silmaril.Wasm.Binaryen.Pass.IfSwap
public import Silmaril.Wasm.Binaryen.Pass.SimplifyLocalsLite
public import Silmaril.Wasm.Binaryen.Pass.Directize
public import Silmaril.Wasm.Binaryen.Pass.ConstBranch
public import Silmaril.Wasm.Binaryen.Pass.ConstSelect
public import Silmaril.Wasm.Binaryen.Pass.AddChain

@[expose] public section

/-! # The optimisation pipeline: executable run functions

This file holds only the **run functions** of the `binaryen-lean` pipeline. Their
soundness is in `Exe/PipelineSound.lean`, where each stage is a `Pass` of the pass API
(`PassAPI/Pass.lean`) whose `run` is, definitionally, the function defined here, and
the pipeline is a product in the pass monoid. The split exists because executable
modules must not import `Inline.lean` (see below); the pass values, which carry their
proofs, live on the proof side.

The pipeline, on a module that passes the **profile check** `profileOk` (in the
GC slice of the Binaryen profile, `BModule.inGcProfile` (`GcProfile.lean`), and a type
section whose function types use numeric and reference types only, `typesInGcProfile`):

1. `inlineSmall` — inline direct calls to small leaf callees (`Exe/InlineExe.lean`);
2. `rounds` repetitions of the **function-level stages** `functionStages`;
3. `rume` — RemoveUnusedModuleElements (`Pass/RUME.lean`).

Inlining is proved for type sections whose function types have numeric, `funcref` or
`externref` parameters and results (`typesInProfile`) and is the identity elsewhere;
RUME is the identity outside the base profile (`Pass/RUME.lean`).

Every stage runs under `guarded`: its output is kept only when it passes `profileOk`,
otherwise the stage is skipped. On the proof side this is exactly a checked pass
(`PassAPI/Checked.lean`): an unverified-invariant transformer with a verified checker.

**Extension point.** `functionStageIds` (`Exe/StageIds.lean`) fixes the function-stage
order shared with `functionPassesP`. `FunctionStageId.transform` gives each
executable transformation; the proof side supplies its `StageOk` certificate.
Checked DCE (`Exe/DCEExe.lean`) is proved equal to `Binaryen.dceChecked`
(`Pass/DCECheck.lean`) in `Exe/DCESound.lean`. See
`PassRegistry.lean` and `Silmaril.Wasm.Binaryen.Exe.OptCompatMain`, section "Adding a pass".

**Executable modules must not import `Inline.lean`.** Its import closure contains
`NTyping.lean`'s `Counterexample.overflowFunc`, a closed term holding
`List.replicate (2 ^ 32 + 1) .i32`; the compiler evaluates closed terms when the
executable initialises its imports, so any executable importing it runs out of
memory before `main`. The executable inliner therefore uses its own copy of
`inlineSite` (`Exe/InlineExe.lean`, proved equal to the original in
`Exe/PipelineSound.lean`).
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Numerics

/-! ## The profile check -/

/-- Every function type of the type section has profile parameters and results
(numeric, `funcref` or `externref`, `sigValType`). -/
def typesInProfile (m : BModule) : Bool :=
  m.base.typeDefinitions.all fun st => match st.body with
    | .func ft => (ft.params ++ ft.results).all sigValType
    | _ => true

/-- Every function type of the type section has GC-slice parameters and results
(struct and array types are not constrained: the encoder rejects what it cannot write). -/
def typesInGcProfile (m : BModule) : Bool :=
  m.base.typeDefinitions.all fun st => match st.body with
    | .func ft => (ft.params ++ ft.results).all gcValType
    | _ => true

/-- **The profile check** every stage's output must pass. -/
def profileOk (m : BModule) : Bool := m.inGcProfile && typesInGcProfile m

/-- Run a stage, keeping its output only when it passes the profile check. -/
def guarded (pass : BModule → BModule) (m : BModule) : BModule :=
  if profileOk (pass m) then pass m else m

/-! ## Stages -/

/-- Inline callees whose body has at most this many lowered instructions
(Binaryen's `-O2` `inlining.alwaysInlineMaxSize` is 2, flexible size 20). -/
def inlineBudget : Nat := 20

/-- At most this many inlining steps. -/
def inlineFuel : Nat := 200

/-- **Inlining with a size heuristic** (`Exe/InlineExe.lean`), on modules whose function
types pass `typesInProfile`. -/
def inlineSmall (budget fuel : Nat) (m : BModule) : BModule :=
  if typesInProfile m then Inl.inlineSmall budget fuel m else m

/-- A named module-to-module stage. -/
abbrev Stage := String × (BModule → BModule)

/-- The inlining stage. -/
def inlineStage (budget : Nat) : Stage := ("inline", guarded (inlineSmall budget inlineFuel))

/-- The RUME stage. -/
def rumeStage : Stage := ("rume", guarded rume)

/-- The DCE stage: per-function dead-code elimination where the cut checker accepts. -/
def dceStage : Stage := ("dce", guarded Dce.dceChecked)

/-- The executable transformation identified by a default function stage. Its
`StageOk` certificate is supplied separately in `Exe/PipelineSound.lean`. -/
def FunctionStageId.transform : FunctionStageId → BModule → BModule
  | .dce => Dce.dceChecked
  | .removeUnusedNames => Binaryen.removeUnusedNames
  | .mergeBlocks => mergeBlocksAny
  | .vacuum => VacuumLite.vacuumLite
  | .simplifyGlobals => Binaryen.simplifyGlobals
  | .directize => Binaryen.directize
  | .precompute => PrecomputeLite.precomputeLite
  | .constBranch => ConstBranch.constBranchChecked
  | .constSelect => ConstSelect.constSelectChecked
  | .addChain => AddChain.addChainChecked
  | .codeFolding => Binaryen.codeFolding
  | .coalesceLocals => CoalesceLocalsLite.deadSetLite
  | .removeUnusedBrs => invertGuardsChecked
  | .optimizeInstructions => IfSwap.ifSwapChecked
  | .simplifyLocals => SimplifyLocalsLite.teeDrop

/-- Every function stage retains the original executable profile guard. -/
def FunctionStageId.run (stage : FunctionStageId) : BModule → BModule :=
  guarded stage.transform

/-- The named executable stage corresponding to an identifier. -/
def FunctionStageId.toStage (stage : FunctionStageId) : Stage := (stage.name, stage.run)

/-- Function-level stages of one round, in the shared registry's order. -/
def functionStages : List Stage := functionStageIds.map FunctionStageId.toStage

/-- Run stages left to right. -/
def runStages (ss : List Stage) (m : BModule) : BModule := ss.foldl (fun m s => s.2 m) m

/-- The pipeline as named stages (the driver's `--stats` report runs these). -/
def pipelineStages (budget rounds : Nat) : List Stage :=
  inlineStage budget :: (List.replicate rounds functionStages).flatten ++ [rumeStage]

/-- **The pipeline** with inlining budget `budget`. -/
def pipelineWith (budget rounds : Nat) (m : BModule) : BModule :=
  runStages (pipelineStages budget rounds) m

/-- The default pipeline. -/
def pipeline (rounds : Nat) (m : BModule) : BModule := pipelineWith inlineBudget rounds m

/-! ## Size-guarded choice between pipeline variants

Inlining without a following SimplifyLocals/block-unwrap pass can grow a module. The
driver runs the pipeline with budget 0 and with `inlineBudget` and keeps the smallest
of the input and the two results. On the proof side this is `Pass.best`
(`bestNamed_run` in `Exe/PipelineSound.lean`); here each score is computed once and
the winner is labelled for the report. -/

/-- The labelled pipeline candidates. -/
def namedCandidates (rounds : Nat) (m : BModule) : List (String × BModule) :=
  [("budget0", pipelineWith 0 rounds m), ("inline", pipelineWith inlineBudget rounds m)]

/-- Fold step: keep the accumulator unless the candidate's score is strictly smaller. -/
def pickScored (acc c : String × BModule × Nat) : String × BModule × Nat :=
  if c.2.2 < acc.2.2 then c else acc

/-- The best labelled candidate (the input, labelled `input`, wins ties). -/
def bestNamed (score : BModule → Nat) (rounds : Nat) (m : BModule) : String × BModule :=
  let r := ((namedCandidates rounds m).map fun c => (c.1, c.2, score c.2)).foldl pickScored
    ("input", m, score m)
  (r.1, r.2.1)

end Silmaril.Wasm.Binaryen.Exe

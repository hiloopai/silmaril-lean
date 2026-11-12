module

public import Silmaril.Wasm.Binaryen.NeutralOps.Defs
public import Silmaril.Wasm.Binaryen.EqzPair.Defs
public import Silmaril.Wasm.Binaryen.RseLine.Defs
public import Silmaril.Wasm.Binaryen.DropGet.Defs
public import Silmaril.Wasm.Binaryen.TeeForm.Defs
public import Silmaril.Wasm.Binaryen.SsaStage.Defs
public import Silmaril.Wasm.Binaryen.Exe.Pipeline
public import Silmaril.Wasm.Binaryen.Exe.CleanupPresets
public import Silmaril.Wasm.Binaryen.Exe.CompactInput

@[expose] public section

/-! # The verified-stage optimisation pipelines: executable run functions

Run functions only; soundness is in `Silmaril.Wasm.Binaryen.Pipeline.Thms`. This
module is executable-safe: it imports silmaril's executable pipeline modules and
the run-function modules of the verified stages, never `Inline.lean` or any proof module (see the
warning in `Silmaril.Wasm.Binaryen.Exe.Pipeline`).

Two pipelines extend silmaril's, mirroring its two drivers:

* **The executable-contract pipeline** (`extraPipelineWith`), mirroring
  `Exe.pipelineWith`: inlining, then `rounds` rounds of silmaril's function stages
  *followed by* the verified function stages, then RUME. Every stage runs under
  silmaril's `guarded` profile check. Soundness: `extra_pipeline_sound`
  (deterministic profiles, the contract `Exe.ExeC`).
* **The selected-stage byte driver** (`extraSelectedCompatBytes`), mirroring
  `Exe.optimizeSelectedCompatBytes` without growth policies: an ordered list of
  silmaril `CleanupStage`s and verified stages, repeated `rounds` times, between
  silmaril's checked decode/validate/lift and encode boundary. Soundness:
  `extraSelectedCompatBytes_sound` (every numerical profile, closed host, for
  every-profile stages), `extraSelectedCompatBytes_sound_exact` (every numerical
  profile, every selection, the opt-in `ssa` stage included) and
  `extraSelectedCompatBytes_sound_det` (every deterministic profile, the same
  selections).

The `-O` presets (`extraPresetStages`) are silmaril's restricted version_133
schedules (`Exe.CleanupPreset.schedule`) with each verified stage inserted after every
slot of its upstream pass (`optimize-instructions`; `rse`, which silmaril's
schedule lists as omitted and which is followed by a `vacuum` slot).

**Profiles.** Every verified export-level stage (`neutral-ops`, `eqz-pair`, `rse-line`,
`drop-get`, `tee-form`) is certified at every numerical profile
(`ExtraStageId.anyProfile`): `rse-line` and `tee-form` through the frame-aware
deferred simulation of `Silmaril.Wasm.Binaryen.Deferred`, `drop-get` through a typed
reverse simulation. The flag is kept for future stages certified at deterministic
profiles only. The byte theorem `extraSelectedCompatBytes_sound` covers selections of
every-profile stages, which are now all selections, the opt-in `ssa` stage included
(`extraSelectedCompatBytes_sound_exact`).

**The SSA stage.** `ExtraStage.ssa` runs the Wasm lambda-SSA optimiser
(`SsaStage.ssaRun`). Its certificate class is `StageCert.anyProfile`: exact export
equivalence at every numerical profile under the closed host (`SsaStage.ssaP`, from
`SSA.replace_exportEquiv` and the caller-side simulation `SSA.behaviours_srel`), like the
other stages. It is never in a preset or in `extraStageIds`.

**Extension point.** A new verified function-level stage is a constructor of
`ExtraStageId` with a `name`, an `upstream` Binaryen slot and an executable
`transform` and `anyProfile` flag here, and certificates `ExtraStageId.stageOk`
(`Exe.StageOk`), `ExtraStageId.detP` (deterministic-profile `EquivPass`) and, for
every-profile stages, `ExtraStageId.equivP` in `Silmaril.Wasm.Binaryen.Pipeline.Thms`;
the exhaustive matches force all of them. The
Wasm lambda-SSA optimiser (`Silmaril/Wasm/SSA`) is intended to be registered this way
once it exposes a per-function `optimizeFunc?` with a lowering-back certificate;
nothing here depends on it yet. Stages listed in `extraStageIds` join the default
round and the presets.
-/

namespace Silmaril.Wasm.Binaryen.Pipeline

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.Exe

/-! ## Verified stage identifiers -/

/-- A verified function-level stage. -/
inductive ExtraStageId where
  /-- `Silmaril.Wasm.Binaryen.NeutralOps`: `x op k` with a neutral constant `k`,
  consumed by an integer operation of the same type, becomes `x`. -/
  | neutralOps
  /-- `Silmaril.Wasm.Binaryen.EqzPair`: `i32.eqz; i32.eqz` before `br_if`, `select` or
  `i32.eqz` is dropped. -/
  | eqzPair
  /-- `Silmaril.Wasm.Binaryen.RseLine` (silmaril's `rse-line`): `local.get x; local.set x`
  becomes `local.get x; drop`, `local.get x; local.tee x` becomes `local.get x`. -/
  | rseLine
  /-- `Silmaril.Wasm.Binaryen.DropGet`: `local.get x; drop` becomes `nop` (removed by
  `vacuum`). -/
  | dropGet
  /-- `Silmaril.Wasm.Binaryen.TeeForm`: `local.set x; local.get x` becomes `local.tee x`. -/
  | teeForm
  deriving DecidableEq, Repr

/-- Command-line and `--stats` name. -/
def ExtraStageId.name : ExtraStageId → String
  | .neutralOps => "neutral-ops"
  | .eqzPair => "eqz-pair"
  | .rseLine => "rse-line"
  | .dropGet => "drop-get"
  | .teeForm => "tee-form"

/-- The upstream Binaryen pass this stage is a restricted subrule of. -/
def ExtraStageId.upstream : ExtraStageId → String
  | .neutralOps => "optimize-instructions"
  | .eqzPair => "optimize-instructions"
  | .rseLine => "rse"
  | .dropGet => "rse"
  | .teeForm => "simplify-locals"

/-- The executable transformation of a verified stage. -/
def ExtraStageId.transform : ExtraStageId → BModule → BModule
  | .neutralOps => NeutralOps.neutralOpsChecked
  | .eqzPair => EqzPair.eqzPairChecked
  | .rseLine => RseLine.rseLineChecked
  | .dropGet => DropGet.dropGetChecked
  | .teeForm => TeeForm.teeFormChecked

/-- Is the stage certified at *every* numerical profile? A stage with `false` would be
certified at every deterministic profile (`Profile.deterministic o`) only; every
current stage is certified at every profile. -/
def ExtraStageId.anyProfile : ExtraStageId → Bool
  | .neutralOps | .eqzPair | .rseLine | .dropGet | .teeForm => true

/-- Every verified stage runs under silmaril's executable profile guard. -/
def ExtraStageId.run (stage : ExtraStageId) : BModule → BModule :=
  guarded stage.transform

def ExtraStageId.toStage (stage : ExtraStageId) : Stage := (stage.name, stage.run)

/-- The verified stages of one default round, in order. -/
def extraStageIds : List ExtraStageId := [.neutralOps, .eqzPair, .rseLine, .dropGet, .teeForm]

def extraFunctionStages : List Stage := extraStageIds.map ExtraStageId.toStage

/-! ## The executable-contract pipeline -/

/-- One round: silmaril's function stages, then the verified stages. -/
def extraRoundStages : List Stage := functionStages ++ extraFunctionStages

/-- The pipeline as named stages. -/
def extraPipelineStages (budget rounds : Nat) : List Stage :=
  inlineStage budget :: (List.replicate rounds extraRoundStages).flatten ++ [rumeStage]

/-- **The verified-stage pipeline** with inlining budget `budget`. -/
def extraPipelineWith (budget rounds : Nat) (m : BModule) : BModule :=
  runStages (extraPipelineStages budget rounds) m

/-- The default verified-stage pipeline. -/
def extraPipeline (rounds : Nat) (m : BModule) : BModule :=
  extraPipelineWith inlineBudget rounds m

/-! ## The selected-stage byte driver -/

/-- A selectable stage: one of silmaril's or a verified stage. -/
inductive ExtraStage where
  | silmaril (stage : CleanupStage)
  | verified (stage : ExtraStageId)
  /-- The opt-in Wasm lambda-SSA optimiser (`SsaStage.ssaRun`); exact export equivalence at
  every profile, never in a preset. -/
  | ssa
  deriving DecidableEq, Repr

def ExtraStage.name : ExtraStage → String
  | .silmaril stage => stage.name
  | .verified stage => stage.name
  | .ssa => "ssa"

/-- What a stage's certificate covers. -/
inductive StageCert where
  /-- Exact export equivalence at every numerical profile (closed host). -/
  | anyProfile
  /-- Exact export equivalence at every deterministic profile (closed host). -/
  | deterministic
  /-- Output validity, and per rewritten function equal Core 3.0 behaviours (closed host,
  every numerical profile, divergence included) of its typed invocations in the allocated
  stores of input and output; no export-level claim. No stage has this class any more: the
  `ssa` stage, its former user, is now `anyProfile` (`SsaStage.ssaRun_exportEquiv`). -/
  | coreInvocations
  deriving DecidableEq, Repr

def ExtraStage.cert : ExtraStage → StageCert
  | .silmaril _ => .anyProfile
  | .verified stage => if stage.anyProfile then .anyProfile else .deterministic
  | .ssa => .anyProfile

/-- Silmaril's selectable stages are all certified at every profile. -/
def ExtraStage.anyProfile : ExtraStage → Bool
  | .silmaril _ => true
  | .verified stage => stage.anyProfile
  | .ssa => true

/-- Is the stage covered by an export-equivalence certificate (at least at
deterministic profiles)? Every stage is, `ssa` included (`SsaStage.ssaP`). -/
def ExtraStage.exact : ExtraStage → Bool
  | _ => true

/-- Validity-only run, as silmaril's `CleanupStage.runValid`: internal checks and
fallbacks remain, the legacy output-profile guard is omitted. -/
def ExtraStage.runValid : ExtraStage → BModule → BModule
  | .silmaril stage => stage.runValid
  | .verified stage => stage.transform
  | .ssa => SsaStage.ssaRun

/-- Run exactly the requested stages, in order. -/
def extraSelectedRound (stages : List ExtraStage) (m : BModule) : BModule :=
  stages.foldl (fun m stage => stage.runValid m) m

/-- Silmaril's checked byte boundary around `rounds` repetitions of the selection. -/
def extraSelectedBytes (stages : List ExtraStage) (rounds : Nat) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  cleanupTransformBytes ((extraSelectedRound stages)^[rounds]) input

/-- The byte endpoint, accepting compact import groups as silmaril's CLI does. -/
def extraSelectedCompatBytes (stages : List ExtraStage) (rounds : Nat) (input : ByteArray) :
    Except String ProfileCleanupArtifact :=
  CompactInput.optimizeUsing (extraSelectedBytes stages rounds) input

/-! ## Presets -/

/-- One slot of a verified-stage preset: upstream name, local stages, note. -/
structure StageSlot where
  upstream : String
  stages : List ExtraStage
  note : String

/-- Silmaril's restricted schedule with each verified stage after every slot of its
upstream pass (`optimize-instructions`, `rse`, `simplify-locals`). -/
def extraSchedule (preset : CleanupPreset) : List StageSlot :=
  preset.schedule.flatMap fun slot =>
    let base : StageSlot := ⟨slot.upstream, slot.stages.map .silmaril, slot.note⟩
    [base] ++ (extraStageIds.filter (·.upstream == slot.upstream)).map fun s =>
      ⟨s.upstream, [.verified s], "verified subrule " ++ s.name ++
        (if s.anyProfile then "" else " (deterministic profiles)")⟩

def extraPresetStages (preset : CleanupPreset) : List ExtraStage :=
  (extraSchedule preset).flatMap (·.stages)

def extraPresetReport (preset : CleanupPreset) : String :=
  preset.name ++ " verified-stage schedule (silmaril restricted version_133 + verified stages)\n" ++
    String.intercalate "\n" ((extraSchedule preset).map fun slot =>
      slot.upstream ++ " => " ++
      (if slot.stages.isEmpty then "[omitted]" else
        String.intercalate "," (slot.stages.map ExtraStage.name)) ++ " (" ++ slot.note ++ ")")

end Silmaril.Wasm.Binaryen.Pipeline

module

public import Silmaril.Wasm.Tools.Gen.Core.Defs
public import Silmaril.Wasm.Binaryen.Pipeline.Defs
public import Silmaril.Wasm.Binaryen.Exe.OptCompatMain

/-!
# Semantics-preserving mutators: random selections of verified optimisation stages

The class of mutators proved **equivalent in Core 3.0**: a seed picks a short sequence of the
stages `wasm-opt` can select (silmaril's cleanup stages, the verified stages and the
`ssa` stage), and the module is lifted to the Binaryen IR (`Exe.checkedLift`, lowering back
exactly: `checkedLift_lower`), run through them, and lowered. Each stage is an
`ArbitraryProfile.EquivPass` (`Silmaril.Wasm.Binaryen.Pipeline.ExtraStage.equivP`), so the result is
**export-equivalent** to the input (`ExportEquiv (· = ·) P closedHost`: on every valid store
and import list, the two instantiate together and every session of export calls has the same
behaviours, divergence included) at **every** numerical profile `P`.

* `CoreEquiv P H`: that equivalence (closed host);
* `semStages`: the selectable stages; `ExtraStage.anyProfile_all`: all are every-profile;
* `pickStages`: a seeded selection of one to three stages; `optRun stages m`: the run.

`Thms`: `optSem P H` (a `SemMutator` for `ModuleValid`), `featSem P H S`, its checked
restriction to the feature set `S`, and `featSemIn P H S`, the same class run by `optRunIn S`
(stage by stage inside `S`), proved to stay inside `S` without any checker.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Sem

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Models Silmaril.Wasm.Binaryen.Pipeline
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **Export equivalence** of Core 3.0 modules at profile `P`, closed host. -/
def CoreEquiv (P : Profile) (H : Type) (m m' : Module) : Prop :=
  ExportEquiv (· = ·) P (closedHost (H := H)) m m'

/-- The selectable stages of `wasm-opt`. -/
def semStages : List ExtraStage :=
  Exe.optCompatStages.map .silmaril ++ extraStageIds.map .verified ++ [.ssa]

theorem ExtraStage.anyProfile_all (s : ExtraStage) : s.anyProfile = true := by
  cases s with
  | silmaril _ => rfl
  | verified s => cases s <;> rfl
  | ssa => rfl

/-- One to three stages, by the seed. -/
def pickStages : Rand (List ExtraStage) := do
  Rand.list (← Rand.range 1 3) (Rand.pick semStages .ssa)

/-- **Run stages on a Core module** through the Binaryen IR. -/
def optRun (stages : List ExtraStage) (m : Module) : Module :=
  (extraSelectedRound stages (Exe.checkedLift m).1).lower

/-- **Run stages inside a feature set**: one stage at a time, keeping a stage's output only
when it stays inside `S` (the syntactic test `Module.inFeatB S`, not validation: validity of
every stage's output is proved, `Thms.optRun_valid`). So the result is inside `S` by
construction (`Thms.optRunIn_inFeat`), valid and export-equivalent to the input
(`Thms.optRunIn_valid`, `optRunIn_equiv`), with no validator call and no fallback to the
input as a whole. -/
def optRunIn (S : FeatureSet) : List ExtraStage → Module → Module
  | [], m => m
  | s :: ss, m => optRunIn S ss (if Module.inFeatB S (optRun [s] m) then optRun [s] m else m)

end Silmaril.Wasm.Tools.Gen.Sem

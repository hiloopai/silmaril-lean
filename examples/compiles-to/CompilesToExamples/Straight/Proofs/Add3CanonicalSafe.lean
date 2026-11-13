module

-- The Core dynamics reads source locations through `libraryLocation`, which splits the file name
-- with `String.splitOn`; these imports expose the String bodies so that `cbv` can run the Core.
import all Init.Data.String.Legacy
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
public import CompilesToExamples.Straight.Defs
public import Silmaril.Project.CompilesTo.Thms

/-! `examples/compiles-to/straight/straight.c`, `add3`: **safe from its canonical entry**. The call
`add3(1, 2, 3)` from the canonical entry (`CFn.canonicalEntry`: the arguments allocated in order
from an empty memory) has a forced Core run (every state has one successor) to `Defined(Specified 6)`,
checked by `cbv`; `safe_of_forced` makes the entry safe. This is the non-vacuity of the
`c.compiles_to.canonical_entry` rows of both builds. -/

namespace CompilesToExamples.Straight

open Silmaril.Project.CompilesTo
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

/-- The arguments of the call `add3(1, 2, 3)`. -/
public def add3Args : Silmaril.X86.SystemV.CApi.Arguments [.int32, .int32, .int32] :=
  .cons (kind := .int32) (1 : BitVec 32) (.cons (kind := .int32) (2 : BitVec 32)
    (.cons (kind := .int32) (3 : BitVec 32) .nil))

attribute [local cbv_eval] Silmaril.Cerberus.Core.Dynamics.requestAux.eq_def
attribute [local cbv_eval] Silmaril.Cerberus.Core.Dynamics.hasCCall.eq_def
attribute [local cbv_eval] Silmaril.Cerberus.Core.Dynamics.controlHasCCall.eq_def
attribute [local cbv_eval] Silmaril.Cerberus.Core.Dynamics.activeCall.eq_def
attribute [local cbv_eval] List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton

/-- The run ends normally. -/
def endsDefined (s : Option State) : Bool :=
  match s with
  | some h => match h.control with
    | .halt (.defined _) => true
    | _ => false
  | none => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem run_forced :
    endsDefined (forcedRun add3Fn.file add3Fn.labels 400 (add3Fn.canonicalEntry add3Args)) = true := by
  cbv

/-- The canonical entry of `add3(1, 2, 3)` is safe. -/
public theorem add3_args_safe : (add3Fn.source []).Safe (add3Fn.canonicalEntry add3Args) := by
  have h := run_forced
  unfold endsDefined at h
  split at h
  · rename_i hfin hrun
    split at h
    · rename_i v hc
      exact safe_of_forced (F := O0.add3) (forcedRun_sound _ _ _ hrun).1 hc
    · cases h
  · cases h

/-- **`add3` is safe from its canonical entry** on `add3(1, 2, 3)`. -/
public theorem add3_canonical_safe : Task.add3_canonical_safe := ⟨add3Args, add3_args_safe⟩

end CompilesToExamples.Straight

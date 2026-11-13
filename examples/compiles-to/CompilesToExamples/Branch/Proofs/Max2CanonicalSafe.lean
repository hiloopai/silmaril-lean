module

-- The Core dynamics reads source locations through `libraryLocation`, which splits the file name
-- with `String.splitOn`; these imports expose the String bodies so that `cbv` can run the Core.
import all Init.Data.String.Legacy
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
public import CompilesToExamples.Branch.Defs
public import Silmaril.Project.CompilesTo.Thms
-- Not used: built after `add3`'s run, so that the two `cbv` runs of the Core (several GB each)
-- do not overlap on a 16 GB machine.
import CompilesToExamples.Straight.Proofs.Add3CanonicalSafe

/-! `examples/compiles-to/branch/branch.c`, `max2`: **safe from its canonical entry**. The call
`max2(1, 2)` from the canonical entry (`CFn.canonicalEntry`: the arguments allocated in order
from an empty memory) has a forced Core run (every state has one successor) to `Defined(Specified 2)`,
checked by `cbv`; `safe_of_forced` makes the entry safe. This is the non-vacuity of the
`c.compiles_to.canonical_entry` rows of both builds. -/

namespace CompilesToExamples.Branch

open Silmaril.Project.CompilesTo
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

/-- The arguments of the call `max2(1, 2)`. -/
public def max2Args : Silmaril.X86.SystemV.CApi.Arguments [.int32, .int32] :=
  .cons (kind := .int32) (1 : BitVec 32) (.cons (kind := .int32) (2 : BitVec 32) .nil)

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
    endsDefined (forcedRun max2Fn.file max2Fn.labels 400 (max2Fn.canonicalEntry max2Args)) = true := by
  cbv

/-- The canonical entry of `max2(1, 2)` is safe. -/
public theorem max2_args_safe : (max2Fn.source []).Safe (max2Fn.canonicalEntry max2Args) := by
  have h := run_forced
  unfold endsDefined at h
  split at h
  · rename_i hfin hrun
    split at h
    · rename_i v hc
      exact safe_of_forced (F := O0.max2) (forcedRun_sound _ _ _ hrun).1 hc
    · cases h
  · cases h

/-- **`max2` is safe from its canonical entry** on `max2(1, 2)`. -/
public theorem max2_canonical_safe : Task.max2_canonical_safe := ⟨max2Args, max2_args_safe⟩

end CompilesToExamples.Branch

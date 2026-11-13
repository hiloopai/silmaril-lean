module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Extends.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs

/-!
# `Engine.Core3.Agreement`: the laws that definitions cite

The theorems of the component reference copy `Engine.Core3.Agreement` that definition parts cite
(engine records bundle such laws as fields). The other theorems stay in
`Silmaril.Raw.Wasm.Component.Engine.Core3.Agreement`, which imports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
variable {H : Type}

/-- On a typed thread, an internal step of the concrete engine is an internal step of the
single-threaded machine. -/
theorem core3_internal_sound {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {ts : List CValType} {y : Store H × SingleThreaded.Thread}
    (ht : SingleThreaded.ThreadOk s t ts)
    (h : SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some y) :
    SingleThreaded.Internal o (s, t) y :=
  SingleThreaded.internalC_sound o (fun _ hc => SingleThreaded.Exec.stepI_sound_typed ht hc) h

/-- On a typed thread, the status of the concrete engine is the flat view of the status of the
single-threaded machine. -/
theorem statusE_eq {o : SingleThreaded.GrowOracle} {s : Store H} {t : SingleThreaded.Thread}
    {ts : List CValType} (ht : SingleThreaded.ThreadOk s t ts) :
    statusE o s t = flatStatus (SingleThreaded.status o s t) := by
  rw [statusE_eq_flatStatus, SingleThreaded.Exec.statusI_eq_typed ht]

end Silmaril.Wasm.Component.Engine.Core3

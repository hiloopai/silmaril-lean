module

public import Silmaril.Containers.SyncComponent.Thms
meta import Silmaril.Containers.SyncComponent.Defs
meta import Silmaril.Containers.Outcome.Defs

open Silmaril.Containers Silmaril.Containers.SyncComponent

/-- Enumerate the two admitted host answers and the defined guest-trap run. `complete_run`
and `runtime_choice` check these traces against source steps and the existing component. -/
public def main : IO Unit := do
  IO.println "Synchronous abstract WIT component (model runner; no Wasm engine)."
  for choice in [false, true] do
    let trace := completedTrace false choice
    IO.println s!"host choose() = {choice}; sample(false) = {!choice}"
    IO.println s!"  source: {repr trace}"
    IO.println s!"  container: {repr (trace.filter Event.isExport)}; wrapper exit 0"
  IO.println "sample(false) can also wait for an answer; availability does not prove delivery. No exit."
  let trapTrace := completedTrace true false
  IO.println s!"sample(true): {repr trapTrace}; guest {repr (guestOutcome none)}; wrapper exit 70"
  IO.println s!"optional more-UB policy: {repr ((guestOutcome none).trapAsUB .unmodeled)}"
  IO.println "Checked: legal turns, typed replies, both host choices, component/host linking,"
  IO.println "executor certificate, same export spec, noHostUB, nonvacuity, trap policy direction."

module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSound.Defs

/-!
# Round 7, REH route 2: soundness of the flow check (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxSound`; see `docs/projects/spectec/README.md`. `Task.flowSound` is frozen and open. Proved here only the base case of its
induction:

* `defsVT_zero`: at fuel `0` every definition conforms (no clause answers, and the primitives
  are not consulted, since running out of fuel is not a definite failure).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxSound

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

/-- **The base case of `Task.flowSound`.** -/
theorem defsVT_zero (S : Sig) (T : TSig) (env : Env) : DefsVT S T env 0 := by
  intro f d pts ws v _ _ _ h
  simp [tryClauses] at h

end Silmaril.Wasm.SpecTec.Sim.Round7.NxSound

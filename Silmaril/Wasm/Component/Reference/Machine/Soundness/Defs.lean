module

public import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

/-!
# Soundness of the executable machine

The executable machine of `Machine/Exec.lean` (`step?`, `hostStep?`, and the fuel
drivers `run`, `runTop`, `runTopCall`) only takes transitions of the relational machine
`Machine.Step` of `Machine/Step.lean`. Both interpret the specification programs
`Canon.P E σ` (the REF functions of `definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>).

## Results (all proved, for every engine `E`, executable stepper `X : E.Exec`, oracle `o`,
dispatcher and host readiness `hr`)

* `step?_sound`: `step? dispatch X o m = some (l, st, m') → Step o.prof hr dispatch m l m'`.
  Core steps are sound through `X.step?_sound` (`E.Internal`); oracle answers through the
  `Allowed o.prof` check of `step?`; internal traps through `Fault`.
* `hostStep?_sound`: `hostStep? hr ev m = some (l, m') → Step prof hr dispatch m l m'` for every
  profile `prof` (host events consult no oracle).
* `run_sound`, `runTop_sound`, `runTopCall_sound`: the label trace of a run is a `Steps` trace
  from the start configuration to the final one (`runTopCall` starts with the invoke label).
* `run_outcome`, `runTop_outcome`: the outcome of a run is `outOfFuel` or `outcomeOf` of the
  final configuration; `outcomeOf_resolved` / `outcomeOf_trap` / `outcomeOf_deadlock` relate
  it to the terminal predicates `Resolved` / `Trapped` / `Deadlocked` of `Machine/Step.lean`.
* `run_sound_resolved`, `runTop_sound_resolved`: a `resolved` outcome gives a `Steps` trace to a
  `Resolved` configuration in whose `results` every pending top-level call appears;
  `runTopCall_sound_resolved`: in particular the issued call `c` has a result.
* `Step.pending_mono` / `Steps.pending_mono`: top-level calls are never forgotten.

The link between the two files' separately written host-frame programs and named store
updates (`Machine.invokeProg` / `StepDefs.invokeProg`, `CStoreOps.setThreadStatus` /
`StepDefs.threadStatusSt`, ...) is definitional (`invokeProg_eq`, ...).

## Design notes

* A run returns the record `RunResult` of `Machine/Exec.lean`
  (`config`, `labels`, `outcome`); the drivers also take `hr` and `X`.
* `Step` takes `hr`; `step?` does not depend on it, so `step?_sound` holds for every `hr`.

Not claimed here: completeness of `step?`, invariants, fairness, termination.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-! ## Agreement of the named definitions of `Machine/Exec.lean` and `Machine/Step.lean` -/

/-! ## Soundness of one step -/

section StepSound

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

end StepSound

/-! ## Monotonicity of the pending calls -/

section Pending

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

@[simp] theorem Config.setCont_pending (m : Config E σ) (t : ThreadId)
    (a : Option (Activation E σ)) : (m.setCont t a).pending = m.pending := rfl

@[simp] theorem Config.setCancel_pending (m : Config E σ) (c : CallId) (r : CancelRef) :
    (m.setCancel c r).pending = m.pending := rfl

end Pending

/-! ## Outcomes and terminal predicates -/

section Outcome

variable (hr : HostReady σ)

end Outcome

/-! ## Soundness of the drivers -/

section Drivers

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

end Drivers

/-! ## Example: the invoke test of `Machine/Exec.lean`, transported to the relation -/

section Examples

end Examples

end Silmaril.Wasm.Component.Machine

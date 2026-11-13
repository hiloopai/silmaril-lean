module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripBase
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripStep
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripFwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripTypMod
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripTypCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripGood
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripMods
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripUnstrip
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripSucc
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripWit

/-!
# Removing export lists from V2 configurations: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.Utf8Strip`; see `docs/projects/spectec/README.md`, "fwd20
".

* `Utf8StripBase`: `stripAdmins20` fixes values and plain code and distributes over `++`; a
  function instance of the stripped store is the stripped instance (`funcInst?_stripStore20`).
* `Utf8StripStep`: **`step_strip20`**, the V2 analogue 's `Round7.step_strip`: on a
  store without host functions, a step `c → c'` gives `stripConfig20 c → stripConfig20 c'`
  (`pureStep_strip`, `readStep_strip`).
* `Utf8StripFwd`: **`fwdU20_of_legs`**: `Utf8Mono.Task.fwdU20` follows from the frozen legs
  `Task.goodStrip20`, `Task.goodUnstrip20` and `Task.unstripStep20`, with `step_strip20`,
  `StoreBulk.fwd_good20B` and `Utf8Else.sstepB_utf8_20T`.
* `Utf8StripTypMod`, `Utf8StripTypCode`: typing in `utf8Env20 B` with the exports removed is typing
  in `simEnv20 B`: module instances (`typedV_moduleInst_strip`), function instances, stores,
  frames, states (`typedV_state_strip`) and code (`typedV_admins_strip`). Every other field is off
  `badU20` and moves by `Utf8Else.hasTyp_u20_iff`; the `EXPORTS` field is `[]`.
* `Utf8StripGood`: **`good20B_strip`**, so `Task.goodStrip20` holds (`goodStrip20_holds`), and
  **`fwdU20_of_unstrip`**: `Utf8Mono.Task.fwdU20` from `Task.goodUnstrip20` and
  `Task.unstripStep20`.
* `Utf8StripMods`: **`modsQ_step`**: a V2 step on a host-free store keeps any property of all
  module instances (it never makes one; a call copies the callee's).
* `Utf8StripUnstrip`: in `utf8Env20 B`, state and code are typed exactly when their non-module
  parts are and their module instances are `moduleinst`s (`ModOk`); so the exports can be put
  back (`typedV_state_unstrip`, `typedV_admins_unstrip`).
* `Utf8StripSucc`: **`good20BU_succ`**, so `Task.goodUnstrip20` holds (`goodUnstrip20_holds`),
  and **`fwdU20_of_unstripStep`**: `Utf8Mono.Task.fwdU20` from `Task.unstripStep20` alone.
* `Utf8StripWit`: **`expCfg_legs`**, a witness outside `Good20B`: round 6's `table.copy`
  configuration with the frame's module exporting `"a"` is `Good20BU`, not `Good20B`, and its step
  strips to a step of `utf8Env20T` between `Good20B` configurations with a `Good20BU` successor.

Open: `Task.unstripStep20` (leg 3), the 2.0 form 's `Round7.Task.swapEquiv`, without
the injectivity side condition.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.step_strip20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.step_strip20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.fwdU20_of_legs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.fwdU20_of_legs

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.goodStrip20_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.goodStrip20_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.fwdU20_of_unstrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.fwdU20_of_unstrip

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.goodUnstrip20_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.goodUnstrip20_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.fwdU20_of_unstripStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.fwdU20_of_unstripStep

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.expCfg_legs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.expCfg_legs

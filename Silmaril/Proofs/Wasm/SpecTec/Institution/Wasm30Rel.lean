module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Wasm30
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms

/-!
# The wasm-3.0 semi-comorphism beyond `Step`: `Step_pure` and `Step_read`

The transition `toModel` relates Core's steps to the `Step` facts of the backend canonical model
`stepModel B`. The script's `Step/pure` and `Step/read` rules make every `Step_pure` and
`Step_read` fact of a model of the theory a `Step` fact (`sstepB_pure`, `sstepB_read`, at typed
arguments). So round 6's backward half carries over:

* `pureFact_sound`: on a valid `BoundedSel` configuration `c`, every `Step_pure` fact of
  `stepModel B` from `c`'s code to a typed `instr*` is the image of a Core step from `c` that keeps
  the state, up to `ConfigEq`.
* `readFact_sound`: the same for `Step_read` facts from `c`.
* `pureFact_obs`, `readFact_obs`: such a fact is an observation of `modelChart (stepModel B)` at
  `c`, so on `DomDet` it is matched by `toModel` (`readFact_core`, `pureFact_core`).

Only the sound (backward) direction is proved for these relations. The forward direction would
say which Core steps are `Step_pure` or `Step_read` steps; Core has one step relation
(`Silmaril.Wasm.Execution.Core.Step`) and that classification is not stated.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Wasm30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type} {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `stepModel_facts`. -/
local notation "SM" => stepModel (builtins hn hinj host hf hh nd r)

/-- The environment of the step model. -/
local notation "EM" => simEnv (builtins hn hinj host hf hh nd r)

/-- A valid `BoundedSel` configuration has a typed state and typed code in every `simEnv B`. -/
theorem typed_parts (B : Builtins) {c : Config H} {ts : List CValType} (hok : ConfigOk c ts)
    (hb : Round5.Target.BoundedSel c) :
    TypedV (simEnv B) stateT (stateV hn c.store c.frame) ∧
      TypedV (simEnv B) instrsT (.list (adminsToV c.code)) :=
  ((Typing.typingFacts_simEnv B hn).config c).1 (Round5.Target.typed_of_configOk_sel B hn hok hb)

/-- **`Step_pure` facts become `Step` facts** of the step model, at a typed result. -/
theorem pureFact_obs {c : Config H} {ts : List CValType} (hok : ConfigOk c ts)
    (hb : Round5.Target.BoundedSel c) {js : List Value} (hjs : TypedV EM instrsT (.list js))
    (hp : (SM).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js])) :
    (SM).D "Step" "%~>%" [] (.tuple [configV hn c, cfgV (stateV hn c.store c.frame) js]) := by
  have ht := typed_parts (hn := hn) (builtins hn hinj host hf hh nd r) hok hb
  exact Round6.Reading.sstepB_pure (hasStepRules_simEnv _).pure ht.1 ht.2 hjs hp

/-- **`Step_read` facts become `Step` facts** of the step model, at a typed result. -/
theorem readFact_obs {c : Config H} {ts : List CValType} (hok : ConfigOk c ts)
    (hb : Round5.Target.BoundedSel c) {js : List Value} (hjs : TypedV EM instrsT (.list js))
    (hp : (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    (SM).D "Step" "%~>%" [] (.tuple [configV hn c, cfgV (stateV hn c.store c.frame) js]) := by
  have ht := typed_parts (hn := hn) (builtins hn hinj host hf hh nd r) hok hb
  exact Round6.Reading.sstepB_read (hasStepRules_simEnv _).read ht.1 ht.2 hjs hp

/-- A `Step` fact of the step model from a valid `BoundedSel` configuration is a Core step. -/
theorem stepFact_sound {c : Config H} {ts : List CValType} (hok : ConfigOk c ts)
    (hb : Round5.Target.BoundedSel c) {w : Value}
    (hw : (SM).D "Step" "%~>%" [] (.tuple [configV hn c, w])) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c' :=
  (Classical.choose_spec (stepModel_facts hn hinj host hf hh nd r)).2 c ts w hok hb hw

/-- **`Step_pure` facts are sound for Core**: a `Step_pure` fact of the step model from the code of
a valid `BoundedSel` configuration, to a typed `instr*`, is the image of a Core step that keeps
the state, up to `ConfigEq`. -/
theorem pureFact_sound {c : Config H} {ts : List CValType} (hok : ConfigOk c ts)
    (hb : Round5.Target.BoundedSel c) {js : List Value} (hjs : TypedV EM instrsT (.list js))
    (hp : (SM).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js])) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ cfgV (stateV hn c.store c.frame) js = configV hn d' ∧
      Step (Profile.spec nd r) host c c' :=
  stepFact_sound hok hb (pureFact_obs hok hb hjs hp)

/-- **`Step_read` facts are sound for Core**: a `Step_read` fact of the step model from a valid
`BoundedSel` configuration, to a typed `instr*`, is the image of a Core step that keeps the
state, up to `ConfigEq`. -/
theorem readFact_sound {c : Config H} {ts : List CValType} (hok : ConfigOk c ts)
    (hb : Round5.Target.BoundedSel c) {js : List Value} (hjs : TypedV EM instrsT (.list js))
    (hp : (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ cfgV (stateV hn c.store c.frame) js = configV hn d' ∧
      Step (Profile.spec nd r) host c c' :=
  stepFact_sound hok hb (readFact_obs hok hb hjs hp)

/-- On `DomDet`, a `Step_pure` fact is matched through `toModel` by a Core observation. -/
theorem pureFact_core {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {js : List Value}
    (hjs : TypedV EM instrsT (.list js))
    (hp : (SM).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js])) :
    ∃ b ∈ Atlas.SpecTec.coreObs (Profile.spec nd r) host hn c (),
      Atlas.SpecTec.CfgRel hn b (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨⟨ts, hok⟩, hb, _⟩ := hc.1
  exact bwd_upto (hinj := hinj) (hf := hf) (hh := hh) c hc () _ (pureFact_obs hok hb hjs hp)

/-- On `DomDet`, a `Step_read` fact is matched through `toModel` by a Core observation. -/
theorem readFact_core {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {js : List Value}
    (hjs : TypedV EM instrsT (.list js))
    (hp : (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    ∃ b ∈ Atlas.SpecTec.coreObs (Profile.spec nd r) host hn c (),
      Atlas.SpecTec.CfgRel hn b (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨⟨ts, hok⟩, hb, _⟩ := hc.1
  exact bwd_upto (hinj := hinj) (hf := hf) (hh := hh) c hc () _ (readFact_obs hok hb hjs hp)

end Silmaril.Wasm.SpecTec.Institution.Wasm30

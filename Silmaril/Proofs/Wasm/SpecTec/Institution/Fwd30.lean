module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Fwd30Leaves
public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms

/-!
# The forward direction for `Step_pure` and `Step_read`, in the institution

At every `B`, read in the backend canonical model `stepModel B`:

* `PureHead.step`, `ReadHead.step`: the classified head steps are Core steps that keep the state.
* `pureFact_complete`: a `PureHead is is'` step at typed `is` is a `Step_pure` fact of
  `stepModel B` (`spure_of_pureHead`, transferred by `Round6.Reading.sPureB_iff`).
* `readFact_complete`: a `ReadHead c is'` step between typed configurations is a `Step_read`
  fact (`sread_of_readHead`, transferred by `Round6.Transfer.sReadB_iff_noCast`: `local.get`
  and `global.get` are not cast redexes).
* `pureFact_fwd`, `readFact_fwd`: the same on round 6's domain `Wasm30.Dom`, where typing is
  proved (`Round5.Target.typed_of_configOk_sel`; the successor's validity by Silmaril's
  `Step.preservation` under `HostOk`).

At the primitives of `Wasm30.toModel` (`Wasm30.builtins`), on `Wasm30.DomDet`:

* `pureFact_core_complete`, `readFact_core_complete`: Core's successor of such a step is an
  observation of `toModel`'s source, and its image is a `Step_pure` (`Step_read`) fact of
  `stepModel` that `Step/pure` (`Step/read`) lifts to the matching `Step` fact.
* `pureFact_unique`, `readFact_unique`: with `Wasm30.pureFact_core`, `Wasm30.readFact_core`, every
  `Step_pure` (`Step_read`) fact from such a configuration to typed code is, up to `CfgRel`,
  that successor. So on these steps the relation is exactly Core's head step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Fwd30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel Dom DomDet)

variable {H : Type}

/-! ## The classification is Core's -/

/-- **A `PureHead` step is a Core step** that keeps the state. -/
theorem PureHead.step {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {is is' : List Admin} (h : PureHead is is') : Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | parametric h => exact .parametric h
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse => exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNonNullNull => exact .brOnNonNullNull
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | trapInstrs hne => exact .trapInstrs hne
  | trapLabel => exact .trapLabel
  | trapHandler => exact .trapHandler
  | trapFrame => exact .trapFrame

/-- **A `ReadHead` step is a Core step** that keeps the state. -/
theorem ReadHead.step {P : Profile} {host : HostSemantics H} {c : Config H} {is' : List Admin}
    (h : ReadHead c is') : Step P host c ⟨c.store, c.frame, is'⟩ := by
  cases h with
  | localGet h => exact .variable (.localGet h)
  | globalGet h => exact .variable (.globalGet h)

/-- A single instruction that is neither a value nor a cast is not a cast redex. -/
theorem not_castRedex_single {i : Instr} (hi : Round6.Target.castInstr i = false)
    (hv : ∀ v : Val, v.toAdmin ≠ .plain i) : ¬ Round6.Target.CastRedex [.plain i] := by
  intro h
  generalize hl : [Admin.plain i] = l at h
  cases h with
  | @skip v _ _ => exact hv v (List.cons.inj hl).1.symm
  | @cast i' _ hc =>
    have : i = i' := Admin.plain.inj (List.cons.inj hl).1
    subst this
    rw [hi] at hc
    exact Bool.false_ne_true hc
  | label _ => exact Admin.noConfusion (List.cons.inj hl).1
  | handler _ => exact Admin.noConfusion (List.cons.inj hl).1
  | frame _ => exact Admin.noConfusion (List.cons.inj hl).1

/-- The redex of a `ReadHead` step is not a cast. -/
theorem ReadHead.not_castRedex {c : Config H} {is' : List Admin} (h : ReadHead c is') :
    ¬ Round6.Target.CastRedex c.code := by
  cases h with
  | localGet _ =>
    exact not_castRedex_single rfl fun v => by
      rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin]
  | globalGet _ =>
    exact not_castRedex_single rfl fun v => by
      rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin]

/-! ## Completeness at every `B` -/

/-- **`PureHead` steps are `Step_pure` facts of `stepModel B`**, at typed code. -/
theorem pureFact_complete (B : Builtins) (hn : H → String) {is is' : List Admin}
    (hp : PureHead is is') (h : TypedV (simEnv B) instrsT (.list (adminsToV is))) :
    (stepModel B).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV is), .list (adminsToV is')]) :=
  (Round6.Reading.sPureB_iff B).2 (spure_of_pureHead B hn hp h)

/-- **`ReadHead` steps are `Step_read` facts of `stepModel B`**, between typed configurations. -/
theorem readFact_complete (B : Builtins) (hn : H → String) {c : Config H} {is' : List Admin}
    (hr : ReadHead c is') (hc : Typed (simEnv B) hn c)
    (hc' : Typed (simEnv B) hn ⟨c.store, c.frame, is'⟩) :
    (stepModel B).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) :=
  (Round6.Transfer.sReadB_iff_noCast hr.not_castRedex).2 (sread_of_readHead B hn hr hc hc')

/-- **On round 6's domain, `PureHead` steps are `Step_pure` facts** of every `stepModel B`. -/
theorem pureFact_fwd (B : Builtins) (hn : H → String) {P : Profile} {host : HostSemantics H}
    {c : Config H} (hc : Dom P host c) {is' : List Admin} (hp : PureHead c.code is') :
    (stepModel B).D "Step_pure" "%~>%" []
      (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) := by
  obtain ⟨⟨ts, hok⟩, hb, -⟩ := hc
  exact pureFact_complete B hn hp
    ((Typing.typingFacts_simEnv B hn).config c |>.1
      (Round5.Target.typed_of_configOk_sel B hn hok hb)).2

/-- **On round 6's domain, `ReadHead` steps are `Step_read` facts** of every `stepModel B`, at a
`HostOk` host (for the validity of the successor). -/
theorem readFact_fwd (B : Builtins) (hn : H → String) {P : Profile} {host : HostSemantics H}
    (hh : HostOk host) {c : Config H} (hc : Dom P host c) {is' : List Admin}
    (hr : ReadHead c is') :
    (stepModel B).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) := by
  obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc
  have hs : Step P host c ⟨c.store, c.frame, is'⟩ := hr.step
  exact readFact_complete B hn hr (Round5.Target.typed_of_configOk_sel B hn hok hb)
    (Round5.Target.typed_of_configOk_sel B hn (Step.preservation hh hok hs).1 (hsucc _ hs))

/-! ## Through `Wasm30.toModel`, on `DomDet` -/

section Model

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`. -/
local notation "SM" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- **`PureHead` steps through `toModel`**: on `DomDet`, Core's successor is an observation, and
its image is a `Step_pure` fact of the step model that `Step/pure` lifts to the `Step` fact. -/
theorem pureFact_core_complete {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hp : PureHead c.code is') :
    configV hn ⟨c.store, c.frame, is'⟩ ∈ SpecTec.coreObs (Profile.spec nd r) host hn c () ∧
      (SM).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) ∧
      (SM).D "Step" "%~>%" [] (.tuple [configV hn c, configV hn ⟨c.store, c.frame, is'⟩]) := by
  have hpf := pureFact_fwd (Wasm30.builtins hn hinj host hf hh nd r) hn hc.1 hp
  obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc.1
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact hp.step
  have ht' := (Typing.typingFacts_simEnv (Wasm30.builtins hn hinj host hf hh nd r) hn).config _ |>.1
    (Round5.Target.typed_of_configOk_sel _ hn (Step.preservation hh hok hs).1 (hsucc _ hs))
  exact ⟨⟨_, hs, rfl⟩, hpf, Wasm30.pureFact_obs hok hb ht'.2 hpf⟩

/-- **`ReadHead` steps through `toModel`**: on `DomDet`, Core's successor is an observation, and
its image is a `Step_read` fact of the step model that `Step/read` lifts to the `Step` fact. -/
theorem readFact_core_complete {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hr : ReadHead c is') :
    configV hn ⟨c.store, c.frame, is'⟩ ∈ SpecTec.coreObs (Profile.spec nd r) host hn c () ∧
      (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) ∧
      (SM).D "Step" "%~>%" [] (.tuple [configV hn c, configV hn ⟨c.store, c.frame, is'⟩]) := by
  have hrf := readFact_fwd (Wasm30.builtins hn hinj host hf hh nd r) hn hh hc.1 hr
  obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc.1
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := hr.step
  have ht' := (Typing.typingFacts_simEnv (Wasm30.builtins hn hinj host hf hh nd r) hn).config _ |>.1
    (Round5.Target.typed_of_configOk_sel _ hn (Step.preservation hh hok hs).1 (hsucc _ hs))
  exact ⟨⟨_, hs, rfl⟩, hrf, Wasm30.readFact_obs hok hb ht'.2 hrf⟩

/-- **`Step_pure` at a `PureHead` redex is that step**: on `DomDet`, every `Step_pure` fact from
the code to typed code is, up to `CfgRel`, the `PureHead` successor. -/
theorem pureFact_unique {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hp : PureHead c.code is') {js : List Value}
    (hjs : TypedV (simEnv (Wasm30.builtins hn hinj host hf hh nd r)) instrsT (.list js))
    (hq : (SM).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js])) :
    SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
      (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ :=
    Wasm30.pureFact_core (hinj := hinj) (hf := hf) (hh := hh) hc hjs hq
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact hp.step
  rw [hc.2 _ _ hs₁ hs] at hrel
  exact hrel

/-- **`Step_read` at a `ReadHead` redex is that step**: on `DomDet`, every `Step_read` fact from
the configuration to typed code is, up to `CfgRel`, the `ReadHead` successor. -/
theorem readFact_unique {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hr : ReadHead c is') {js : List Value}
    (hjs : TypedV (simEnv (Wasm30.builtins hn hinj host hf hh nd r)) instrsT (.list js))
    (hq : (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
      (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ :=
    Wasm30.readFact_core (hinj := hinj) (hf := hf) (hh := hh) hc hjs hq
  rw [hc.2 _ _ hs₁ hr.step] at hrel
  exact hrel

end Model

end Silmaril.Wasm.SpecTec.Institution.Fwd30

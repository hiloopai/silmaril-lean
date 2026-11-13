module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30FinLeaves
public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Thms
public import Silmaril.Wasm.SpecTec.Institution.Nondet.Thms
public import Silmaril.Wasm.SpecTec.Institution.Cover.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms

/-!
# The forward direction at wasm-3.0, finished: in the institution

At the concrete primitives `Round4Int.BI`, the model of `Cover.toModelDom`:

* `CastRead.step`, `RetFrameAddr.step`: the nine head steps are Core steps that keep the state.
* `readFactCast_complete`, `readFactCast_dom`: a `CastRead` step is a `Step_read` fact of
  `stepModel BI` (from a bounded configuration with `CastsInv`, typed; on `Dom`, unconditionally).
* `readFactRet_complete`, `readFactRet_dom`: for `RetFrameAddr`, a `Step_read` fact up to
  `ConfigEq`: to a code `CodeEq` to Core's successor code.
* `readFactCast_core_complete`, `readFactRet_core_complete`: on `Dom` at a spec profile, Core's
  successor is an observation, and (up to `ConfigEq` for `RetFrameAddr`) its image is the
  `Step_read` fact, lifted by `Step/read` to the `Step` fact.
* `readFactCast_unique`, `readFactRet_unique`: on `DomDet`, every `Step_read` fact to typed code is
  the classified successor up to `CfgRel` (soundness is `FwdX30.readFactX_sound`, which holds of
  every `Step_read` fact).

Through `Wasm30.toModel`, at the choice-made primitives `Wasm30.builtins`:

* `sat_builtins_iff_BI`: on `DomDet`, `modelChart (stepModel builtins)` and
  `modelChart (stepModel BI)` satisfy the same `CfgRel`-respecting sentences at `configV c`
  (both are `equal` to Core: `Wasm30.sat_iff_stepModel`, `Cover.sat_iff_dom`).
* `stepObs_builtins`: on `DomDet`, the `Step` observations of `stepModel builtins` at `configV c`
  are exactly the image of Core's unique successor, up to `CfgRel`.
* `pureFactX_builtins`, `readFactX_builtins`, `readFactCast_builtins`, `readFactRet_builtins`:
  for each classified redex on `DomDet`, the `Step_pure`/`Step_read` fact of `stepModel BI`
  together with the `Step` observations of `stepModel builtins`, which are the classified
  successor up to `CfgRel`.

* `pureFact_unique_builtins`, `readFact_unique_builtins`: on `DomDet`, every `Step_pure`
  (`Step_read`) fact of `stepModel builtins` to typed code is Core's successor up to `CfgRel`
  (instantiate `hs` with `PureHeadX.step`, `ReadHeadX.step`, `CastRead.step`, `RetFrameAddr.step`).

Not restated at `builtins`: that the `Step_pure`/`Step_read` facts exist. `builtins` is a
`Classical.choose` constrained only by its `Step` facts on `DomDet`, so nothing is known of its
primitives, and these relations call them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30Fin

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel modelChart Dom DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdX30 (PureHeadX ReadHeadX)
open Round4Int (BI)

variable {H : Type}

/-! ## The classification is Core's -/

/-- **A `CastRead` step is a Core step** that keeps the state. -/
theorem CastRead.step {P : Profile} {host : HostSemantics H} {c : Config H} {is' : List Admin}
    (h : CastRead c is') : Step P host c ⟨c.store, c.frame, is'⟩ := by
  unfold CastRead at h
  generalize hc' : (⟨c.store, c.frame, is'⟩ : Config H) = c' at h ⊢
  cases h with
  | testTrue h => exact .reference (.testTrue h)
  | testFalse h => exact .reference (.testFalse h)
  | castSucceed h => exact .reference (.castSucceed h)
  | castFail h => exact .reference (.castFail h)
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h

/-- **A `RetFrameAddr` step is a Core step** that keeps the state. -/
theorem RetFrameAddr.step {P : Profile} {host : HostSemantics H} {c : Config H}
    {is' : List Admin} (h : RetFrameAddr c is') : Step P host c ⟨c.store, c.frame, is'⟩ := by
  cases h with
  | mk hc hf he hn => exact .returnCallRefFrameAddr hc hf he hn

/-! ## Completeness at `BI` -/

section Complete

variable {P : Profile} (hn : H → String) (host : HostSemantics H)

/-- **`CastRead` steps are `Step_read` facts of `stepModel BI`**, from a typed, bounded
configuration with `CastsInv`. -/
theorem readFactCast_complete {c : Config H} {is' : List Admin} (h : CastRead c is')
    (hb : Round4.Bounded c) (hI : Round6.CastsV.CastsInv c)
    (hc : Typed (simEnv (BI P hn host)) hn c) :
    (stepModel (BI P hn host)).D "Step_read" "%~>%" []
      (.tuple [configV hn c, .list (adminsToV is')]) :=
  have ht := ((Typing.typingFacts_simEnv (BI P hn host) hn).config c).1 hc
  sreadB_of_castRead hn host h hb hI ht.1 ht.2

/-- **`RetFrameAddr` steps are `Step_read` facts of `stepModel BI` up to `ConfigEq`**, from a
typed, bounded configuration. -/
theorem readFactRet_complete {c : Config H} {is' : List Admin} (h : RetFrameAddr c is')
    (hb : Round4.Bounded c) (hc : Typed (simEnv (BI P hn host)) hn c) :
    ∃ is'', Bwd.CodeEq is' is'' ∧ (stepModel (BI P hn host)).D "Step_read" "%~>%" []
      (.tuple [configV hn c, .list (adminsToV is'')]) :=
  have ht := ((Typing.typingFacts_simEnv (BI P hn host) hn).config c).1 hc
  sreadB_retFrameAddr hn host h hb.storeBnd ht.1 ht.2

/-- **On round 6's domain, `CastRead` steps are `Step_read` facts** of `stepModel BI`. -/
theorem readFactCast_dom {c : Config H} (hc : Dom P host c) {is' : List Admin}
    (h : CastRead c is') :
    (stepModel (BI P hn host)).D "Step_read" "%~>%" []
      (.tuple [configV hn c, .list (adminsToV is')]) := by
  obtain ⟨⟨ts, hok⟩, hb, -⟩ := hc
  exact readFactCast_complete hn host h hb.1.1 (Round6.CastsV.castsInv_of_configOk hok)
    (Round5.Target.typed_of_configOk_sel _ hn hok hb)

/-- **On round 6's domain, `RetFrameAddr` steps are `Step_read` facts** of `stepModel BI`, up to
`ConfigEq`. -/
theorem readFactRet_dom {c : Config H} (hc : Dom P host c) {is' : List Admin}
    (h : RetFrameAddr c is') :
    ∃ is'', Bwd.CodeEq is' is'' ∧ (stepModel (BI P hn host)).D "Step_read" "%~>%" []
      (.tuple [configV hn c, .list (adminsToV is'')]) := by
  obtain ⟨⟨ts, hok⟩, hb, -⟩ := hc
  exact readFactRet_complete hn host h hb.1.1 (Round5.Target.typed_of_configOk_sel _ hn hok hb)

end Complete

/-! ## Through `Cover.toModelDom`, on `Dom` -/

section Model

variable {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Cover.toModelDom`. -/
local notation "SM" => stepModel (BI (Profile.spec nd r) hn host)

/-- The environment of that model. -/
local notation "EM" => simEnv (BI (Profile.spec nd r) hn host)

/-- **`CastRead` steps through `Cover.toModelDom`**: on `Dom`, Core's successor is an
observation, and its image is a `Step_read` fact that `Step/read` lifts to the `Step` fact. -/
theorem readFactCast_core_complete (hh : HostOk host) {c : Config H}
    (hc : Dom (Profile.spec nd r) host c) {is' : List Admin} (h : CastRead c is') :
    configV hn ⟨c.store, c.frame, is'⟩ ∈ SpecTec.coreObs (Profile.spec nd r) host hn c () ∧
      (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) ∧
      (SM).D "Step" "%~>%" [] (.tuple [configV hn c, configV hn ⟨c.store, c.frame, is'⟩]) := by
  have hrf := readFactCast_dom hn host hc h
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := h.step
  obtain ⟨⟨hz, hcode⟩, hcode'⟩ := FwdX30.typed_succ hh hc hs
  exact ⟨⟨_, hs, rfl⟩, hrf,
    Round6.Reading.sstepB_read (hasStepRules_simEnv _).read hz hcode hcode' hrf⟩

/-- **`RetFrameAddr`, typed**: from a typed configuration with a bounded store whose Core
successor is typed, SpecTec's successor code is `CodeEq` to Core's, typed, and a `Step_read`
fact of `stepModel BI`. -/
theorem typed_retFrameAddr {c : Config H} {is' : List Admin} (h : RetFrameAddr c is')
    (hbs : Round4.StoreBnd c.store) (hc : Typed EM hn c)
    (hc' : Typed EM hn ⟨c.store, c.frame, is'⟩) :
    ∃ is'', Bwd.CodeEq is' is'' ∧ Typed EM hn ⟨c.store, c.frame, is''⟩ ∧
      (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is'')]) := by
  have T := Typing.typingFacts_simEnv (BI (Profile.spec nd r) hn host) hn
  have Tg := Typing.ctrlTyping_simEnv (BI (Profile.spec nd r) hn host)
  have ht := (T.config c).1 hc
  cases h with
  | @mk s f fi k vs' vs a c₀ rest fn ps rs hc₀ hfn hex hlen =>
    obtain ⟨yy, hyy, hyy'⟩ := adminToV_retToCall hc₀
    have hy := Bwd.typed_retAnnot _ T Tg hyy hc
    exact ⟨_, Bwd.codeEq_retToCall hc₀ fi.module vs a,
      Bwd.typed_retToCall _ T (FwdMem.callRefTyping_simEnv _) hyy' hy hc',
      (Round6.Transfer.sReadB_iff_noCast (not_castRedex_retFrameAddr hc₀)).2
        (sread_retFrameAddr hn host hc₀ hfn hex hlen (Round5.Fwd.tyBnd_funcType hbs hfn) ht.1
          ht.2)⟩

/-- **`RetFrameAddr` steps through `Cover.toModelDom`, up to `ConfigEq`**: on `Dom`, Core's
successor is an observation; a configuration `ConfigEq` to it (SpecTec's, with the `CALL_REF`
index kept) has a `Step_read` fact as code, which `Step/read` lifts to the `Step` fact. -/
theorem readFactRet_core_complete (hh : HostOk host) {c : Config H}
    (hc : Dom (Profile.spec nd r) host c) {is' : List Admin} (h : RetFrameAddr c is') :
    configV hn ⟨c.store, c.frame, is'⟩ ∈ SpecTec.coreObs (Profile.spec nd r) host hn c () ∧
      ∃ is'', Bwd.ConfigEq ⟨c.store, c.frame, is'⟩ ⟨c.store, c.frame, is''⟩ ∧
        (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is'')]) ∧
        (SM).D "Step" "%~>%" [] (.tuple [configV hn c, configV hn ⟨c.store, c.frame, is''⟩]) := by
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := h.step
  obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := id hc
  have htc := Round5.Target.typed_of_configOk_sel (BI (Profile.spec nd r) hn host) hn hok hb
  have htc' := Round5.Target.typed_of_configOk_sel (BI (Profile.spec nd r) hn host) hn (Step.preservation hh hok hs).1
    (hsucc _ hs)
  obtain ⟨is'', he, ht'', hrf⟩ := typed_retFrameAddr h hb.1.1.storeBnd htc htc'
  have T := Typing.typingFacts_simEnv (BI (Profile.spec nd r) hn host) hn
  have hz := ((T.config c).1 htc)
  exact ⟨⟨_, hs, rfl⟩, is'', ⟨rfl, rfl, he⟩, hrf,
    Round6.Reading.sstepB_read (hasStepRules_simEnv _).read hz.1 hz.2 ((T.config _).1 ht'').2 hrf⟩

/-- **`Step_read` at a `CastRead` redex is that step**, on `DomDet`: every `Step_read` fact of
`stepModel BI` from the configuration to typed code is the classified successor up to
`CfgRel`. -/
theorem readFactCast_unique (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (h : CastRead c is') {js : List Value} (hjs : TypedV EM instrsT (.list js))
    (hq : (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
      (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ := FwdX30.readFactX_sound hinj hf hh hc.1 hjs hq
  rw [hc.2 _ _ hs₁ h.step] at hrel
  exact hrel

/-- **`Step_read` at a `RetFrameAddr` redex is that step**, on `DomDet`, up to `CfgRel`. -/
theorem readFactRet_unique (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (h : RetFrameAddr c is') {js : List Value} (hjs : TypedV EM instrsT (.list js))
    (hq : (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
      (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ := FwdX30.readFactX_sound hinj hf hh hc.1 hjs hq
  rw [hc.2 _ _ hs₁ h.step] at hrel
  exact hrel

end Model

/-! ## Through `Wasm30.toModel`, at the choice-made primitives -/

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- The step model of `Cover.toModelDom`, at the concrete primitives. -/
local notation "SI" => stepModel (BI (Profile.spec nd r) hn host)

/-- **The two models agree on `DomDet`**: `stepModel builtins` (the target of `Wasm30.toModel`)
and `stepModel BI` (the target of `Cover.toModelDom`) satisfy the same `CfgRel`-respecting
sentences at the image of a point of `DomDet`, since both transitions are `equal`. -/
theorem sat_builtins_iff_BI {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {s : BSen Unit Value} (hs : s.Respects (SpecTec.CfgRel hn)) :
    (modelChart (SB)).Sat (configV hn c) s ↔ (modelChart (SI)).Sat (configV hn c) s :=
  (Wasm30.sat_iff_stepModel hn hinj host hf hh nd r hc hs).symm.trans
    (Cover.sat_iff_dom hinj hf hh hc.1 hs)

/-- **The `Step` observations of `stepModel builtins` on `DomDet`** are Core's successor, up to
`CfgRel`: there is one, and every one is related to it. -/
theorem stepObs_builtins {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') :
    (∃ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) ∧
        SpecTec.CfgRel hn (configV hn c') w) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) →
        SpecTec.CfgRel hn (configV hn c') w := by
  refine ⟨?_, fun w hw => ?_⟩
  · obtain ⟨w, hw, hrel⟩ :=
      Wasm30.fwd_upto (hinj := hinj) (hf := hf) (hh := hh) c hc () _ ⟨c', hs, rfl⟩
    exact ⟨w, hw, hrel⟩
  · obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ :=
      Wasm30.bwd_upto (hinj := hinj) (hf := hf) (hh := hh) c hc () w hw
    rw [hc.2 _ _ hs₁ hs] at hrel
    exact hrel

/-- **`PureHeadX` at both models**: on `DomDet`, the redex's successor is a `Step_pure` fact of
`stepModel BI`, and the `Step` observations of `stepModel builtins` are that successor up to
`CfgRel`. -/
theorem pureFactX_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hp : PureHeadX (Profile.spec nd r) c.code is') :
    (SI).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) ∧
      (∃ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) ∧
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w := by
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact hp.step
  exact ⟨FwdX30.pureFactX_dom hn host hc.1 hp, stepObs_builtins hc hs⟩

/-- **`ReadHeadX` at both models**: on `DomDet`, the successor is a `Step_read` fact of
`stepModel BI`, and the `Step` observations of `stepModel builtins` are it up to `CfgRel`. -/
theorem readFactX_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hr : ReadHeadX (Profile.spec nd r) c is') :
    (SI).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) ∧
      (∃ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) ∧
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w :=
  ⟨FwdX30.readFactX_dom hn host hh hc.1 hr, stepObs_builtins hc hr.step⟩

/-- **`CastRead` at both models**: on `DomDet`, the successor is a `Step_read` fact of
`stepModel BI`, and the `Step` observations of `stepModel builtins` are it up to `CfgRel`. -/
theorem readFactCast_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (h : CastRead c is') :
    (SI).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) ∧
      (∃ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) ∧
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w :=
  ⟨readFactCast_dom hn host hc.1 h, stepObs_builtins hc h.step⟩

/-- **`RetFrameAddr` at both models**: on `DomDet`, a code `CodeEq` to the successor's is a
`Step_read` fact of `stepModel BI`, and the `Step` observations of `stepModel builtins` are the
successor up to `CfgRel`. -/
theorem readFactRet_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (h : RetFrameAddr c is') :
    (∃ is'', Bwd.CodeEq is' is'' ∧
      (SI).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is'')])) ∧
      (∃ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) ∧
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w) ∧
      ∀ w, (SB).D "Step" "%~>%" [] (.tuple [configV hn c, w]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) w :=
  ⟨readFactRet_dom hn host hc.1 h, stepObs_builtins hc h.step⟩

/-- **`Step_pure` facts of `stepModel builtins` at a classified redex are its successor**: on
`DomDet`, every `Step_pure` fact from the code of `c` to typed code is, up to `CfgRel`, the image
of Core's successor (`Wasm30.pureFact_core` and determinism). Only existence is not known at
`builtins`. -/
theorem pureFact_unique_builtins {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') {js : List Value}
    (hjs : TypedV (simEnv (Wasm30.builtins hn hinj host hf hh nd r)) instrsT (.list js))
    (hq : (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js])) :
    SpecTec.CfgRel hn (configV hn c') (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ := Wasm30.pureFact_core (hinj := hinj) (hf := hf) (hh := hh)
    hc hjs hq
  rw [hc.2 _ _ hs₁ hs] at hrel
  exact hrel

/-- **`Step_read` facts of `stepModel builtins` at a classified redex are its successor**: on
`DomDet`, every `Step_read` fact from `c` to typed code is, up to `CfgRel`, the image of Core's
successor (`Wasm30.readFact_core` and determinism). -/
theorem readFact_unique_builtins {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') {js : List Value}
    (hjs : TypedV (simEnv (Wasm30.builtins hn hinj host hf hh nd r)) instrsT (.list js))
    (hq : (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    SpecTec.CfgRel hn (configV hn c') (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ := Wasm30.readFact_core (hinj := hinj) (hf := hf) (hh := hh)
    hc hjs hq
  rw [hc.2 _ _ hs₁ hs] at hrel
  exact hrel

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdX30Fin

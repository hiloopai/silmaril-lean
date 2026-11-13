module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30Ctrl
public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Thms
public import Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.Thms

/-!
# The forward direction at the choice-made primitives `Wasm30.builtins`

* `PureG.toX`, `ReadG.toX`: the primitive-free rules are among `FwdX30`'s classification.
* `spure_of_pureG`, `sread_of_readG`: at **every** evaluator `simEnv B`, a `PureG` step at typed
  code is an `SPure` fact, and a `ReadG` step from a typed state and code to typed code is an
  `SRead` fact. The arms are those of `FwdX30.spure_of_pureHeadX` and
  `FwdX30.sread_of_ctrlRead` whose leaves need no law of the primitives.
* `pureG_builtins`, `readG_builtins`: on `DomDet`, at `Wasm30.builtins` (the target of
  `Wasm30.toModel`), Core's successor of a `PureG` (`ReadG`) redex is a `Step_pure`
  (`Step_read`) fact of `stepModel builtins`, which `Step/pure` (`Step/read`) lifts to the
  `Step` fact. This is the existence half that `FwdX30Fin` left open.
* `pureG_two_sided`, `readG_two_sided`: with `FwdX30Fin.pureFact_unique_builtins` and
  `readFact_unique_builtins`, at these redexes the `Step_pure` (`Step_read`) facts of
  `stepModel builtins` to typed code are exactly Core's successor up to `CfgRel`, and it is one.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdX30 (PureHeadX ReadHeadX CtrlRead)

variable {H : Type}

/-! ## Inside the classification -/

/-- The primitive-free `Step_pure` rules are `PureHeadX` rules. -/
theorem PureG.toX {P : Profile} {is is' : List Admin} (h : PureG is is') : PureHeadX P is is' := by
  cases h with
  | isNullTrue => exact .isNullTrue
  | isNullFalse h => exact .isNullFalse h
  | asNonNullNull => exact .asNonNullNull
  | asNonNullAddr h => exact .asNonNullAddr h
  | eqNull => exact .eqNull
  | eqTrue h => exact .eqTrue h
  | eqFalse h => exact .eqFalse h
  | i31GetNull sx => exact .i31GetNull sx
  | externConvertNull => exact .externConvertNull
  | externConvertAddr h => exact .externConvertAddr h
  | anyConvertNull => exact .anyConvertNull
  | anyConvertAddr r => exact .anyConvertAddr r
  | arrayNew v n => exact .arrayNew v n
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | localTee => exact .localTee
  | handlerVals => exact .handlerVals

/-- The primitive-free `Step_read` rules are `ReadHeadX` rules. -/
theorem ReadG.toX {P : Profile} {c : Config H} {is' : List Admin} (h : ReadG c is') :
    ReadHeadX P c is' := by
  cases h with
  | refNull ht => exact .refNull ht
  | call hx hf => exact .ctrl (.call hx hf)
  | returnCall hx hf => exact .ctrl (.returnCall hx hf)
  | returnCallRefLabel hc => exact .ctrl (.returnCallRefLabel hc)
  | returnCallRefHandler hc => exact .ctrl (.returnCallRefHandler hc)
  | returnCallRefFrameNull hc => exact .ctrl (.returnCallRefFrameNull hc)
  | throwRefNull => exact .ctrl .throwRefNull
  | throwRefInstrs hne => exact .ctrl (.throwRefInstrs hne)
  | throwRefLabel => exact .ctrl .throwRefLabel
  | throwRefFrame => exact .ctrl .throwRefFrame
  | throwRefHandlerEmpty => exact .ctrl .throwRefHandlerEmpty
  | throwRefHandlerCatchAll => exact .ctrl .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .ctrl .throwRefHandlerCatchAllRef

/-! ## At every `B` -/

/-- **`PureG` steps are `Step_pure` facts at every `B`**, at typed code. -/
theorem spure_of_pureG (B : Builtins) (hn : H → String) {is is' : List Admin} (hp : PureG is is')
    (hc : TypedV (simEnv B) instrsT (.list (adminsToV is))) :
    SPure (simEnv B) (adminsToV is) (adminsToV is') := by
  have T : TypingFacts (simEnv B) hn := Typing.typingFacts_simEnv B hn
  have R : RefsGC.RTyping (simEnv B) := Typing.rTyping_simEnv B
  have rr : Equiv.ExecRef.HasRefRules (envOfScript Specs.wasm30) := Equiv.ExecRef.hasRefRules_wasm30
  have pt : ((RefsGC.relRules (simEnv B) "Step_pure").map RefsGC.ruleTags).take 46 =
      RefsGC.pureTagTable := RefsGC.pureTable_simEnv B
  cases hp with
  | isNullTrue =>
    exact RefsGC.spure_isNullTrue (RefsGC.refRule _ rr.refIsNullTrue)
      (R.ref _ (RefsGC.typed_head T hc))
  | isNullFalse hr =>
    exact RefsGC.spure_isNullFalse (RefsGC.refRule _ rr.refIsNullFalse)
      (RefsGC.refRule _ rr.refIsNullTrue) pt hr (R.ref _ (RefsGC.typed_head T hc))
  | asNonNullNull =>
    exact RefsGC.spure_asNonNullNull (RefsGC.refRule _ rr.refAsNonNullNull)
      (R.ref _ (RefsGC.typed_head T hc))
  | asNonNullAddr hr =>
    exact RefsGC.spure_asNonNullAddr (RefsGC.refRule _ rr.refAsNonNullAddr)
      (RefsGC.refRule _ rr.refAsNonNullNull) pt hr (R.ref _ (RefsGC.typed_head T hc))
  | eqNull =>
    exact RefsGC.spure_eqNull (RefsGC.refRule _ rr.refEqNull) (R.ref _ (RefsGC.typed_head T hc))
  | eqTrue hr =>
    exact RefsGC.spure_eqTrue (RefsGC.refRule _ rr.refEqTrue) (RefsGC.refRule _ rr.refEqNull) pt hr
      (R.ref _ (RefsGC.typed_head T hc))
  | eqFalse hr =>
    exact RefsGC.spure_eqFalse (RefsGC.refRule _ rr.refEqFalse) (RefsGC.refRule _ rr.refEqNull)
      (RefsGC.refRule _ rr.refEqTrue) pt hr (R.ref _ (RefsGC.typed_head T hc))
      (R.ref _ (RefsGC.typed_head T (RefsGC.typed_tail T hc)))
  | i31GetNull sx => exact RefsGC.spure_i31GetNull (RefsGC.refRule _ rr.i31GetNull) R sx
  | externConvertNull =>
    exact RefsGC.spure_externConvertNull (RefsGC.refRule _ rr.externConvertAnyNull)
      (R.ref _ (RefsGC.typed_head T hc))
  | externConvertAddr hr =>
    exact RefsGC.spure_externConvertAddr (RefsGC.refRule _ rr.externConvertAnyAddr)
      (RefsGC.refRule _ rr.externConvertAnyNull) pt hr (R.ref _ (RefsGC.typed_head T hc))
  | anyConvertNull => exact RefsGC.spure_anyConvertNull (RefsGC.refRule _ rr.anyConvertExternNull)
  | anyConvertAddr r =>
    exact RefsGC.spure_anyConvertAddr (RefsGC.refRule _ rr.anyConvertExternAddr)
      (R.externArg r (RefsGC.typed_head T hc))
  | arrayNew v n =>
    exact Aggregates.spure_arrayNew
      (hasRuleAt_simEnv _ Equiv.ExecPureArrayNew.hasArrayNew_wasm30) T R v n hc
  | brOnNullAddr hv => exact FwdX30.spure_brOnNullAddrH B hn hv hc
  | brOnNonNullAddr hv => exact FwdX30.spure_brOnNonNullAddrH B hn hv hc
  | localTee => exact FwdX30.spure_localTeeH B hn hc
  | handlerVals => exact FwdX30.spure_handlerValsH B hn hc

/-- **`ReadG` steps are `Step_read` facts at every `B`**, from a typed state and code to typed
code. -/
theorem sread_of_readG (B : Builtins) (hn : H → String) {c : Config H} {is' : List Admin}
    (hr : ReadG c is') (hz : TypedV (simEnv B) stateT (stateV hn c.store c.frame))
    (his : TypedV (simEnv B) instrsT (.list (adminsToV c.code))) :
    SRead (simEnv B) (configV hn c) (adminsToV is') := by
  have T : TypingFacts (simEnv B) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv B) := Typing.rTyping_simEnv B
  have X : Exn.Typing (simEnv B) := Typing.exnTyping_simEnv' _
  have Rd : Equiv.ExecRead.HasReadRules (simEnv B) := Exn.hasReadRules_simEnv _
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  cases hr with
  | refNull ht => exact RefsGC.sread_refNull (hasRuleAt_simEnv _ rd.refNull) R hz his
  | call hx hf => exact sreadC_call B hn hx hf hz
  | returnCall hx hf => exact sreadC_returnCall B hn hx hf hz
  | returnCallRefLabel hc => exact sreadC_returnCallRefLabel B hn hc hz his
  | returnCallRefHandler hc => exact sreadC_returnCallRefHandler B hn hc hz his
  | returnCallRefFrameNull hc => exact sreadC_returnCallRefFrameNull B hn hc hz his
  | throwRefNull => exact Exn.sread_throwRefNull Rd.throwRefNull hz
  | throwRefInstrs hne => exact sreadC_throwRefInstrs B hn hne hz his
  | @throwRefLabel s f n cont a =>
    exact Exn.sread_throwRefLabel Rd.throwRefLabel hz (T.label n cont _ his).1
      (T.label n cont _ his).2.1 (X.addr a)
  | @throwRefFrame s f fi n a =>
    exact Exn.sread_throwRefFrame Rd.throwRefFrame hz (T.frame n fi _ his).1
      (T.frame n fi _ his).2.1 (X.addr a)
  | @throwRefHandlerEmpty s f n a =>
    exact Exn.sread_throwRefHandlerEmpty Rd.throwRefHandlerEmpty hz (T.handler n [] _ his).1
      (X.addr a)
  | @throwRefHandlerCatchAll s f n l cs a =>
    exact Exn.sread_throwRefHandlerCatchAll Rd.throwRefHandlerCatchAll hz (T.handler n _ _ his).1
      (X.labelidx l) (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a)
  | @throwRefHandlerCatchAllRef s f n l cs a =>
    exact Exn.sread_throwRefHandlerCatchAllRef Rd.throwRefHandlerCatchAllRef hz
      (T.handler n _ _ his).1 (X.labelidx l) (X.catch_ _ cs (T.handler n _ _ his).2.1).2 (X.addr a)

/-! ## At `Wasm30.builtins` -/

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- On `DomDet`, the state and code of `c` and the code of a successor are typed in `EB`. -/
theorem typed_builtins {c c' : Config H} (hc : DomDet (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') :
    (TypedV EB stateT (stateV hn c.store c.frame) ∧ TypedV EB instrsT (.list (adminsToV c.code))) ∧
      TypedV EB instrsT (.list (adminsToV c'.code)) := by
  obtain ⟨⟨⟨ts, hok⟩, hb, hsucc⟩, -⟩ := hc
  have T := Typing.typingFacts_simEnv (Wasm30.builtins hn hinj host hf hh nd r) hn
  exact ⟨(T.config c).1 (Round5.Target.typed_of_configOk_sel _ hn hok hb),
    ((T.config c').1 (Round5.Target.typed_of_configOk_sel _ hn
      (Step.preservation hh hok hs).1 (hsucc _ hs))).2⟩

/-- **Existence at `builtins` for `PureG`**: on `DomDet`, Core's successor of a `PureG` redex is a
`Step_pure` fact of `stepModel builtins`, and `Step/pure` lifts it to the `Step` fact. -/
theorem pureG_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hp : PureG c.code is') :
    (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) ∧
      (SB).D "Step" "%~>%" [] (.tuple [configV hn c, configV hn ⟨c.store, c.frame, is'⟩]) := by
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact (hp.toX (P := Profile.spec nd r)).step
  obtain ⟨⟨hz, hcode⟩, hcode'⟩ := typed_builtins hc hs
  have hpf : (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) :=
    (Round6.Reading.sPureB_iff _).2 (spure_of_pureG _ hn hp hcode)
  exact ⟨hpf, Round6.Reading.sstepB_pure (hasStepRules_simEnv _).pure hz hcode hcode' hpf⟩

/-- **Existence at `builtins` for `ReadG`**: on `DomDet`, Core's successor of a `ReadG` redex is a
`Step_read` fact of `stepModel builtins`, and `Step/read` lifts it to the `Step` fact. -/
theorem readG_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadG c is') :
    (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) ∧
      (SB).D "Step" "%~>%" [] (.tuple [configV hn c, configV hn ⟨c.store, c.frame, is'⟩]) := by
  have hx : ReadHeadX (Profile.spec nd r) c is' := hr.toX
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := hx.step
  obtain ⟨⟨hz, hcode⟩, hcode'⟩ := typed_builtins hc hs
  have hrf : (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) :=
    (Round6.Transfer.sReadB_iff_noCast hx.not_castRedex).2 (sread_of_readG _ hn hr hz hcode)
  exact ⟨hrf, Round6.Reading.sstepB_read (hasStepRules_simEnv _).read hz hcode hcode' hrf⟩

/-- **`Step_pure` at `builtins` is two-sided at `PureG` redexes**: on `DomDet`, Core's successor
is a `Step_pure` fact of `stepModel builtins`, and every `Step_pure` fact from the code to typed
code is that successor up to `CfgRel`. -/
theorem pureG_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hp : PureG c.code is') :
    (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) (cfgV (stateV hn c.store c.frame) js) := by
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact (hp.toX (P := Profile.spec nd r)).step
  exact ⟨(pureG_builtins hc hp).1, fun _ hjs hq => FwdX30Fin.pureFact_unique_builtins hc hs hjs hq⟩

/-- **`Step_read` at `builtins` is two-sided at `ReadG` redexes**: on `DomDet`, Core's successor
is a `Step_read` fact of `stepModel builtins`, and every `Step_read` fact from `c` to typed code is
that successor up to `CfgRel`. -/
theorem readG_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadG c is') :
    (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩) (cfgV (stateV hn c.store c.frame) js) :=
  ⟨(readG_builtins hc hr).1, fun _ hjs hq =>
    FwdX30Fin.readFact_unique_builtins hc (hr.toX (P := Profile.spec nd r)).step hjs hq⟩

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30

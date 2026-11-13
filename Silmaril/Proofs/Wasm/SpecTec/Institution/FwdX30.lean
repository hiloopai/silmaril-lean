module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdX30Leaves
public import Silmaril.Wasm.SpecTec.Institution.Fwd30.Thms
public import Silmaril.Wasm.SpecTec.Institution.Nondet.Thms
public import Silmaril.Wasm.SpecTec.Institution.Cover.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms

/-!
# The forward direction at wasm-3.0, extended: in the institution

Read in the backend canonical model `stepModel (BI P hn host)` at the concrete primitives
`Round4Int.BI`, the model of `Cover.toModelDom` (the `equal` transition on all 's
domain `Wasm30.Dom`):

* `PureHeadX.step`, `ReadHeadX.step`: the classified head steps are Core steps that keep the
  state.
* `pureFactX_complete`, `readFactX_complete`: such a step at typed code (for `Step_read`, from a
  typed, bounded configuration to typed code) is a `Step_pure` (`Step_read`) fact of
  `stepModel BI`
  (`spure_of_pureHeadX`, `sread_of_readHeadX`, transferred by `Round6.Reading.sPureB_iff` and
  `Round6.Transfer.sReadB_iff_noCast`: no `ReadHeadX` redex is a cast redex,
  `ReadHeadX.not_castRedex`).
* `pureFactX_dom`, `readFactX_dom`: on `Dom`, where typing is proved.
* `pureFactX_core_complete`, `readFactX_core_complete`: at a spec profile, on `Dom` (no
  determinism), Core's successor is an observation of the Core step chart, and its image is the
  `Step_pure` (`Step_read`) fact, which `Step/pure` (`Step/read`) lifts to the `Step` fact.
* `pureFactX_sound`, `readFactX_sound`: on `Dom`, every `Step_pure` (`Step_read`) fact of
  `stepModel BI` to typed code is, up to `CfgRel`, a Core successor (`Nondet.halves_BI`).
* `pureFactX_unique`, `readFactX_unique`: on `DomDet`, it is the classified successor.

The numeric family is not deterministic in Core (NaN payloads): `pureFactX_core_complete` gives
each Core successor as a fact, on all of `Dom`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel Dom DomDet)
open Round4Int (BI)

variable {H : Type}

/-! ## The classification is Core's -/

/-- **A `PureHeadX` step is a Core step** that keeps the state. -/
theorem PureHeadX.step {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {is is' : List Admin} (h : PureHeadX P is is') : Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases h with
  | numeric h => exact .numeric h
  | vector h _ => exact .vector h
  | refI31 i => exact .reference (.refI31 i)
  | isNullTrue => exact .reference .isNullTrue
  | isNullFalse h => exact .reference (.isNullFalse h)
  | asNonNullNull => exact .reference .asNonNullNull
  | asNonNullAddr h => exact .reference (.asNonNullAddr h)
  | eqNull => exact .reference .eqNull
  | eqTrue h => exact .reference (.eqTrue h)
  | eqFalse h => exact .reference (.eqFalse h)
  | i31GetNull sx => exact .reference (.i31GetNull sx)
  | i31GetNum sx i => exact .reference (.i31GetNum sx i)
  | externConvertNull => exact .reference .externConvertNull
  | externConvertAddr h => exact .reference (.externConvertAddr h)
  | anyConvertNull => exact .reference .anyConvertNull
  | anyConvertAddr r => exact .reference (.anyConvertAddr r)
  | arrayNew v n => exact .aggregate (.arrayNew v n)
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | localTee => exact .variable .localTee
  | handlerVals => exact .handlerVals

/-- **A `CtrlRead` step is a Core step** that keeps the state. -/
theorem CtrlRead.step {P : Profile} {host : HostSemantics H} {c : Config H} {is' : List Admin}
    (h : CtrlRead c is') : Step P host c ⟨c.store, c.frame, is'⟩ := by
  cases h with
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | call hx hf => exact .call hx hf
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hc => exact .returnCallRefLabel hc
  | returnCallRefHandler hc => exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact .returnCallRefFrameNull hc
  | throwRefNull => exact .throwRefNull
  | throwRefInstrs hne => exact .throwRefInstrs hne
  | throwRefLabel => exact .throwRefLabel
  | throwRefFrame => exact .throwRefFrame
  | throwRefHandlerEmpty => exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext hnm => exact .throwRefHandlerNext hnm
  | tryTable hbt hm => exact .tryTable hbt hm

/-- **A `ReadHeadX` step is a Core step** that keeps the state. -/
theorem ReadHeadX.step {P : Profile} {host : HostSemantics H} {c : Config H} {is' : List Admin}
    (h : ReadHeadX P c is') : Step P host c ⟨c.store, c.frame, is'⟩ := by
  cases h with
  | refNull ht => exact .reference (.refNull ht)
  | refFunc h => exact .reference (.refFunc h)
  | table h => exact .table h.1
  | memory h => exact .memory h.1
  | aggregate h => exact .aggregate h.1
  | ctrl h => exact h.step

/-- An administrative instruction that cannot start a cast redex. -/
def noCastAdmin : Admin → Bool
  | .plain i => !Round6.Target.castInstr i
  | .label .. | .handler .. | .frame .. => false
  | _ => true

/-- A value cannot start a cast redex. -/
theorem noCastAdmin_toAdmin (v : Val) : noCastAdmin v.toAdmin = true := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> rfl

/-- Code none of whose instructions can start a cast redex is not a cast redex. -/
theorem not_castRedex_of_all {is : List Admin} (h : ∀ a ∈ is, noCastAdmin a = true) :
    ¬ Round6.Target.CastRedex is := by
  intro hc
  induction hc with
  | skip _ ih => exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)
  | @cast i l hi =>
    have h₀ : noCastAdmin (.plain i) = true := h _ List.mem_cons_self
    simp [noCastAdmin, hi] at h₀
  | label _ _ => exact Bool.false_ne_true (h _ List.mem_cons_self)
  | handler _ _ => exact Bool.false_ne_true (h _ List.mem_cons_self)
  | frame _ _ => exact Bool.false_ne_true (h _ List.mem_cons_self)

/-- A value is not a label, handler, frame or plain cast: `noCastAdmin` on a value. -/
theorem toAdmin_ne_of_noCast {v : Val} {a : Admin} (ha : noCastAdmin a = false) :
    v.toAdmin ≠ a := by
  intro he
  have hv : noCastAdmin v.toAdmin = true := noCastAdmin_toAdmin v
  rw [he, ha] at hv
  exact Bool.false_ne_true hv

/-- An instruction equal to one that cannot start a cast redex cannot either. -/
theorem noCast_false_of {a b : Admin} (he : a = b) (ha : noCastAdmin a = true)
    (hb : noCastAdmin b = false) : False := by
  rw [he, hb] at ha
  exact Bool.false_ne_true ha

/-- A cast redex whose head is neither a value nor a cast start does not exist. -/
theorem not_castRedex_head {a : Admin} {rest : List Admin}
    (h : Round6.Target.CastRedex (a :: rest)) (ha : noCastAdmin a = true)
    (hv : ∀ v : Val, v.toAdmin ≠ a) : False := by
  generalize hl : a :: rest = l at h
  cases h with
  | skip _ => exact hv _ (List.cons.inj hl).1.symm
  | @cast i _ hi =>
    have hai : a = .plain i := (List.cons.inj hl).1
    have h₀ : noCastAdmin (.plain i) = true := hai ▸ ha
    simp [noCastAdmin, hi] at h₀
  | label _ => exact noCast_false_of (List.cons.inj hl).1 ha rfl
  | handler _ => exact noCast_false_of (List.cons.inj hl).1 ha rfl
  | frame _ => exact noCast_false_of (List.cons.inj hl).1 ha rfl

/-- A cast redex after a value is a cast redex of the rest. -/
theorem castRedex_tail {v : Val} {l : List Admin}
    (h : Round6.Target.CastRedex (v.toAdmin :: l)) : Round6.Target.CastRedex l := by
  generalize hl : v.toAdmin :: l = l' at h
  cases h with
  | skip h' => exact (List.cons.inj hl).2 ▸ h'
  | @cast i _ hi =>
    exact absurd (List.cons.inj hl).1 (toAdmin_ne_of_noCast (by simp [noCastAdmin, hi]))
  | label _ => exact absurd (List.cons.inj hl).1 (toAdmin_ne_of_noCast rfl)
  | handler _ => exact absurd (List.cons.inj hl).1 (toAdmin_ne_of_noCast rfl)
  | frame _ => exact absurd (List.cons.inj hl).1 (toAdmin_ne_of_noCast rfl)

/-- **Cast redexes stop at the first non-value**: after values, an instruction that is neither a
value nor able to start a cast redex ends the search. -/
theorem not_castRedex_vals {a : Admin} {rest : List Admin} (ha : noCastAdmin a = true)
    (hv : ∀ v : Val, v.toAdmin ≠ a) :
    ∀ vs : List Val, ¬ Round6.Target.CastRedex (vals vs ++ a :: rest)
  | [], h => not_castRedex_head h ha hv
  | _ :: vs, h => not_castRedex_vals ha hv vs (castRedex_tail h)

/-- `not_castRedex_vals`, at a code given by an equation. -/
theorem not_castRedex_prefix {l : List Admin} (h : Round6.Target.CastRedex l) (vs : List Val)
    (a : Admin) (rest : List Admin) (he : l = vals vs ++ a :: rest) (ha : noCastAdmin a = true)
    (hv : ∀ v : Val, v.toAdmin ≠ a) : False :=
  not_castRedex_vals ha hv vs (he ▸ h)

/-- A cast redex at a label is a cast redex of its body. -/
theorem castRedex_label {n : Nat} {cont : List Instr} {b l : List Admin}
    (h : Round6.Target.CastRedex (.label n cont b :: l)) : Round6.Target.CastRedex b := by
  generalize hl : Admin.label n cont b :: l = l' at h
  cases h with
  | skip _ => exact absurd (List.cons.inj hl).1 (Ne.symm (toAdmin_ne_of_noCast rfl))
  | cast _ => exact Admin.noConfusion (List.cons.inj hl).1
  | label hb' =>
    injection (List.cons.inj hl).1 with _ _ hbb
    exact hbb ▸ hb'
  | handler _ => exact Admin.noConfusion (List.cons.inj hl).1
  | frame _ => exact Admin.noConfusion (List.cons.inj hl).1

/-- A cast redex at a handler is a cast redex of its body. -/
theorem castRedex_handler {n : Nat} {cs : List Catch} {b l : List Admin}
    (h : Round6.Target.CastRedex (.handler n cs b :: l)) : Round6.Target.CastRedex b := by
  generalize hl : Admin.handler n cs b :: l = l' at h
  cases h with
  | skip _ => exact absurd (List.cons.inj hl).1 (Ne.symm (toAdmin_ne_of_noCast rfl))
  | cast _ => exact Admin.noConfusion (List.cons.inj hl).1
  | label _ => exact Admin.noConfusion (List.cons.inj hl).1
  | handler hb' =>
    injection (List.cons.inj hl).1 with _ _ hbb
    exact hbb ▸ hb'
  | frame _ => exact Admin.noConfusion (List.cons.inj hl).1

/-- A cast redex at a frame is a cast redex of its body. -/
theorem castRedex_frame {n : Nat} {fi : Frame} {b l : List Admin}
    (h : Round6.Target.CastRedex (.frame n fi b :: l)) : Round6.Target.CastRedex b := by
  generalize hl : Admin.frame n fi b :: l = l' at h
  cases h with
  | skip _ => exact absurd (List.cons.inj hl).1 (Ne.symm (toAdmin_ne_of_noCast rfl))
  | cast _ => exact Admin.noConfusion (List.cons.inj hl).1
  | label _ => exact Admin.noConfusion (List.cons.inj hl).1
  | handler _ => exact Admin.noConfusion (List.cons.inj hl).1
  | frame hb' =>
    injection (List.cons.inj hl).1 with _ _ hbb
    exact hbb ▸ hb'

/-- A plain instruction that is not a constant is not a value. -/
theorem toAdmin_ne_plain {i : Instr} (hi : ∀ t b, i ≠ .intConst t b)
    (hf : ∀ t b, i ≠ .floatConst t b) (hv : ∀ b, i ≠ .vecConst b) (v : Val) :
    v.toAdmin ≠ .plain i := by
  intro he
  cases v with
  | num n =>
    obtain ⟨ty, b⟩ := n
    cases ty with
    | int t => exact hi t b (Admin.plain.inj he).symm
    | float t => exact hf t b (Admin.plain.inj he).symm
  | vec b => exact hv b (Admin.plain.inj he).symm
  | ref r => exact Admin.noConfusion he

/-- `return_call_ref` is neither a value nor a cast. -/
theorem retCallRef_noCast {c : Admin} (hc : c.IsReturnCallRef) :
    noCastAdmin c = true ∧ ∀ v : Val, v.toAdmin ≠ c := by
  match c, hc with
  | .plain (.returnCallRef _), _ =>
    exact ⟨rfl, fun v => by rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin]⟩
  | .returnCallRefType _, _ =>
    exact ⟨rfl, fun v => by rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin]⟩

/-- `throwing a` is a value followed by `throw_ref`. -/
theorem vals_throwing (vs : List Val) (a : Nat) (rest : List Admin) :
    vals vs ++ throwing a ++ rest = vals (vs ++ [.ref (.exn a)]) ++ .plain .throwRef :: rest := by
  simp [vals, throwing, Val.toAdmin]

/-- `throw_ref` is neither a value nor a cast. -/
theorem throwRef_noCast :
    noCastAdmin (.plain .throwRef) = true ∧ ∀ v : Val, v.toAdmin ≠ .plain .throwRef :=
  ⟨rfl, fun v => by rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin]⟩

/-- The redex of a `CtrlRead` step is not a cast. -/
theorem ctrlRead_not_castRedex {c : Config H} {is' : List Admin} (h : CtrlRead c is') :
    ¬ Round6.Target.CastRedex c.code := by
  intro hx
  cases h with
  | block _ _ =>
    exact not_castRedex_prefix hx _ _ [] rfl rfl
      (toAdmin_ne_plain (by simp) (by simp) (by simp))
  | loop _ _ =>
    exact not_castRedex_prefix hx _ _ [] rfl rfl
      (toAdmin_ne_plain (by simp) (by simp) (by simp))
  | tryTable _ _ =>
    exact not_castRedex_prefix hx _ _ [] rfl rfl
      (toAdmin_ne_plain (by simp) (by simp) (by simp))
  | call _ _ =>
    exact not_castRedex_prefix hx [] _ [] rfl rfl
      (toAdmin_ne_plain (by simp) (by simp) (by simp))
  | returnCall _ _ =>
    exact not_castRedex_prefix hx [] _ [] rfl rfl
      (toAdmin_ne_plain (by simp) (by simp) (by simp))
  | @returnCallRefLabel s f k cont vs c rest hc =>
    exact not_castRedex_prefix (castRedex_label hx) vs c rest (by simp) (retCallRef_noCast hc).1
      (retCallRef_noCast hc).2
  | @returnCallRefHandler s f k cs vs c rest hc =>
    exact not_castRedex_prefix (castRedex_handler hx) vs c rest (by simp)
      (retCallRef_noCast hc).1 (retCallRef_noCast hc).2
  | @returnCallRefFrameNull s f fi k vs c rest hc =>
    exact not_castRedex_prefix (castRedex_frame hx) (vs ++ [.ref .null]) c rest
      (by simp [vals, Val.toAdmin]) (retCallRef_noCast hc).1 (retCallRef_noCast hc).2
  | throwRefNull =>
    exact not_castRedex_prefix hx [.ref .null] _ [] rfl throwRef_noCast.1 throwRef_noCast.2
  | @throwRefInstrs s f vs a rest _ =>
    exact not_castRedex_prefix hx _ _ _ (vals_throwing vs a rest) throwRef_noCast.1
      throwRef_noCast.2
  | throwRefLabel =>
    exact not_castRedex_prefix (castRedex_label hx) [.ref (.exn _)] _ [] rfl throwRef_noCast.1
      throwRef_noCast.2
  | throwRefFrame =>
    exact not_castRedex_prefix (castRedex_frame hx) [.ref (.exn _)] _ [] rfl throwRef_noCast.1
      throwRef_noCast.2
  | throwRefHandlerEmpty =>
    exact not_castRedex_prefix (castRedex_handler hx) [.ref (.exn _)] _ [] rfl throwRef_noCast.1
      throwRef_noCast.2
  | throwRefHandlerCatch _ _ =>
    exact not_castRedex_prefix (castRedex_handler hx) [.ref (.exn _)] _ [] rfl throwRef_noCast.1
      throwRef_noCast.2
  | throwRefHandlerCatchRef _ _ =>
    exact not_castRedex_prefix (castRedex_handler hx) [.ref (.exn _)] _ [] rfl throwRef_noCast.1
      throwRef_noCast.2
  | throwRefHandlerCatchAll =>
    exact not_castRedex_prefix (castRedex_handler hx) [.ref (.exn _)] _ [] rfl throwRef_noCast.1
      throwRef_noCast.2
  | throwRefHandlerCatchAllRef =>
    exact not_castRedex_prefix (castRedex_handler hx) [.ref (.exn _)] _ [] rfl throwRef_noCast.1
      throwRef_noCast.2
  | throwRefHandlerNext _ =>
    exact not_castRedex_prefix (castRedex_handler hx) [.ref (.exn _)] _ [] rfl throwRef_noCast.1
      throwRef_noCast.2

/-- The code of a table step holds no cast. -/
theorem tableStep_noCast {P : Profile} {c c' : Config H} (h : TableStep P c c') :
    ∀ a ∈ c.code, noCastAdmin a = true := by
  cases h <;>
    (simp only [List.forall_mem_cons, constI32, noCastAdmin_toAdmin, true_and]
     simp [noCastAdmin, Round6.Target.castInstr])

/-- The code of a memory step holds no cast. -/
theorem memStep_noCast {P : Profile} {c c' : Config H} (h : MemoryStep P c c') :
    ∀ a ∈ c.code, noCastAdmin a = true := by
  cases h <;>
    (simp only [List.forall_mem_cons, constI32, noCastAdmin_toAdmin, true_and]
     simp [noCastAdmin, Round6.Target.castInstr])

/-- The code of an aggregate step holds no cast. -/
theorem aggStep_noCast {c c' : Config H} (h : AggregateStep c c') :
    ∀ a ∈ c.code, noCastAdmin a = true := by
  cases h <;>
    (simp only [List.forall_mem_cons, List.forall_mem_append, vals, List.forall_mem_map,
       constI32, noCastAdmin_toAdmin, implies_true, true_and]
     simp [noCastAdmin, Round6.Target.castInstr])

/-- The redex of a `ReadHeadX` step is not a cast. -/
theorem ReadHeadX.not_castRedex {P : Profile} {c : Config H} {is' : List Admin}
    (h : ReadHeadX P c is') : ¬ Round6.Target.CastRedex c.code := by
  cases h with
  | refNull _ => exact not_castRedex_of_all (by simp [noCastAdmin, Round6.Target.castInstr])
  | refFunc _ => exact not_castRedex_of_all (by simp [noCastAdmin, Round6.Target.castInstr])
  | table h => exact not_castRedex_of_all (tableStep_noCast h.1)
  | memory h => exact not_castRedex_of_all (memStep_noCast h.1)
  | aggregate h => exact not_castRedex_of_all (aggStep_noCast h.1)
  | ctrl h => exact ctrlRead_not_castRedex h

/-! ## Completeness at `BI` -/

section Complete

variable {P : Profile} (hn : H → String) (host : HostSemantics H)

/-- **`PureHeadX` steps are `Step_pure` facts of `stepModel BI`**, at typed code. -/
theorem pureFactX_complete {is is' : List Admin} (hp : PureHeadX P is is')
    (h : TypedV (simEnv (BI P hn host)) instrsT (.list (adminsToV is))) :
    (stepModel (BI P hn host)).D "Step_pure" "%~>%" []
      (.tuple [.list (adminsToV is), .list (adminsToV is')]) :=
  (Round6.Reading.sPureB_iff _).2 (spure_of_pureHeadX hn host hp h)

/-- **`ReadHeadX` steps are `Step_read` facts of `stepModel BI`**, at a typed, bounded
configuration. -/
theorem readFactX_complete {c : Config H} {is' : List Admin} (hr : ReadHeadX P c is')
    (hb : Round4.Bounded c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hc' : TypedV (simEnv (BI P hn host)) instrsT (.list (adminsToV is'))) :
    (stepModel (BI P hn host)).D "Step_read" "%~>%" []
      (.tuple [configV hn c, .list (adminsToV is')]) :=
  (Round6.Transfer.sReadB_iff_noCast hr.not_castRedex).2
    (sread_of_readHeadX hn host hr hb hc hc')

/-- **On round 6's domain, `PureHeadX` steps are `Step_pure` facts** of `stepModel BI`. -/
theorem pureFactX_dom {c : Config H} (hc : Dom P host c) {is' : List Admin}
    (hp : PureHeadX P c.code is') :
    (stepModel (BI P hn host)).D "Step_pure" "%~>%" []
      (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) := by
  obtain ⟨⟨ts, hok⟩, hb, -⟩ := hc
  exact pureFactX_complete hn host hp
    ((Typing.typingFacts_simEnv _ hn).config c |>.1
      (Round5.Target.typed_of_configOk_sel _ hn hok hb)).2

/-- **On round 6's domain, `ReadHeadX` steps are `Step_read` facts** of `stepModel BI`, at a
`HostOk` host (for the typing of the successor). -/
theorem readFactX_dom (hh : HostOk host) {c : Config H} (hc : Dom P host c) {is' : List Admin}
    (hr : ReadHeadX P c is') :
    (stepModel (BI P hn host)).D "Step_read" "%~>%" []
      (.tuple [configV hn c, .list (adminsToV is')]) := by
  obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc
  have hs : Step P host c ⟨c.store, c.frame, is'⟩ := hr.step
  have hc' := Round5.Target.typed_of_configOk_sel (BI P hn host) hn (Step.preservation hh hok hs).1
    (hsucc _ hs)
  exact readFactX_complete hn host hr hb.1.1 (Round5.Target.typed_of_configOk_sel _ hn hok hb)
    (((Typing.typingFacts_simEnv _ hn).config _).1 hc').2

end Complete

/-! ## Through `Cover.toModelDom`, on `Dom` -/

section Model

variable {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Cover.toModelDom`. -/
local notation "SM" => stepModel (BI (Profile.spec nd r) hn host)

/-- The environment of that model. -/
local notation "EM" => simEnv (BI (Profile.spec nd r) hn host)

/-- The state and code of a point of `Dom`, and of a successor, are typed. -/
theorem typed_succ (hh : HostOk host) {c c' : Config H} (hc : Dom (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') :
    (TypedV EM stateT (stateV hn c.store c.frame) ∧ TypedV EM instrsT (.list (adminsToV c.code))) ∧
      TypedV EM instrsT (.list (adminsToV c'.code)) := by
  obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc
  have T := Typing.typingFacts_simEnv (BI (Profile.spec nd r) hn host) hn
  exact ⟨(T.config c).1 (Round5.Target.typed_of_configOk_sel _ hn hok hb),
    ((T.config c').1 (Round5.Target.typed_of_configOk_sel _ hn
      (Step.preservation hh hok hs).1 (hsucc _ hs))).2⟩

/-- **`PureHeadX` steps through `Cover.toModelDom`**: on `Dom`, Core's successor is an
observation, and its image is a `Step_pure` fact that `Step/pure` lifts to the `Step` fact. -/
theorem pureFactX_core_complete (hh : HostOk host) {c : Config H}
    (hc : Dom (Profile.spec nd r) host c) {is' : List Admin}
    (hp : PureHeadX (Profile.spec nd r) c.code is') :
    configV hn ⟨c.store, c.frame, is'⟩ ∈ SpecTec.coreObs (Profile.spec nd r) host hn c () ∧
      (SM).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list (adminsToV is')]) ∧
      (SM).D "Step" "%~>%" [] (.tuple [configV hn c, configV hn ⟨c.store, c.frame, is'⟩]) := by
  have hpf := pureFactX_dom hn host hc hp
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact hp.step
  obtain ⟨⟨hz, hcode⟩, hcode'⟩ := typed_succ hh hc hs
  exact ⟨⟨_, hs, rfl⟩, hpf,
    Round6.Reading.sstepB_pure (hasStepRules_simEnv _).pure hz hcode hcode' hpf⟩

/-- **`ReadHeadX` steps through `Cover.toModelDom`**: on `Dom`, Core's successor is an
observation, and its image is a `Step_read` fact that `Step/read` lifts to the `Step` fact. -/
theorem readFactX_core_complete (hh : HostOk host) {c : Config H}
    (hc : Dom (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadHeadX (Profile.spec nd r) c is') :
    configV hn ⟨c.store, c.frame, is'⟩ ∈ SpecTec.coreObs (Profile.spec nd r) host hn c () ∧
      (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) ∧
      (SM).D "Step" "%~>%" [] (.tuple [configV hn c, configV hn ⟨c.store, c.frame, is'⟩]) := by
  have hrf := readFactX_dom hn host hh hc hr
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := hr.step
  obtain ⟨⟨hz, hcode⟩, hcode'⟩ := typed_succ hh hc hs
  exact ⟨⟨_, hs, rfl⟩, hrf,
    Round6.Reading.sstepB_read (hasStepRules_simEnv _).read hz hcode hcode' hrf⟩

/-- **`Step_pure` facts at `BI` are sound on `Dom`**: every `Step_pure` fact of `stepModel BI`
from the code of a point of `Dom` to typed code is, up to `CfgRel`, a Core successor. -/
theorem pureFactX_sound (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {c : Config H} (hc : Dom (Profile.spec nd r) host c) {js : List Value}
    (hjs : TypedV EM instrsT (.list js))
    (hq : (SM).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js])) :
    ∃ b ∈ SpecTec.coreObs (Profile.spec nd r) host hn c (),
      SpecTec.CfgRel hn b (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨⟨ts, hok⟩, hb, _⟩ := id hc
  have ht := ((Typing.typingFacts_simEnv (BI (Profile.spec nd r) hn host) hn).config c).1
    (Round5.Target.typed_of_configOk_sel _ hn hok hb)
  exact Nondet.bwd_rel (Nondet.halves_BI hinj hf hh nd r) hc ()
    _ (Round6.Reading.sstepB_pure (hasStepRules_simEnv _).pure ht.1 ht.2 hjs hq)

/-- **`Step_read` facts at `BI` are sound on `Dom`**: every `Step_read` fact of `stepModel BI`
from a point of `Dom` to typed code is, up to `CfgRel`, a Core successor. -/
theorem readFactX_sound (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {c : Config H} (hc : Dom (Profile.spec nd r) host c) {js : List Value}
    (hjs : TypedV EM instrsT (.list js))
    (hq : (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    ∃ b ∈ SpecTec.coreObs (Profile.spec nd r) host hn c (),
      SpecTec.CfgRel hn b (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨⟨ts, hok⟩, hb, _⟩ := id hc
  have ht := ((Typing.typingFacts_simEnv (BI (Profile.spec nd r) hn host) hn).config c).1
    (Round5.Target.typed_of_configOk_sel _ hn hok hb)
  exact Nondet.bwd_rel (Nondet.halves_BI hinj hf hh nd r) hc ()
    _ (Round6.Reading.sstepB_read (hasStepRules_simEnv _).read ht.1 ht.2 hjs hq)

/-- **`Step_pure` at a `PureHeadX` redex is that step**, on `DomDet`: every `Step_pure` fact of
`stepModel BI` from the code to typed code is the classified successor up to `CfgRel`. -/
theorem pureFactX_unique (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hp : PureHeadX (Profile.spec nd r) c.code is') {js : List Value}
    (hjs : TypedV EM instrsT (.list js))
    (hq : (SM).D "Step_pure" "%~>%" [] (.tuple [.list (adminsToV c.code), .list js])) :
    SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
      (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ := pureFactX_sound hinj hf hh hc.1 hjs hq
  have hs : Step (Profile.spec nd r) host c ⟨c.store, c.frame, is'⟩ := by
    obtain ⟨s, f, is⟩ := c
    exact hp.step
  rw [hc.2 _ _ hs₁ hs] at hrel
  exact hrel

/-- **`Step_read` at a `ReadHeadX` redex is that step**, on `DomDet`: every `Step_read` fact of
`stepModel BI` from the configuration to typed code is the classified successor up to
`CfgRel`. -/
theorem readFactX_unique (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {c : Config H} (hc : DomDet (Profile.spec nd r) host c) {is' : List Admin}
    (hr : ReadHeadX (Profile.spec nd r) c is') {js : List Value}
    (hjs : TypedV EM instrsT (.list js))
    (hq : (SM).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) :
    SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
      (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨b, ⟨c₁, hs₁, rfl⟩, hrel⟩ := readFactX_sound hinj hf hh hc.1 hjs hq
  rw [hc.2 _ _ hs₁ hr.step] at hrel
  exact hrel

end Model

end Silmaril.Wasm.SpecTec.Institution.FwdX30

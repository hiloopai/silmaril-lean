module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef.NewDataNum

/-!
# Round 5, pass 2, track fwdref: the host rules from `HostRespectsT`

`$hostcall` (`Prims.hostcallCall`) lists the outcomes of a *chosen* call with the same image as
the given one. Family C's `CtrlHost.hostcall` and `Bwd.HostInv` relate the two for
every call, which needs `Prims.HostRespects` everywhere (refuted, `Host.lean`). The consumers only
meet calls on typed store images: the forward rules have the source configuration `Typed`, and
`Bwd.HostStepsV` has it as a hypothesis. So:

* `hostcall_typed`, `hostInv_typed`: the two directions of `$hostcall` at one call on a typed
  store image, from `HostRespectsT`;
* `fwd_callRefHostT`, `fwd_callRefHostDivT`: `fwd_callRefHost5`/`-Div5` with those;
* `bwd_callRefHostT`, `bwd_callRefHostDivT`, `hostStepsV_of_T`: track backward's
  `bwd_callRefHost`/`-Div` and `hostStepsV_of_hostInv` with those;
* `oblT`, `forward_validT`: `Obl` and forward conjunct with the host fields from
  `HostRespectsT` and `array.new_data-num` from `newDataNumB_builtins`;
* `partsOkR_of_openT`, `wholeStepValidOk_of_openT`: the pass-1 integration's assembly from
  `OpenT`; `openT_of_open`: `OpenT` is no stronger than `Round5.Int.Open`.

The copied proofs (`*T`) are the originals with the host hypothesis replaced.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.ExecReadAggregate (evalExp_iterNVar)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4 (Bounded tyBnd)
open Round4Int (BI)
open Round5.Fwd (TypesB Obl callTypesB)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## `HostRespectsT` -/

/-- `HostRespects` gives `HostRespectsT`. -/
theorem hostRespectsT_of {env : Env} (hr : Prims.HostRespects hn host) :
    HostRespectsT env hn host := fun h h' s s' vs vs' _ he o ho => hr h h' s s' vs vs' he o ho

/-- The store images of two calls with the same image agree. -/
theorem storeV_eq_of_hostArgs {h h' : H} {s s' : Store H} {vs vs' : List Val}
    (he : Prims.hostArgs hn h s vs = Prims.hostArgs hn h' s' vs') : storeV hn s = storeV hn s' := by
  simp only [Prims.hostArgs, List.cons.injEq, ArgV.val.injEq] at he
  exact he.2.1

/-- **Injectivity of `storeV` on typed images gives `HostRespectsT`**, for every host, when `hn`
is injective (`valV` is, `Typing.valV_injective`). -/
theorem hostRespectsT_of_storeInj {env : Env} (hinj : Function.Injective hn)
    (hs : StoreInjT env hn) : HostRespectsT env hn host := by
  intro h h' s s' vs vs' hst he o ho
  have he' : Value.text (hn h) = Value.text (hn h') ∧ storeV hn s = storeV hn s' ∧
      vs.map valV = vs'.map valV := by
    simpa only [Prims.hostArgs, List.cons.injEq, ArgV.val.injEq, Value.case.injEq, true_and,
      Value.list.injEq, and_true] using he
  have hh : h = h' := hinj (Value.text.inj he'.1)
  have hss : s = s' := hs s s' hst he'.2.1
  have hvs : vs = vs' := List.map_injective_iff.2 (fun _ _ e => Typing.valV_injective e) he'.2.2
  subst hh hss hvs
  exact ⟨o, ho, rfl⟩

/-- **`$hostcall` lists every outcome of a call on a typed store image**, from `HostRespectsT`
(`Prims.ctrlHost_hostcall` at one call). -/
theorem hostcall_typed (hf : HostFinite host)
    (hr : HostRespectsT (simEnv (BI P hn host)) hn host) (h : H) (s : Store H) (vs : List Val)
    (hst : TypedV (simEnv (BI P hn host)) storeT (storeV hn s)) :
    ∃ os : List Value,
      Applies (simEnv (BI P hn host)) "hostcall" [.val (.case "_HOSTFUNC" (.text (hn h))),
        .val (storeV hn s), .val (.list (vs.map valV))] (.list os) ∧
      ∀ o, host h s vs o → outcomeV hn o ∈ os := by
  classical
  have hex : ∃ p : H × Store H × List Val, Prims.hostArgs hn h s vs =
      Prims.hostArgs hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os :=
    ⟨(h, s, vs), rfl, hf h s vs⟩
  refine ⟨hex.choose_spec.2.choose.map (outcomeV hn), ?_, ?_⟩
  · refine Prims.applies_of_noClause (Prims.findDef_hostcall _) ?_
    show (Prims.builtins P hn host).call "hostcall" (Prims.hostArgs hn h s vs) = _
    rw [Prims.call_hostcall, Prims.hostcallCall]
    split
    · rfl
    · contradiction
  · intro o ho
    obtain ⟨o', ho', he⟩ := hr _ _ _ _ _ _ hst hex.choose_spec.1 o ho
    rw [he]
    exact List.mem_map_of_mem ((hex.choose_spec.2.choose_spec o').1 ho')

/-- **Every member of `$hostcall`'s result at a call on a typed store image is an outcome the
host allows**, from `HostRespectsT` (`Integrate.hostInv_concrete` at one call). -/
theorem hostInv_typed (hf : HostFinite host) (hr : HostRespectsT (simEnv (BI P hn host)) hn host)
    {h : H} {s : Store H} {vs : List Val} {v x : Value}
    (hst : TypedV (simEnv (BI P hn host)) storeT (storeV hn s))
    (happ : Applies (simEnv (BI P hn host)) "hostcall"
      [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeV hn s), .val (.list (vs.map valV))] v)
    (hm : memValue x v = .ok (.bool true)) : ∃ o, host h s vs o ∧ x = outcomeV hn o := by
  classical
  have hex : ∃ p : H × Store H × List Val,
      Prims.hostArgs hn h s vs = Prims.hostArgs hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os := ⟨(h, s, vs), rfl, hf h s vs⟩
  have hcall : (Prims.builtins P hn host).call "hostcall" (Prims.hostArgs hn h s vs) =
      some (.list (hex.choose_spec.2.choose.map (outcomeV hn))) := by
    rw [Prims.call_hostcall, Prims.hostcallCall]
    split
    · rfl
    · contradiction
  have happ' : Applies (simEnv (BI P hn host)) "hostcall" (Prims.hostArgs hn h s vs)
      (.list (hex.choose_spec.2.choose.map (outcomeV hn))) :=
    Prims.applies_of_noClause (Prims.findDef_hostcall _) hcall
  have hv : v = .list (hex.choose_spec.2.choose.map (outcomeV hn)) := happ.unique happ'
  have hmem : x ∈ hex.choose_spec.2.choose.map (outcomeV hn) := by
    rw [hv] at hm
    simpa [memValue] using hm
  obtain ⟨o', ho', hx⟩ := List.mem_map.1 hmem
  have hho' : host hex.choose.1 hex.choose.2.1 hex.choose.2.2 o' :=
    (hex.choose_spec.2.choose_spec o').2 ho'
  have hst' : TypedV (simEnv (BI P hn host)) storeT (storeV hn hex.choose.2.1) :=
    storeV_eq_of_hostArgs hex.choose_spec.1 ▸ hst
  obtain ⟨o, ho, he⟩ := hr _ _ _ _ _ _ hst' hex.choose_spec.1.symm o' hho'
  exact ⟨o, ho, hx.symm.trans he⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef

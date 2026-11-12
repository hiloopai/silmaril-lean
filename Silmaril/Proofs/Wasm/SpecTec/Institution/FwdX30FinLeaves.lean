module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.Defs
public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms

/-!
# The forward direction at wasm-3.0, finished: the leaves

At the concrete primitives `Round4Int.BI`:

* `sreadB_of_castRead`: a `CastRead` step from a bounded configuration with round 6's
  `Round6.CastsV.CastsInv`, at a typed state and code, is a `Step_read` fact of the backend reading
  (`SReadB`). The derivations are those of the cast leaf of `Round6.Int.openR_backend`
  (`Round6.Reading.fwd_refTestG` & co., used by `Casts.fwdG_top`), stopped before the lift with
  `Step/read`. `RefOkAtB` comes from `RefOkV.refOkBV_of_agreeTy` at `Int.agreeTy_BI`, through
  `Round6.CastsV.castRefOk_of_refOkBV`, as in `Round6.CastsV.castsFwdV`.
* `sread_retFrameAddr`: `return_call_ref` out of a frame at an address, at a typed state and
  code with a bounded store, is a `Step_read` fact of the declarative reading to SpecTec's code
  `vals vs ++ [ref (func a), c.retToCall]` (the body of
  `Round5.Fwd.fwd_returnCallRefFrameAddr_retToCall5`, stopped before the lift), and
  `sreadB_retFrameAddr` transfers it to the backend reading (`Round6.Transfer.sReadB_iff_noCast`:
  the redex is not a cast redex).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30Fin

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Round4 (Bounded ModuleBnd)
open Round4Int (BI)
open Round6.Reading (SReadB)

variable {H : Type} {P : Profile} (hn : H → String) (host : HostSemantics H)

/-- The environment at the concrete primitives. -/
local notation "EB" => simEnv (BI P hn host)

/-! ## The cast rules -/

/-- `CastRefOk` at the bounded configurations with `CastsInv`, at the concrete primitives
(`Round6.CastsV.castsFwdV`'s hypothesis). -/
theorem castRefOk_BI :
    Round6.CastsV.CastRefOk EB hn (fun c : Config H => Bounded c ∧ Round6.CastsV.CastsInv c) :=
  Round6.CastsV.castRefOk_of_refOkBV (Round6.RefOkV.refOkBV_of_agreeTy (Round6.Int.agreeTy_BI P hn host))
    (fun _ h => h.1.frame) (fun _ h => h.2)

/-- **A `CastRead` step is a `Step_read` fact of the backend reading**, from a bounded
configuration with `CastsInv`, at a typed state and code (the cast leaf of
`Round6.Int.openR_backend`, before the lift). -/
theorem sreadB_of_castRead {c : Config H} {is' : List Admin} (h : CastRead c is')
    (hb : Bounded c) (hI : Round6.CastsV.CastsInv c) (hz : TypedV EB stateT (stateV hn c.store c.frame))
    (hc : TypedV EB instrsT (.list (adminsToV c.code))) :
    SReadB EB (configV hn c) (adminsToV is') := by
  have K := castRefOk_BI hn host (P := P)
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping EB := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns EB := Round5.Fwd.rStore_builtins hn host
  have rd : HasReadRules (envOfScript Specs.wasm30) := hasReadRules_wasm30
  have RT := RefsGC.readTable_simEnv (BI P hn host)
  have NO := Round6.Reading.noOpt_read_at (BI P hn host)
  obtain ⟨s, f, code⟩ := c
  have hv : Bounded ⟨s, f, code⟩ ∧ Round6.CastsV.CastsInv ⟨s, f, code⟩ := ⟨hb, hI⟩
  unfold CastRead at h
  cases h with
  | testTrue hok =>
    exact Round6.Reading.sread_refTestTrueB (hasRuleAt_simEnv _ rd.refTestTrue) T R G
      (Round6.Reading.refOkAtG K hv rfl hz) hok hz hc
  | testFalse hok =>
    exact Round6.Reading.sread_refTestFalseB (hasRuleAt_simEnv _ rd.refTestFalse)
      (hasRuleAt_simEnv _ rd.refTestTrue) RT NO T R G (Round6.Reading.refOkAtG K hv rfl hz) hok hz hc
  | castSucceed hok =>
    exact Round6.Reading.sread_refCastSucceedB (hasRuleAt_simEnv _ rd.refCastSucceed) T R G
      (Round6.Reading.refOkAtG K hv rfl hz) hok hz hc
  | castFail hok =>
    exact Round6.Reading.sread_refCastFailB (hasRuleAt_simEnv _ rd.refCastFail)
      (hasRuleAt_simEnv _ rd.refCastSucceed) RT NO T R G (Round6.Reading.refOkAtG K hv rfl hz)
      hok hz hc
  | brOnCastSucceed hok =>
    exact Round6.Reading.sread_brOnCastSucceedB (hasRuleAt_simEnv _ rd.brOnCastSucceed) T R G
      (Round6.Reading.refOkAtG K hv rfl hz) hok hz hc
  | brOnCastFail hok =>
    exact Round6.Reading.sread_brOnCastFailB (hasRuleAt_simEnv _ rd.brOnCastFail)
      (hasRuleAt_simEnv _ rd.brOnCastSucceed) RT NO T R G (Round6.Reading.refOkAtG K hv rfl hz)
      hok hz hc
  | brOnCastFailSucceed hok =>
    exact Round6.Reading.sread_brOnCastFailSucceedB (hasRuleAt_simEnv _ rd.brOnCastFailSucceed)
      T R G (Round6.Reading.refOkAtG K hv rfl hz) hok hz hc
  | brOnCastFailFail hok =>
    exact Round6.Reading.sread_brOnCastFailFailB (hasRuleAt_simEnv _ rd.brOnCastFailFail)
      (hasRuleAt_simEnv _ rd.brOnCastFailSucceed) RT NO T R G
      (Round6.Reading.refOkAtG K hv rfl hz) hok hz hc

/-! ## `return_call_ref` out of a frame at an address -/

/-- **`return_call_ref` out of a frame at an address, declaratively**: a `Step_read` fact to
SpecTec's code, with the `CALL_REF` index kept (`Round5.Fwd.fwd_returnCallRefFrameAddr_retToCall5`,
before the lift). -/
theorem sread_retFrameAddr {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} {fn : FuncInst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hc : c.IsReturnCallRef) (hfn : s.funcs[a]? = some fn) (hex : Expand fn.type (.func ps rs))
    (hlen : vs.length = ps.length) (hd : Round4.tyBnd fn.type = true)
    (hz : TypedV EB stateT (stateV hn s f))
    (h : TypedV EB instrsT
      (.list (adminsToV [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]))) :
    SRead EB (configV hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩)
      (adminsToV (vals vs ++ [.ref (.func a), c.retToCall])) := by
  have T : TypingFacts EB hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping EB := Typing.ctrlTyping_simEnv _
  obtain ⟨hps, hrs, hexp⟩ := Round5.Fwd.callTypesB (Round5.Int.typesB _) hd hex
  obtain ⟨yy, hyy, hyy'⟩ := adminToV_retToCall hc
  obtain ⟨hk, hfi, hb⟩ := T.frame _ fi _ h
  have hb' : TypedV EB instrsT
      (.list (adminsToV (vals vs') ++ adminsToV (vals vs) ++ [adminToV (.ref (.func a))] ++
        [adminToV c] ++ adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨habcd, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨habc, hcv⟩ := typedV_list_append.1 habcd
  obtain ⟨hab, -⟩ := typedV_list_append.1 habc
  obtain ⟨hv', hv⟩ := typedV_list_append.1 hab
  have hy : TypedV EB typeuseT yy := Tg.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have key := sread_returnCallRefFrameAddr (simEnv_readRules _).returnCallRefFrameAddr
    (z := stateV hn s f) (k := .num (.natN k)) (f := frameV fi) (ws' := adminsToV (vals vs'))
    (is := adminsToV rest) (fs := s.funcs.map (funcInstV hn)) (fv := funcInstV hn fn)
    (ty := CT.defType fn.type) (a := a) hw hz hk hfi
    (typedV_vals_prefix T (b := []) (by simpa using hv')) (Tg.nat _)
    (typedV_vals_prefix T (b := []) (by simpa using hv)) (Tg.addr a) hy hrest
    hps (Tg.natM _) hrs (Prims.applies_funcinst (Prims.projDefs_simEnv _) hn s f)
    (funcs_getElem_map hfn) rfl hexp
  simpa [configV, adminsToV_append, hyy, hyy'] using key

/-- The redex of `return_call_ref` out of a frame at an address is not a cast redex. -/
theorem not_castRedex_retFrameAddr {k : Nat} {fi : Frame} {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
    ¬ Round6.Target.CastRedex [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)] :=
  fun hx => FwdX30.not_castRedex_prefix (FwdX30.castRedex_frame hx) (vs' ++ vs ++ [.ref (.func a)])
    c rest (by simp [vals, Val.toAdmin]) (FwdX30.retCallRef_noCast hc).1
    (FwdX30.retCallRef_noCast hc).2

/-- **`return_call_ref` out of a frame at an address, up to `ConfigEq`, under the backend
reading**: from a typed state and code with a bounded store, there is a code `CodeEq` to Core's
successor code (SpecTec's, with the index kept) that is a `Step_read` fact of `SReadB`. -/
theorem sreadB_retFrameAddr {c : Config H} {is' : List Admin} (hr : RetFrameAddr c is')
    (hs : Round4.StoreBnd c.store) (hz : TypedV EB stateT (stateV hn c.store c.frame))
    (hcode : TypedV EB instrsT (.list (adminsToV c.code))) :
    ∃ is'', Bwd.CodeEq is' is'' ∧ SReadB EB (configV hn c) (adminsToV is'') := by
  cases hr with
  | @mk s f fi k vs' vs a c rest fn ps rs hc hfn hex hlen =>
    exact ⟨_, Bwd.codeEq_retToCall hc fi.module vs a,
      (Round6.Transfer.sReadB_iff_noCast (not_castRedex_retFrameAddr hc)).2
        (sread_retFrameAddr hn host hc hfn hex hlen (Round5.Fwd.tyBnd_funcType hs hfn) hz hcode)⟩

end Silmaril.Wasm.SpecTec.Institution.FwdX30Fin

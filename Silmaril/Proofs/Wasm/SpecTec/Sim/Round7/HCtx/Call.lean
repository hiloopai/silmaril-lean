module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HCtx.Host

/-!
# Round 7, `BD`: every `call_ref` step on a reference, under any context, forward at `configVD`

`HStep.forwardD_noMS` excludes sources whose image contains `CALL_REF`, because the whole-step
transfer from `BI` must keep `Step` rules 8 and 9 silent. Rules 6–9 are the rules of `Step`
whose left-hand side ends in `CALL_REF`; their Core counterparts are `callRefNull`, `callRefFunc`,
`callRefHost` and `callRefHostDiv`. Here the first two are proved at `configVD` and `BD` directly
(the last two are round 5's `HostRulesD`), for every store, memory SIMD code included, and lifted
through every evaluation context:

* `frameV_forCallD`, `funcInstVD_code_wasm`: the new frame of a call and the `CODE` field of a
  Wasm function at `funcInstVD`;
* `fwdD_callRefNull`, `fwdD_callRefFunc`: the two leaves, after round 3's value-level rule lemmas
  `Sim.sstep_callRefNull`, `Sim.sstep_callRefFunc` (a copy of round 5's `fwd_callRefFunc5` with
  `HostRulesD`'s `storeVD` facts);
* `fwdD_callLeaf`, `fwdD_callCtx`, `step_of_callCtx`, `forwardD_callCtx`: as in `Host.lean`, for
  `CallLeaf`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCtx

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (tyBnd)
open Round6.MemSimd (AdminMS AdminsMS)
open Round7.HostD (BD)
open Round7.MemSimd (storeVD stateVD configVD funcInstVD adminsToVD adminToVD instrsToVD TypedD
  BoundedSelM typingFactsD_simEnv adminsToVD_eq adminToVD_eq adminsToVD_vals)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- The new frame of a call, encoded, with `$default_` at `BD`. -/
theorem frameV_forCallD (m : ModuleInst) (vs : List Val) (ts : List ValType) :
    frameV (Frame.forCall m vs ts) = .struct [("LOCALS", .list
      ((vs.map valV).map (fun w => .opt (some w)) ++
        (ts.map Encode.toValue).map (defaultFn (simEnv (BD P hn host))))),
      ("MODULE", Equiv.RuntimeBridge.moduleInstToValue CT m)] := by
  have hd : ∀ t ∈ ts, defaultFn (simEnv (BD P hn host)) (Encode.toValue t) =
      .opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV) :=
    fun t _ => defaultFn_eq (Integrate.ctrlCallDefault_simEnv _ m t)
  have hmap : (ts.map Encode.toValue).map (defaultFn (simEnv (BD P hn host))) =
      ts.map fun t => .opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV) := by
    rw [List.map_map]
    exact List.map_congr_left fun t ht => hd t ht
  rw [hmap]
  simp [frameV, Frame.forCall, List.map_map, Function.comp_def]

/-- The `CODE` field of a Wasm function at `funcInstVD`. -/
theorem funcInstVD_code_wasm {fi : FuncInst H} {code : Func} (hc : fi.code = .wasm code) :
    (funcInstVD hn fi).field? "CODE" = some (.case "FUNC" (.tuple [pctV code.type.toNat,
      .list ((code.locals.map Encode.toValue).map (.case "LOCAL")),
      .list (instrsToVD code.body)])) := by
  simp [funcInstVD, Value.field?, hc, List.map_map, Function.comp_def]

/-- **`call_ref` on a null reference, at `configVD`**, in every `simEnv B`. -/
theorem fwdD_callRefNull (B : Builtins) {s : Store H} {f : Frame} {c : Admin} (hc : c.IsCallRef) :
    FwdPD (simEnv B) hn ⟨s, f, [.ref .null, c]⟩ ⟨s, f, [.trap]⟩ := by
  intro hc₁ _
  have TD := typingFactsD_simEnv B hn
  have Tg : CtrlTyping (simEnv B) := Typing.ctrlTyping_simEnv _
  have hms : AdminsMS [.ref .null, c] := ⟨trivial, HostRulesD.adminMS_callRef hc, trivial⟩
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode⟩ := (TD.config _).1 hc₁
  rw [adminsToVD_eq _ hms] at hcode
  have hcv : TypedV (simEnv B) instrT (adminToV c) := typedV_code hcode c (by simp)
  have hy : TypedV (simEnv B) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have key := sstep_callRefNull (hasStepRules_simEnv B).callRefNull hz hy
  have e₁ : adminsToVD [.ref .null, c] = [caseNilV "REF.NULL_ADDR", .case "CALL_REF" yy] := by
    rw [adminsToVD_eq _ hms]
    simp [adminsToV, adminToV, hyy, Equiv.RuntimeBridge.refToValue, caseNilV]
  have e₂ : adminsToVD [Admin.trap] = [caseNilV "TRAP"] := by
    simp [adminsToVD, adminToVD]
  change SStep (simEnv B) (cfgV (stateVD hn s f) (adminsToVD _))
    (cfgV (stateVD hn s f) (adminsToVD _))
  rw [e₁, e₂]
  exact key

/-- **`call_ref` into a Wasm function, at `configVD` and `BD`** (`Step` rule 7), for typed images
and a bounded callee type. The store may hold memory SIMD code. -/
theorem fwdD_callRefFunc {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func} (hc : c.IsCallRef)
    (hfa : s.funcs[a]? = some fi) (hex : Expand fi.type (.func ps rs))
    (hlen : vs.length = ps.length) (hcode : fi.code = .wasm code) (hd : tyBnd fi.type = true) :
    FwdPD (simEnv (BD P hn host)) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  intro hc₁ hc₂
  have TD := typingFactsD_simEnv (BD P hn host) hn
  have T : TypingFacts (simEnv (BD P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BD P hn host)) := Typing.ctrlTyping_simEnv _
  have hms := HostRulesD.adminsMS_hostCode vs a hc
  obtain ⟨hps, hrs, hexp⟩ := HostRulesD.callTypesD (P := P) (hn := hn) (host := host) hd hex
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (TD.config _).1 hc₁
  obtain ⟨-, hcode₂⟩ := (TD.config _).1 hc₂
  obtain ⟨hst, -⟩ := (TD.state _ _).1 hz
  have hcode₂' : TypedV (simEnv (BD P hn host)) instrsT (.list [adminToVD (.frame rs.length
      (Frame.forCall fi.module vs code.locals) [.label rs.length [] (expression code.body)])]) := by
    simpa only [adminsToVD] using hcode₂
  obtain ⟨hF, hbody⟩ := TD.frame _ _ _ hcode₂'
  have hbody' : TypedV (simEnv (BD P hn host)) instrsT
      (.list [adminToVD (.label rs.length [] (expression code.body))]) := by
    simpa only [adminsToVD] using hbody
  have his : TypedV (simEnv (BD P hn host)) instrsT (.list (instrsToVD code.body)) := by
    simpa [Round7.MemSimd.adminsToVD_expression] using TD.label _ _ _ hbody'
  rw [adminsToVD_eq _ hms] at hcode₁
  have hcv : TypedV (simEnv (BD P hn host)) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv (BD P hn host)) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hF' := frameV_forCallD (P := P) (hn := hn) (host := host) fi.module vs code.locals
  have key := sstep_callRefFunc (hasStepRules_simEnv _).callRefFunc (z := stateVD hn s f)
    (fs := s.funcs.map (funcInstVD hn)) (a := a) (D := defaultFn (simEnv (BD P hn host)))
    (f := frameV (Frame.forCall fi.module vs code.locals)) hw hz (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy (Tg.natM _) hF his
    (HostRulesD.funcinstD_of_store _ s hst hfa)
    hps hrs (Tg.idx code.type) (Integrate.locals_simEnv _ code.locals)
    (HostRulesD.applies_funcinstD _ s f)
    (HostRulesD.funcsD_getElem_map hfa) rfl hexp (funcInstVD_code_wasm hcode) rfl
    (fun t ht => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht
      exact (defaultFn_eq (Integrate.ctrlCallDefault_simEnv _ fi.module l)) ▸
        Integrate.ctrlCallDefault_simEnv _ fi.module l)
    (by rw [hF', adminsToV_vals])
  have e₁ : adminsToVD (vals vs ++ [.ref (.func a), c]) =
      adminsToV (vals vs) ++ [.case "REF.FUNC_ADDR" (.num (.natN a)), .case "CALL_REF" yy] := by
    rw [adminsToVD_eq _ hms, adminsToV_append]
    simp [adminsToV, adminToV, hyy, Equiv.RuntimeBridge.refToValue]
  have e₂ : adminsToVD [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]] =
      [.case "FRAME_%{%}%" (.tuple [.num (.natN rs.length),
        frameV (Frame.forCall fi.module vs code.locals),
        .list [.case "LABEL_%{%}%" (.tuple [.num (.natN rs.length), .list [],
          .list (instrsToVD code.body)])]])] := by
    simp [adminsToVD, adminToVD, instrsToVD, Round7.MemSimd.adminsToVD_expression, Ty.length]
  change SStep _ (cfgV (stateVD hn s f) (adminsToVD _))
    (cfgV (stateVD hn s f) (adminsToVD _))
  rw [e₁, e₂]
  simpa [Ty.length] using key

/-- **Core's `call_ref` leaves, forward at `configVD` and `BD`**, at a store whose function types
are bounded. -/
theorem fwdD_callLeaf (hinj : Function.Injective hn) (hf : HostFinite host) {s₀ : Store H}
    (hb : ∀ fi ∈ s₀.funcs, tyBnd fi.type = true) :
    ∀ c c' : Config H, CallLeaf P host c c' → c.store = s₀ →
      FwdPD (simEnv (BD P hn host)) hn c c'
  | _, _, .null hc, _ => fwdD_callRefNull _ hc
  | _, _, .func hc hfa hex hlen hcode, hs => by
      subst hs
      exact fwdD_callRefFunc hc hfa hex hlen hcode (hb _ (List.mem_of_getElem? hfa))
  | _, _, .host h, hs => fwdD_hostLeaf hinj hf hb _ _ h hs

/-- **A `call_ref` step on a reference under any evaluation context, forward at `configVD` and
`BD`.** -/
theorem fwdD_callCtx (hinj : Function.Injective hn) (hf : HostFinite host) {c c' : Config H}
    (hb : ∀ fi ∈ c.store.funcs, tyBnd fi.type = true) (h : CallCtxStep P host c c') :
    FwdPD (simEnv (BD P hn host)) hn c c' :=
  fwdD_ctxStep _ (fwdD_callLeaf hinj hf hb) h rfl

/-- A `call_ref` leaf is a Core step. -/
theorem step_of_callLeaf : ∀ {c c' : Config H}, CallLeaf P host c c' → Step P host c c'
  | _, _, .null hc => .callRefNull hc
  | _, _, .func hc hfa hex hlen hcode => .callRefFunc hc hfa hex hlen hcode
  | _, _, .host h => step_of_hostLeaf h

/-- **A `call_ref` step on a reference under any evaluation context is a Core step.** -/
theorem step_of_callCtx {c c' : Config H} (h : CallCtxStep P host c c') : Step P host c c' :=
  step_of_ctxStep (fun _ _ => step_of_callLeaf) h

/-- A host call under contexts is a `call_ref` step under contexts. -/
theorem callCtx_of_hostCtx {c c' : Config H} (h : HostCtxStep P host c c') :
    CallCtxStep P host c c' := by
  induction h with
  | leaf h => exact .leaf (.host h)
  | instrs _ hne ih => exact .instrs ih hne
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

/-- **`forward` at `BD` for `call_ref` steps on a reference under any evaluation context**, in the
shape of `RMD.OpenRMRestD.forward`, at every source (memory SIMD code included). -/
theorem forwardD_callCtx (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hb : BoundedSelM c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelM c₁)
    (h : CallCtxStep P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d') := by
  have hs := step_of_callCtx h
  have hT := Round7.MemSimd.typedD_of_configOk_selM (BD P hn host) hn hc hb
  have hT' := Round7.MemSimd.typedD_of_configOk_selM (BD P hn host) hn
    (Step.preservation hh hc hs).1 (hsucc _ hs)
  refine ⟨c', hs, fun _ => rfl, c', Bwd.ConfigEq.refl c', ?_⟩
  exact fwdD_callCtx hinj hf (fun fi hfi => (hb.1.1.storeBnd.funcs fi hfi).1) h hT hT'

end Silmaril.Wasm.SpecTec.Sim.Round7.HCtx

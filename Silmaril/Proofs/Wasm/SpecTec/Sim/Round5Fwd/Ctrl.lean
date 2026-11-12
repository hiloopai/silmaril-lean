module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.TyBnd

/-!
# Round 5: the block and call rules from bounded type typing

The earlier forward proofs of `block`, `loop`, `call_ref` (Wasm and host callee) and
`return_call_ref`-frame-addr took family C's `CtrlState`/`CtrlCall`, whose `blocktype`,
`valtypes` and `expand` fields quantify over every Core type and are refuted
(`ConfigOk.not_ctrlCall`). Here the same proofs take `Round5.Fwd.TypesB` (the bounded
restatement) and the bounds that `Round4.Bounded` gives: the frame's module types
(`ModuleBnd`), and every function instance's type (`StoreBnd.funcs`). `tyBnd_of_expand` carries
the bound to the expanded function type.

* `dderives_expandB`: SpecTec's `Expand` on the image of Core's `Expand d ct`, for bounded `d`;
* `blocktypeB`: `$blocktype_` with typed results, for a bounded frame module;
* `fwd_block5`, `fwd_loop5`, `fwd_callRefFunc5`, `fwd_callRefHost5`, `fwd_callRefHostDiv5`,
  `fwdUp_returnCallRefFrameAddr5`: the forward cases, matching the fields of `Obl`.

The host cases also take `HostFinite` and `Prims.HostRespects` (for `$hostcall`), as round 2's did.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded tyBnd ModuleBnd)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## `Expand` and `$blocktype_` on bounded types -/

/-- **SpecTec's `Expand` holds of the images of Core's `Expand d ct`, for bounded `d`.** Track
builtins' `Prims.dderives_expand` with `TypesB` in place of the refuted `TypeTyping`. -/
theorem dderives_expandB (T : TypesB (simEnv (BI P hn host))) (O : ElseI) {d : DefType}
    {ct : CCompType} (hd : tyBnd d = true) (h : Expand d ct) :
    DDerives (simEnv (BI P hn host)) O "Expand" "%~~%" [] (.tuple [tyV d, tyV ct]) := by
  obtain ⟨hu⟩ := h
  rename_i fin sups
  have hb : tyBnd sups = true ∧ tyBnd ct = true := tyBnd_of_unrolldt hd hu
  have hρ : ValsOnly (VarEnv.empty.bindVals (Prims.expandσ d fin sups ct)) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt (Prims.hasRuleAt_expand _) (Prims.expandσ d fin sups ct)
    (QuantsOk.cons rfl (T.deftype d hd _ hρ) (QuantsOk.cons rfl (T.comptype ct hb.2 _ hρ)
      (QuantsOk.cons rfl (T.final fin _ hρ) (QuantsOk.cons rfl (T.typeuses sups hb.1 _ hρ)
        QuantsOk.nil))))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) ?_
  intro pr hpr
  simp only [List.mem_singleton] at hpr
  subst hpr
  exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_callArgs rfl
    (Equiv.evalArgs_cons (evalExp_var rfl) (evalArgs_nil _ _))
    ((Prims.applies_unrolldt (prof := P) hn host d _).2 (by rw [hu]; rfl)),
    Prims.evalExp_expandSub d fin sups ct, by simp [cmpValues]⟩)

/-- The facts the call rules consume, for a bounded defined type expanding to a function
type: both result types are typed, and SpecTec's `Expand` holds of the images. -/
theorem callTypesB (T : TypesB (simEnv (BI P hn host))) {d : DefType} {ps rs : Ty (.list .val)}
    (hd : tyBnd d = true) (hex : Expand d (.func ps rs)) :
    TypedV (simEnv (BI P hn host)) valtypesT (.list (ps.toList.map tyV)) ∧
      TypedV (simEnv (BI P hn host)) valtypesT (.list (rs.toList.map tyV)) ∧
      DDerives (simEnv (BI P hn host)) (otherwise (simEnv (BI P hn host))) "Expand" "%~~%" []
        (.tuple [CT.defType d, funcTypeV ps rs]) := by
  have hct : tyBnd ps = true ∧ tyBnd rs = true := tyBnd_func (tyBnd_of_expand hd hex)
  refine ⟨T.valtypes ps hct.1, T.valtypes rs hct.2, ?_⟩
  rw [Prims.funcTypeV_eq]
  exact dderives_expandB T _ hd hex

/-- `$blocktype_(z, _IDX x)` on images, with typed result types, for a bounded frame module. -/
theorem blocktypeB_idx (T : TypesB (simEnv (BI P hn host))) (s : Store H) (f : Frame)
    (hM : ModuleBnd f.module) (x : TypeIdx) (t₁ t₂ : List CValType)
    (h : f.module.blockType? (.typeIdx x) = some (t₁, t₂)) :
    ∃ T₁ T₂ : List Value, T₁.length = t₁.length ∧ T₂.length = t₂.length ∧
      TypedV (simEnv (BI P hn host)) valtypesT (.list T₁) ∧
      TypedV (simEnv (BI P hn host)) valtypesT (.list T₂) ∧
      Applies (simEnv (BI P hn host)) "blocktype_"
        [.val (stateV hn s f), .val (Encode.toValue (BlockType.typeIdx x))]
        (Exn.instrTypeV T₁ T₂) := by
  obtain ⟨d, hx, hft⟩ : ∃ d, f.module.types[x.toNat]? = some d ∧
      DefType.funcType? d = some (t₁, t₂) := by
    simpa only [ModuleInst.blockType?, Option.bind_eq_bind, Option.bind_eq_some_iff] using h
  obtain ⟨ps, rs, he, h₁, h₂⟩ := Prims.funcType?_inv hft
  have hd : tyBnd d = true := hM.1 d (List.mem_of_getElem? hx)
  have hct : tyBnd ps = true ∧ tyBnd rs = true :=
    tyBnd_func (tyBnd_of_expand hd (Expand.iff.2 he))
  obtain ⟨ps', t', cs, hd', hu⟩ := Prims.blocktype_idx_undef (Prims.blocktypeDefs_simEnv _)
    (State.stateDefs_simEnv _) hn s f x hx
  have hb : (BI P hn host).call "blocktype_" [.val (stateV hn s f),
      .val (.case "_IDX" (Encode.toValue x))] =
      some (Exn.instrTypeV (ps.toList.map tyV) (rs.toList.map tyV)) := by
    rw [Prims.call_blocktype, Prims.blocktypeCall_stateV, h, h₁, h₂]
    rfl
  have hl₁ : (ps.toList.map tyV).length = t₁.length := by rw [h₁, List.length_map]
  have hl₂ : (rs.toList.map tyV).length = t₂.length := by rw [h₂, List.length_map]
  exact ⟨_, _, hl₁, hl₂, T.valtypes ps hct.1, T.valtypes rs hct.2,
    ps', t', cs, hd', Or.inr ⟨hu, hb⟩⟩

/-- **`$blocktype_` on images, with typed result types, for a bounded frame module.** -/
theorem blocktypeB (T : TypesB (simEnv (BI P hn host))) (s : Store H) (f : Frame)
    (hM : ModuleBnd f.module) (bt : BlockType) (t₁ t₂ : List CValType)
    (h : f.module.blockType? bt = some (t₁, t₂)) :
    ∃ T₁ T₂ : List Value, T₁.length = t₁.length ∧ T₂.length = t₂.length ∧
      TypedV (simEnv (BI P hn host)) valtypesT (.list T₁) ∧
      TypedV (simEnv (BI P hn host)) valtypesT (.list T₂) ∧
      Applies (simEnv (BI P hn host)) "blocktype_" [.val (stateV hn s f), .val (Encode.toValue bt)]
        (Exn.instrTypeV T₁ T₂) := by
  cases bt with
  | typeIdx x => exact blocktypeB_idx T s f hM x t₁ t₂ h
  | empty =>
    have ht : [] = t₁ ∧ [] = t₂ := by simpa only [ModuleInst.blockType?, Option.some.injEq,
      Prod.mk.injEq] using h
    exact ⟨[], [], by rw [← ht.1]; rfl, by rw [← ht.2]; rfl, Integrate.locals_simEnv _ [],
      Integrate.locals_simEnv _ [],
      Prims.applies_blocktypeResult (Prims.blocktypeDefs_simEnv _) _ none⟩
  | value t =>
    have ht : [] = t₁ ∧ [f.module.instVal t] = t₂ := by
      simpa only [ModuleInst.blockType?, Option.some.injEq, Prod.mk.injEq] using h
    exact ⟨[], [Encode.toValue t], by rw [← ht.1]; rfl, by rw [← ht.2]; rfl,
      Integrate.locals_simEnv _ [], Integrate.locals_simEnv _ [t],
      Prims.applies_blocktypeResult (Prims.blocktypeDefs_simEnv _) _ (some (Encode.toValue t))⟩

/-! ## `block` and `loop` -/

/-- `block`, from a bounded frame module. -/
theorem fwd_block5 (TB : TypesB (simEnv (BI P hn host))) {s : Store H} {f : Frame}
    {bt : BlockType} {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hlen : vs.length = t₁.length)
    (hM : ModuleBnd f.module) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩ := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Ty : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  obtain ⟨T₁, T₂, hl₁, hl₂, h₁, h₂, hb⟩ := blocktypeB TB s f hM bt t₁ t₂ hbt
  refine fwd_of_sread' T (hasStepRules_simEnv _).read fun hz h => ?_
  have hv : TypedV (simEnv (BI P hn host)) valsT (.list (adminsToV (vals vs))) :=
    typedV_vals_prefix T h
  have hblk : TypedV (simEnv (BI P hn host)) instrT (adminToV (.plain (.block bt body))) :=
    typedV_code h (.plain (.block bt body)) (by simp)
  obtain ⟨hbtT, hbody⟩ := Ty.blockInv _ _ hblk
  have hw : (adminsToV (vals vs)).length = T₁.length := by
    rw [adminsToV_length, vals_length, hlen, hl₁]
  have key := sread_block (simEnv_readRules _).block (z := stateV hn s f)
    (ws := adminsToV (vals vs)) (is := instrsToV body) hw hz (Ty.natM _) hv hbtT hbody
    (Ty.nat _) h₁ h₂ hb
  rw [hl₂] at key
  have e : adminsToV (vals vs ++ expression body) = adminsToV (vals vs) ++ instrsToV body := by
    rw [adminsToV_append, adminsToV_expression]
  have e' : adminsToV (vals vs ++ [.plain (.block bt body)]) =
      adminsToV (vals vs) ++ [adminToV (.plain (.block bt body))] := by
    rw [adminsToV_append]; rfl
  show SRead _ (cfgV _ (adminsToV (vals vs ++ [.plain (.block bt body)])))
    [adminToV (.label t₂.length [] (vals vs ++ expression body))]
  rw [e', adminToV_label, e]
  exact key

/-- `loop`, from a bounded frame module. -/
theorem fwd_loop5 (TB : TypesB (simEnv (BI P hn host))) {s : Store H} {f : Frame}
    {bt : BlockType} {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hlen : vs.length = t₁.length)
    (hM : ModuleBnd f.module) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩ := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Ty : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  obtain ⟨T₁, T₂, hl₁, hl₂, h₁, h₂, hb⟩ := blocktypeB TB s f hM bt t₁ t₂ hbt
  refine fwd_of_sread' T (hasStepRules_simEnv _).read fun hz h => ?_
  have hv : TypedV (simEnv (BI P hn host)) valsT (.list (adminsToV (vals vs))) :=
    typedV_vals_prefix T h
  have hlp : TypedV (simEnv (BI P hn host)) instrT (adminToV (.plain (.loop bt body))) :=
    typedV_code h (.plain (.loop bt body)) (by simp)
  obtain ⟨hbtT, hbody⟩ := Ty.loopInv _ _ hlp
  have hw : (adminsToV (vals vs)).length = T₁.length := by
    rw [adminsToV_length, vals_length, hlen, hl₁]
  have key := sread_loop (simEnv_readRules _).loop (z := stateV hn s f)
    (ws := adminsToV (vals vs)) (is := instrsToV body) hw hz (Ty.natM _) hv hbtT hbody
    (Ty.nat _) h₁ h₂ hb
  rw [hl₁] at key
  have e : adminsToV (vals vs ++ expression body) = adminsToV (vals vs) ++ instrsToV body := by
    rw [adminsToV_append, adminsToV_expression]
  have e' : adminsToV (vals vs ++ [.plain (.loop bt body)]) =
      adminsToV (vals vs) ++ [adminToV (.plain (.loop bt body))] := by
    rw [adminsToV_append]; rfl
  show SRead _ (cfgV _ (adminsToV (vals vs ++ [.plain (.loop bt body)])))
    [adminToV (.label t₁.length [.loop bt body] (vals vs ++ expression body))]
  rw [e', adminToV_label, e]
  exact key

/-! ## Calls -/

/-- The new frame of a call, encoded (`frameV_forCall` with `$default_` proved). -/
theorem frameV_forCall5 (m : ModuleInst) (vs : List Val) (ts : List ValType) :
    frameV (Frame.forCall m vs ts) = .struct [("LOCALS", .list
      ((vs.map valV).map (fun w => .opt (some w)) ++
        (ts.map Encode.toValue).map (defaultFn (simEnv (BI P hn host))))),
      ("MODULE", Equiv.RuntimeBridge.moduleInstToValue CT m)] := by
  have hd : ∀ t ∈ ts, defaultFn (simEnv (BI P hn host)) (Encode.toValue t) =
      .opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV) :=
    fun t _ => defaultFn_eq (Integrate.ctrlCallDefault_simEnv _ m t)
  have hmap : (ts.map Encode.toValue).map (defaultFn (simEnv (BI P hn host))) =
      ts.map fun t => .opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV) := by
    rw [List.map_map]
    exact List.map_congr_left fun t ht => hd t ht
  rw [hmap]
  simp [frameV, Frame.forCall, List.map_map, Function.comp_def]

/-- The function instance at a store address is bounded in a bounded store. -/
theorem tyBnd_funcType {s : Store H} {a : Nat} {fi : FuncInst H} (hs : Round4.StoreBnd s)
    (hfa : s.funcs[a]? = some fi) : tyBnd fi.type = true :=
  (hs.funcs fi (List.mem_of_getElem? hfa)).1

/-- `call_ref` into a Wasm function, for a bounded callee type. -/
theorem fwd_callRefFunc5 (TB : TypesB (simEnv (BI P hn host))) {s : Store H} {f : Frame}
    {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (hex : Expand fi.type (.func ps rs))
    (hlen : vs.length = ps.length) (hcode : fi.code = .wasm code) (hd : tyBnd fi.type = true) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  intro hc₁ hc₂
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  obtain ⟨hps, hrs, hexp⟩ := callTypesB TB hd hex
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (T.config _).1 hc₁
  obtain ⟨-, hcode₂⟩ := (T.config _).1 hc₂
  obtain ⟨hst, -⟩ := (T.state _ _).1 hz
  obtain ⟨-, hF, hbody⟩ := T.frame _ _ _ hcode₂
  obtain ⟨-, -, hbody'⟩ := T.label _ _ _ hbody
  have his : TypedV (simEnv (BI P hn host)) instrsT (.list (instrsToV code.body)) := by
    simpa [adminsToV_expression] using hbody'
  have hcv : TypedV (simEnv (BI P hn host)) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv (BI P hn host)) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hF' := frameV_forCall5 (P := P) (hn := hn) (host := host) fi.module vs code.locals
  have key := sstep_callRefFunc (hasStepRules_simEnv _).callRefFunc (z := stateV hn s f)
    (fs := s.funcs.map (funcInstV hn)) (a := a) (D := defaultFn (simEnv (BI P hn host)))
    (f := frameV (Frame.forCall fi.module vs code.locals)) hw hz (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy (Tg.natM _) hF his
    (ConfigOk.funcinst_of_store hn s a fi hst hfa)
    hps hrs (Tg.idx code.type) (Integrate.locals_simEnv _ code.locals)
    (Prims.applies_funcinst (Prims.projDefs_simEnv _) hn s f)
    (funcs_getElem_map hfa) rfl hexp (funcInstV_code_wasm hcode) rfl
    (fun t ht => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht
      exact (defaultFn_eq (Integrate.ctrlCallDefault_simEnv _ fi.module l)) ▸
        Integrate.ctrlCallDefault_simEnv _ fi.module l)
    (by rw [hF', adminsToV_vals])
  simpa [configV, adminsToV_append, hyy, adminsToV_expression, Ty.length] using key

/-- Family C's `CtrlHost` for the concrete `B`, from a finite host that respects the encoding
(no `TypingInputs`: `result` and `funcinst` are track configok's proofs). -/
theorem ctrlHost5 (hf : HostFinite host) (hr : Prims.HostRespects hn host) :
    CtrlHost (simEnv (BI P hn host)) hn host :=
  ⟨Prims.ctrlHost_hostcall hf hr, Prims.applies_liftResult _, fun r _ => ConfigOk.typedV_result r,
    fun s a fi hst hfa => ConfigOk.funcinst_of_store hn s a fi hst hfa⟩

/-- `call_ref` into a host function that returns, for a bounded callee type. -/
theorem fwd_callRefHost5 (TB : TypesB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : Prims.HostRespects hn host) {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val}
    {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {r : Result}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (hex : Expand fi.type (.func ps rs))
    (hlen : vs.length = ps.length) (hcode : fi.code = .host h)
    (hhost : host h s vs (.returned s' r)) (hd : tyBnd fi.type = true) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩ := by
  intro hc₁ hc₂
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  have Hs : CtrlHost (simEnv (BI P hn host)) hn host := ctrlHost5 hf hr
  obtain ⟨hps, hrs, hexp⟩ := callTypesB TB hd hex
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (T.config _).1 hc₁
  obtain ⟨hz', hres⟩ := (T.config _).1 hc₂
  obtain ⟨hst, hfr⟩ := (T.state _ _).1 hz
  obtain ⟨hst', -⟩ := (T.state _ _).1 hz'
  obtain ⟨os, hcall, hall⟩ := Hs.hostcall h s vs
  have hcv : TypedV (simEnv (BI P hn host)) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv (BI P hn host)) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hcall' : Applies (simEnv (BI P hn host)) "hostcall"
      [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeV hn s),
        .val (.list (adminsToV (vals vs)))] (.list os) := by
    rw [adminsToV_vals]; exact hcall
  have key := sstep_callRefHostRes (hasStepRules_simEnv _).callRefHostfuncRes
    (fs := s.funcs.map (funcInstV hn)) (a := a) hw hst hfr (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy hst' (Hs.result r hres)
    (Hs.funcinst s a fi hst hfa) hps (Tg.natM _) hrs (typedV_text (hn h))
    (Prims.applies_funcinst (Prims.projDefs_simEnv _) hn s f)
    (funcs_getElem_map hfa) rfl (funcInstV_code_host hcode) hexp hcall'
    (hall _ hhost) (Hs.liftResult r)
  simpa [configV, stateV, adminsToV_append, hyy] using key

/-- `call_ref` into a host function that diverges, for a bounded callee type. -/
theorem fwd_callRefHostDiv5 (TB : TypesB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : Prims.HostRespects hn host) {s : Store H} {f : Frame} {c : Admin} {vs : List Val}
    {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (hex : Expand fi.type (.func ps rs))
    (hlen : vs.length = ps.length) (hcode : fi.code = .host h) (hhost : host h s vs .diverged)
    (hd : tyBnd fi.type = true) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ := by
  intro hc₁ _
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  have Hs : CtrlHost (simEnv (BI P hn host)) hn host := ctrlHost5 hf hr
  obtain ⟨hps, hrs, hexp⟩ := callTypesB TB hd hex
  obtain ⟨yy, hyy⟩ := adminToV_of_isCallRef hc
  obtain ⟨hz, hcode₁⟩ := (T.config _).1 hc₁
  obtain ⟨hst, hfr⟩ := (T.state _ _).1 hz
  obtain ⟨os, hcall, hall⟩ := Hs.hostcall h s vs
  have hcv : TypedV (simEnv (BI P hn host)) instrT (adminToV c) := typedV_code hcode₁ c (by simp)
  have hy : TypedV (simEnv (BI P hn host)) typeuseT yy := Tg.callRefInv yy (hyy ▸ hcv)
  have hw : (adminsToV (vals vs)).length = (ps.toList.map tyV).length := by
    rw [adminsToV_length, vals_length, hlen, List.length_map]; rfl
  have hcall' : Applies (simEnv (BI P hn host)) "hostcall"
      [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeV hn s),
        .val (.list (adminsToV (vals vs)))] (.list os) := by
    rw [adminsToV_vals]; exact hcall
  have key := sstep_callRefHostDiv (hasStepRules_simEnv _).callRefHostfuncDiv
    (fs := s.funcs.map (funcInstV hn)) (a := a) hw hst hfr (Tg.nat _)
    (typedV_vals_prefix T hcode₁) (Tg.addr a) hy (Hs.funcinst s a fi hst hfa)
    hps (Tg.natM _) hrs (typedV_text (hn h))
    (Prims.applies_funcinst (Prims.projDefs_simEnv _) hn s f)
    (funcs_getElem_map hfa) rfl (funcInstV_code_host hcode) hexp hcall' (hall _ hhost)
  simpa [configV, stateV, adminsToV_append, hyy] using key

/-- `return_call_ref` out of a frame, with SpecTec's result `c.retToCall`, for a bounded callee
type. -/
theorem fwd_returnCallRefFrameAddr_retToCall5 (TB : TypesB (simEnv (BI P hn host)))
    {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)} (hc : c.IsReturnCallRef)
    (hfn : s.funcs[a]? = some fn) (hex : Expand fn.type (.func ps rs))
    (hlen : vs.length = ps.length) (hd : tyBnd fn.type = true) :
    FwdP (simEnv (BI P hn host)) hn
      ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCall]⟩ := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  obtain ⟨hps, hrs, hexp⟩ := callTypesB TB hd hex
  obtain ⟨yy, hyy, hyy'⟩ := adminToV_retToCall hc
  refine fwd_of_sread' T (hasStepRules_simEnv _).read fun hz h => ?_
  obtain ⟨hk, hfi, hb⟩ := T.frame _ fi _ h
  have hb' : TypedV (simEnv (BI P hn host)) instrsT
      (.list (adminsToV (vals vs') ++ adminsToV (vals vs) ++ [adminToV (.ref (.func a))] ++
        [adminToV c] ++ adminsToV rest)) := by
    simpa [adminsToV_append] using hb
  obtain ⟨habcd, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨habc, hcv⟩ := typedV_list_append.1 habcd
  obtain ⟨hab, -⟩ := typedV_list_append.1 habc
  obtain ⟨hv', hv⟩ := typedV_list_append.1 hab
  have hy : TypedV (simEnv (BI P hn host)) typeuseT yy :=
    Tg.retCallRefInv yy (hyy ▸ typedV_list_single.1 hcv)
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

/-- **`return_call_ref` out of a frame, up to call annotations, for a bounded callee type**
(`FwdMem.fwdUp_returnCallRefFrameAddr` without `CtrlState`/`CtrlCall`). -/
theorem fwdUp_returnCallRefFrameAddr5 (TB : TypesB (simEnv (BI P hn host))) {s : Store H}
    {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin}
    {fn : FuncInst H} {ps rs : Ty (.list .val)} (hc : c.IsReturnCallRef)
    (hfn : s.funcs[a]? = some fn) (hex : Expand fn.type (.func ps rs))
    (hlen : vs.length = ps.length) (hd : tyBnd fn.type = true) :
    FwdMem.FwdUp (simEnv (BI P hn host)) hn
      ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  intro h₁ h₂
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have Tg : CtrlTyping (simEnv (BI P hn host)) := Typing.ctrlTyping_simEnv _
  obtain ⟨yy, hyy, hyy'⟩ := adminToV_retToCall hc
  have hy := Bwd.typed_retAnnot _ T Tg hyy h₁
  have h₃ := Bwd.typed_retToCall _ T (FwdMem.callRefTyping_simEnv _) hyy' hy h₂
  exact ⟨⟨s, f, vals vs ++ [.ref (.func a), c.retToCall]⟩,
    ⟨rfl, rfl, Bwd.codeEq_retToCall hc fi.module vs a⟩, h₃,
    fwd_returnCallRefFrameAddr_retToCall5 TB hc hfn hex hlen hd h₁ h₃⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

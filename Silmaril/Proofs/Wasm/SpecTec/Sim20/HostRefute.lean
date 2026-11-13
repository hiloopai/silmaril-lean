module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Thms
public import Silmaril.Wasm.SpecTec.Sim20.StoreAgree.Thms

/-!
# Host calls have no 2.0 counterpart: the forward half restated on host-free stores

wasm-2.0 has no host functions. V2 adds them (its deviation 3, `Step.callAddrHost`), and the
encoding writes a host function's code as `_HOSTFUNC (hn h)`, which is not a 2.0 `func`
(`Encode/Defs.lean`, "Host functions"). This module proves what that means for the forward half,
in both the corrected script `simEnv20S` and the script with the `STORE` erratum `simEnv20T`:

* `not_typedV_store_host`: a store holding a host function has no IL type `store`, in any
  environment whose `store`, `funcinst` and `func` are the 2.0 ones (`simEnv20` and
  `simEnv20T`, `findTyp_*20T`);
* `stuck_host`: so neither script has a step from the image of a configuration whose store holds
  a host function: every rule of their `Step` types its state or store (`StoreFix.stepRules20S_state`;
  `simEnv20T` has the same relations, `StoreAgree.envSame20T`);
* **`not_fwd_host`**: a V2 configuration that calls a host function steps (`Step.callAddrHost`),
  and its image has no step in either script, at every builtins.

So the forward 2.0 half fails on host calls, and the honest statement is the one on host-free
stores: `Whole.StoreOk`, `StoreGood.Good20CS` and `CallIndGood.StoreOkI` require every function
of the store to be a Wasm function.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.HostRefute

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly cfgV stateT storeT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB conclAlts hasOptNil)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T stateLhsB stateLhsB_cases findVal_of_cfgLhs
  findVal_of_stLhs hasTyp_of_quantsOk)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-- **A store with a host function.** -/
def HostFn20 (s : Store H) : Prop := ∃ a fi h, s.funcInst? a = some fi ∧ fi.code = .host h

/-! ## The 2.0 record types, in `simEnv20T` -/

set_option maxRecDepth 8000000 in
theorem findTyp_state20T : (simEnv20T B).findTyp? "state" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "store" (.varT "store" []), .mk "frame" (.varT "frame" [])])
      [] []])]) := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem findTyp_store20T : (simEnv20T B).findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableinst" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "meminst" []) .list) [] [],
      .mk "ELEMS" (.iterT (.varT "eleminst" []) .list) [] [],
      .mk "DATAS" (.iterT (.varT "datainst" []) .list) [] []])]) := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem findTyp_funcinst20T : (simEnv20T B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "functype" []) [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
      .mk "CODE" (.varT "func" []) [] []])]) := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem findTyp_func20T : (simEnv20T B).findTyp? "func" = some ([], [.instD [] [] (.variantT
    [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
      .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] []])]) := by
  with_unfolding_all rfl

/-! ## No host function is typed -/

/-- The 2.0 types `store`, `funcinst` and `func`, as an environment finds them. -/
structure Types20 (env : Env) : Prop where
  state : env.findTyp? "state" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "store" (.varT "store" []), .mk "frame" (.varT "frame" [])])
      [] []])])
  store : env.findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableinst" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "meminst" []) .list) [] [],
      .mk "ELEMS" (.iterT (.varT "eleminst" []) .list) [] [],
      .mk "DATAS" (.iterT (.varT "datainst" []) .list) [] []])])
  funcinst : env.findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "functype" []) [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
      .mk "CODE" (.varT "func" []) [] []])])
  func : env.findTyp? "func" = some ([], [.instD [] [] (.variantT
    [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
      .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] []])])

theorem types20_simEnv20 : Types20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) :=
  ⟨Whole.findTyp_state20, Whole.findTyp_store20, Whole.findTyp_funcinst20, Whole.findTyp_func20⟩

theorem types20_simEnv20T : Types20 (simEnv20T B) :=
  ⟨findTyp_state20T, findTyp_store20T, findTyp_funcinst20T, findTyp_func20T⟩

/-- A host function's image, as a record. -/
theorem funcInstV_host {fi : FuncInst H} {h : H} (hc : fi.code = .host h) :
    funcInstV hn fi = .struct [("TYPE", funcTypeV fi.type), ("MODULE", moduleInstV fi.module),
      ("CODE", .case "_HOSTFUNC" (.text (hn h)))] := by
  simp [funcInstV, hc]

/-- **`_HOSTFUNC` is not a 2.0 `func`.** -/
theorem not_hasTyp_hostFunc {env : Env} (T : Types20 env) (t : String) :
    ¬ HasTyp env VarEnv.empty (.varT "func" []) (.case "_HOSTFUNC" (.text t)) := by
  intro h
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 (Whole.hasTypDef_of_closed T.func h)
  obtain ⟨rfl, -⟩ : "_HOSTFUNC" = op ∧ _ := by simpa using he
  obtain ⟨_, _, _, hm, -⟩ := hasTypCase_mem hc
  simp at hm

/-- **A store holding a host function has no IL type `store`.** -/
theorem not_typedV_store_host {env : Env} (T : Types20 env) {s : Store H} (hs : HostFn20 s) :
    ¬ TypedV env storeT (storeV hn s) := by
  intro h
  obtain ⟨a, fi, hh, hf, hc⟩ := hs
  have hfuncs := Whole.typedV_list_of_empty20
    (Whole.hasTypFields_cons_nil_iff.1 (Whole.hasTypFields_of_closed T.store h)).1
  have hfi : TypedV env (.varT "funcinst" []) (funcInstV hn fi) :=
    Whole.typedV_of_getElem? hfuncs (by simpa [Store.funcInst?] using hf)
  rw [funcInstV_host hc] at hfi
  have h₁ := (Whole.hasTypFields_cons_nil_iff.1 (Whole.hasTypFields_of_closed T.funcinst hfi)).2
  have h₂ := (Whole.hasTypFields_cons_nil_iff.1 h₁).2
  exact not_hasTyp_hostFunc T _ (Whole.hasTypFields_cons_nil_iff.1 h₂).1

/-- Nor the state, at any scope that binds values only; nor the store there. -/
theorem not_hasTyp_state_host {env : Env} (T : Types20 env) {ρ : VarEnv} (hρ : ValsOnly ρ)
    {s : Store H} (f : Frame) (hs : HostFn20 s) : ¬ HasTyp env ρ stateT (stateV hn s f) :=
  fun h => not_typedV_store_host T hs
    (Whole.typedV_pair_inv T.state (Whole.typedV_of_valsOnly20 hρ h)).1

theorem not_hasTyp_store_host {env : Env} (T : Types20 env) {ρ : VarEnv} (hρ : ValsOnly ρ)
    {s : Store H} (hs : HostFn20 s) : ¬ HasTyp env ρ storeT (storeV hn s) :=
  fun h => not_typedV_store_host T hs (Whole.typedV_of_valsOnly20 hρ h)

/-! ## No step -/

/-- No rule whose conclusion types the state or the store fires from a state with a host
function. -/
theorem not_rule_host {env : Env} (T : Types20 env) {s : Store H} {f : Frame} (hs : HostFn20 s)
    {code : List Value} {w : Value} {nm : IL.Id} {qs : List Param} {op : MixopS} {e e' : Exp}
    {prems : List Prem} {σ : List (IL.Id × Value)} (hr : stateLhsB (.ruleD nm qs op e prems) = true)
    (halt : e' ∈ conclAlts e) (hq : Sim.QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ) e' (.tuple [cfgV (stateV hn s f) code, w])) :
    False := by
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  obtain ⟨hnil, hshape⟩ := stateLhsB_cases hr
  have he' : e' = e := by simpa [conclAlts, hnil] using halt
  subst he'
  rcases hshape with ⟨a, b, rfl, hz⟩ | ⟨a, b, rfl, hsq⟩
  · exact not_hasTyp_state_host T hρ f hs (hasTyp_of_quantsOk hq hz (findVal_of_cfgLhs he))
  · exact not_hasTyp_store_host T hρ hs (hasTyp_of_quantsOk hq hsq (findVal_of_stLhs he))

/-- **No step from a state with a host function**, in an environment with the 2.0 types whose
`Step` rules all type their state. -/
theorem stuck_host {env : Env} (T : Types20 env)
    (hrules : ∃ t rules, env.findRel? "Step" = some ([], "%~>%", t, rules) ∧
      rules.all stateLhsB = true)
    {s : Store H} (f : Frame) (hs : HostFn20 s) (code : List Value) (w : Value) :
    ¬ SStepB env (cfgV (stateV hn s f) code) w := by
  intro h
  obtain ⟨t, rules, hrel, hall⟩ := hrules
  cases h with
  | rule hrel' hrule halt hps hq he _ =>
    rw [hrel] at hrel'
    obtain ⟨rfl, -, rfl⟩ := by simpa using hrel'
    obtain rfl := Whole.bindParams_nil hps
    exact not_rule_host T hs (List.all_eq_true.1 hall _ (List.mem_of_getElem? hrule)) halt hq he

theorem stepRules20T_state (B : Builtins) : ∃ t rules,
    (simEnv20T B).findRel? "Step" = some ([], "%~>%", t, rules) ∧ rules.all stateLhsB = true := by
  rw [(StoreAgree.envSame20T B).rels "Step"]
  exact StoreFix.stepRules20S_state B

/-- `simEnv20S` has the 2.0 types (it is `simEnv20` with another relation table). -/
theorem types20_simEnv20S : Types20 (simEnv20S B) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-! ## The refutation -/

/-- A store with one host function of type `[] → []`. -/
def hostStore : Store Unit := { funcs := [⟨⟨[], []⟩, {}, .host ()⟩] }

/-- `CALL_ADDR 0` over that store. -/
def hostCfg : Config Unit := ⟨hostStore, {}, [.callAddr 0]⟩

/-- The host returns nothing and keeps the store. -/
def unitHost : HostSemantics Unit := fun _ s _ o => o = .returned s (.values [])

theorem hostFn_hostStore : HostFn20 hostStore := ⟨0, _, (), rfl, rfl⟩

/-- **V2 calls the host function.** -/
theorem step_hostCfg (P : Silmaril.Wasm.Numerics.Profile) :
    Step P unitHost hostCfg ⟨hostStore, {}, (Result.values []).toAdmin⟩ :=
  .callAddrHost (vs := []) (h := ()) rfl rfl rfl rfl

/-- **The forward 2.0 half fails on host calls**: V2 steps from `hostCfg`, and, at every
builtins, neither the corrected script nor the script with the `STORE` erratum has a step from
its image. -/
theorem not_fwd_host (P : Silmaril.Wasm.Numerics.Profile) (B : Builtins) (hn : Unit → String) :
    Step P unitHost hostCfg ⟨hostStore, {}, (Result.values []).toAdmin⟩ ∧
      (∀ w, ¬ SStepB (simEnv20S B) (configV hn hostCfg) w) ∧
      (∀ w, ¬ SStepB (simEnv20T B) (configV hn hostCfg) w) :=
  ⟨step_hostCfg P,
    fun w => stuck_host types20_simEnv20S (StoreFix.stepRules20S_state B) _ hostFn_hostStore _ w,
    fun w => stuck_host types20_simEnv20T (stepRules20T_state B) _ hostFn_hostStore _ w⟩

end Silmaril.Wasm.SpecTec.Sim20.HostRefute

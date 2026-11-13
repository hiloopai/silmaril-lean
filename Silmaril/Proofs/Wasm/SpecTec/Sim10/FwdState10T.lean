module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdCtrl10T

/-!
# `global.set` and host calls forward in `simEnv10T`

`global.set` at `FwdAt10T`. A state typed in `simEnv10T`
still has no host function: the `func` declaration is not corrected (`findTyp_func10T`), so a host
function instance is no more a typed `funcinst` there than in `simEnv10`
(`not_typed_host10T`), and the two host-call leaves hold vacuously.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value values setGlobal
  result)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst GlobalAddr FuncAddr Result)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV stateT evalExp_case evalExp_tup2)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_nil evalExp_list0 evalExp_list2
  evalExp_sub)
open Silmaril.Wasm.SpecTec.Sim20.State (globalSetRule)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- Every V1 index is a typed `idx` in `simEnv10T`. -/
theorem typedV_idxAll10T {k : IndexKind} (x : Idx k) :
    TypedV (simEnv10T B) (.varT "idx" []) (idxV x) :=
  typedV10T (typedV_idxAll10 x)

theorem findTyp_store10T : ∃ rest, (simEnv10T B).findTyp? "store" = some ([], [.instD [] []
    (.structT (.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [] :: rest))]) :=
  let ⟨rest, h⟩ := findTyp_store10 (B := B)
  ⟨rest, findTypT_ne h⟩

theorem findTyp_funcinst10T : ∃ t₁ t₂, (simEnv10T B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" t₁ [] [], .mk "MODULE" t₂ [] [], .mk "CODE" (.varT "func" []) [] []])]) :=
  let ⟨t₁, t₂, h⟩ := findTyp_funcinst10 (B := B)
  ⟨t₁, t₂, findTypT_ne h⟩

theorem findTyp_func10T : ∃ cs, (simEnv10T B).findTyp? "func" =
    some ([], [.instD [] [] (.variantT cs)]) ∧ cs.map caseName10 = ["FUNC"] :=
  let ⟨cs, h, hc⟩ := findTyp_func10 (B := B)
  ⟨cs, findTypT_ne h, hc⟩

/-- **`global.set` forward**, for a value of the global's type. -/
theorem fwdAt10T_globalSet (s : Store H) (f : Frame) (x : GlobalIdx) (a : GlobalAddr)
    (g : GlobalInst) (v : Execution.Runtime.Value) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a.value]? = some g) (ht : v.type = g.value.type) :
    FwdAt10T B hn ⟨s, f, [value v, .source (.globalSet x)]⟩
      ⟨setGlobal s a { g with value := v }, f, []⟩ := by
  intro hz _ hc _
  have hv : TypedV (simEnv10T B) (.varT "val" []) (valV v) := typedV_val_of_head10T hc
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("val", valV v), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fv : (VarEnv.empty.bindVals σ).findVal? "val" = some (valV v) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have hcode : adminsToV [value v, .source (.globalSet x)] =
      [valV v, .case "GLOBAL.SET" (idxV x)] := by
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  have hlhs : configV hn ⟨s, f, [value v, .source (.globalSet x)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list [valV v, .case "GLOBAL.SET" (idxV x)]]) := by
    rw [configV_eq_cfgV10, hcode]
  have hf : Fires (simEnv10T B) "Step" 6 (.tuple [configV hn ⟨s, f, [value v, .source (.globalSet x)]⟩,
      configV hn ⟨setGlobal s a { g with value := v }, f, []⟩]) := by
    rw [hlhs]
    exact fires_of_ruleAtT (hasRuleAt10_globalSet B) σ
      (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fv (hv _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fx (typedV_idxAll10T x _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
      (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
          (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fx)))))
        (evalExp_case (evalExp_tup2 (evalExp_withGlobal10 rfl (evalExp_var fz)
          (evalExp_var fx) (evalExp_var fv) ha hg ht) evalExp_list0)))
      prems_nil
  exact sstepB10T_of_fires' hf

/-- The `CODE` of a host function instance is not a 1.0 `func`. -/
theorem not_typed_hostCode10T (t : String) :
    ¬ HasTyp (simEnv10T B) VarEnv.empty (.varT "func" []) (.case "_HOSTFUNC" (.text t)) := by
  intro h
  obtain ⟨cs, htd, hcs⟩ := findTyp_func10T (B := B)
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 (Sim20.Whole.hasTypDef_of_closed htd h)
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  obtain ⟨t', qs, prems, hm, -⟩ := hasTypCase_mem hc
  have hmem : "_HOSTFUNC" ∈ cs.map caseName10 := List.mem_map.2 ⟨_, hm, rfl⟩
  rw [hcs] at hmem
  simp at hmem

/-- A host function instance is not a typed `funcinst`. -/
theorem not_typed_hostInst10T (ft : V1.FuncType) (h : H) :
    ¬ HasTyp (simEnv10T B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn (.host ft h)) := by
  intro hh
  obtain ⟨t₁, t₂, htd⟩ := findTyp_funcinst10T (B := B)
  obtain ⟨gs, he, hfs⟩ := hasTypDef_structT_iff.1 (Sim20.Whole.hasTypDef_of_closed htd hh)
  obtain rfl := (Value.struct.inj he).symm
  obtain ⟨w₁, gs₁, he₁, -, -, hfs₁⟩ := hasTypFields_cons_iff.1 hfs
  obtain ⟨-, rfl⟩ := List.cons.inj he₁
  obtain ⟨w₂, gs₂, he₂, -, -, hfs₂⟩ := hasTypFields_cons_iff.1 hfs₁
  obtain ⟨-, rfl⟩ := List.cons.inj he₂
  obtain ⟨w, gs₃, he₃, hw, -, -⟩ := hasTypFields_cons_iff.1 hfs₂
  obtain ⟨he₃', -⟩ := List.cons.inj he₃
  obtain rfl := (Prod.mk.inj he₃').2
  exact not_typed_hostCode10T (B := B) (hn h) hw

/-- **A typed 1.0 state has no host function.** -/
theorem not_typed_host10T {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) {a : FuncAddr} {ft : V1.FuncType} {h : H}
    (hs : s.funcs[a.value]? = some (.host ft h)) : False := by
  obtain ⟨hst, -⟩ := typedV_stV_iff10T.1 hz
  obtain ⟨rest, htd⟩ := findTyp_store10T (B := B)
  have hfs := Sim20.Whole.hasTypFields_of_closed htd hst
  obtain ⟨w, gs', he, hw, -, -⟩ := hasTypFields_cons_iff.1 hfs
  obtain ⟨he', -⟩ := List.cons.inj he
  obtain rfl := (Prod.mk.inj he').2
  obtain ⟨us, hus, hl⟩ := hasTyp_iterT_list_iff.1 hw
  obtain rfl := (Value.list.inj hus).symm
  have hm : funcInstV hn (.host ft h) ∈ s.funcs.map (funcInstV hn) :=
    List.mem_map_of_mem (List.mem_of_getElem? hs)
  exact not_typed_hostInst10T ft h (hasTypList_iff.1 hl _ hm)

/-- **The host-call leaf holds vacuously**: its source state is untypable. -/
theorem fwdAt10T_invokeHost (s s' : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType) (h : H)
    (args : List Execution.Runtime.Value) (r : Result)
    (hs : s.funcs[a.value]? = some (.host ft h)) :
    FwdAt10T B hn ⟨s, f, values args ++ [.invoke a]⟩ ⟨s', f, result r⟩ :=
  fun hz _ _ _ => (not_typed_host10T hz hs).elim

/-- **The diverging host-call leaf holds vacuously.** -/
theorem fwdAt10T_invokeHostDiverges (s : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType)
    (h : H) (args : List Execution.Runtime.Value) (hs : s.funcs[a.value]? = some (.host ft h)) :
    FwdAt10T B hn ⟨s, f, values args ++ [.invoke a]⟩ ⟨s, f, values args ++ [.invoke a]⟩ :=
  fun hz _ _ _ => (not_typed_host10T hz hs).elim


end Silmaril.Wasm.SpecTec.Sim10.Whole

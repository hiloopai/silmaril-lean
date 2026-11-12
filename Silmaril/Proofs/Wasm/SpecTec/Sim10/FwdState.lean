module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdCtrl
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.GlobalSet

/-!
# The 1.0 script forward at `global.set`, and the host-call leaves

* `fwdAt10_globalSet`: `Step/global.set` (6) forward, **for a value of the global's type**. V1's
  `GlobalInst` has no type of its own, and the image of `{g with value := v}` takes its `TYPE`
  from `v`, while `$with_global` keeps `g`'s; the two agree exactly when `v.type = g.value.type`
  (round 2's `setField_globalInstV`). This is the `GSetOk` conjunct of `GoodV1`, which validation
  guarantees and which passes inwards (`PlainInv.gsetOk_mid`, …).
* `not_typed_host10`: **a typed 1.0 state has no host function.** The image of a host function
  instance has `CODE = _HOSTFUNC …`, and 1.0's `func` has the one case `FUNC`. So the three
  host-call leaves of V1 (`invokeHost`, `invokeHostDiverges`) hold vacuously under `FwdAt10`
  (`fwdAt10_invokeHost`, `fwdAt10_invokeHostDiverges`): their source state is untypable.
* `typedV_idxAll10`: every V1 index is a typed `idx`.
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

variable {B : Builtins} {H : Type} {hn : H → String}

/-- **Every V1 index is a typed `idx`.** -/
theorem typedV_idxAll10 {k : IndexKind} (x : Idx k) :
    TypedV (simEnv10 B) (.varT "idx" []) (idxV x) := by
  have h32 : TypedV (simEnv10 B) (.varT "u32" []) (idxV x) :=
    typedV_aliasG10 findTyp_u32_10 (hasTyp_uN10 evalExp_num x.value.isLt)
  exact typedV_aliasG10 findTyp_idx10 (h32 _ valsOnly_empty)

/-! ## `global.set` -/

/-- **`global.set` forward**, for a value of the global's type. -/
theorem fwdAt10_globalSet (s : Store H) (f : Frame) (x : GlobalIdx) (a : GlobalAddr)
    (g : GlobalInst) (v : Execution.Runtime.Value) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a.value]? = some g) (ht : v.type = g.value.type) :
    FwdAt10 B hn ⟨s, f, [value v, .source (.globalSet x)]⟩
      ⟨setGlobal s a { g with value := v }, f, []⟩ := by
  intro hz _ hc _
  have hv : TypedV (simEnv10 B) (.varT "val" []) (valV v) := typedV_val_of_head10 hc
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
  have hf : Fires (simEnv10 B) "Step" 6 (.tuple [configV hn ⟨s, f, [value v, .source (.globalSet x)]⟩,
      configV hn ⟨setGlobal s a { g with value := v }, f, []⟩]) := by
    rw [hlhs]
    exact fires_of_ruleAt (hasRuleAt10_globalSet B) σ
      (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fv (hv _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fx (typedV_idxAll10 x _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
      (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
          (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fx)))))
        (evalExp_case (evalExp_tup2 (evalExp_withGlobal10 rfl (evalExp_var fz)
          (evalExp_var fx) (evalExp_var fv) ha hg ht) evalExp_list0)))
      prems_nil
  exact sstepB10_of_fires hf

/-! ## Host functions are untypable -/

set_option maxRecDepth 8000000 in
theorem findTyp_store10 : ∃ rest, (simEnv10 B).findTyp? "store" = some ([], [.instD [] []
    (.structT (.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [] :: rest))]) := ⟨_, rfl⟩

set_option maxRecDepth 8000000 in
theorem findTyp_funcinst10 : ∃ t₁ t₂, (simEnv10 B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" t₁ [] [], .mk "MODULE" t₂ [] [], .mk "CODE" (.varT "func" []) [] []])]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 8000000 in
theorem findTyp_func10 : ∃ cs, (simEnv10 B).findTyp? "func" =
    some ([], [.instD [] [] (.variantT cs)]) ∧ cs.map caseName10 = ["FUNC"] := ⟨_, rfl, rfl⟩

/-- The `CODE` of a host function instance is not a 1.0 `func`. -/
theorem not_typed_hostCode10 (t : String) :
    ¬ HasTyp (simEnv10 B) VarEnv.empty (.varT "func" []) (.case "_HOSTFUNC" (.text t)) := by
  intro h
  obtain ⟨cs, htd, hcs⟩ := findTyp_func10 (B := B)
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 (Sim20.Whole.hasTypDef_of_closed htd h)
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  obtain ⟨t', qs, prems, hm, -⟩ := hasTypCase_mem hc
  have hmem : "_HOSTFUNC" ∈ cs.map caseName10 := List.mem_map.2 ⟨_, hm, rfl⟩
  rw [hcs] at hmem
  simp at hmem

/-- A host function instance is not a typed `funcinst`. -/
theorem not_typed_hostInst10 (ft : V1.FuncType) (h : H) :
    ¬ HasTyp (simEnv10 B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn (.host ft h)) := by
  intro hh
  obtain ⟨t₁, t₂, htd⟩ := findTyp_funcinst10 (B := B)
  obtain ⟨gs, he, hfs⟩ := hasTypDef_structT_iff.1 (Sim20.Whole.hasTypDef_of_closed htd hh)
  obtain rfl := (Value.struct.inj he).symm
  obtain ⟨w₁, gs₁, he₁, -, -, hfs₁⟩ := hasTypFields_cons_iff.1 hfs
  obtain ⟨-, rfl⟩ := List.cons.inj he₁
  obtain ⟨w₂, gs₂, he₂, -, -, hfs₂⟩ := hasTypFields_cons_iff.1 hfs₁
  obtain ⟨-, rfl⟩ := List.cons.inj he₂
  obtain ⟨w, gs₃, he₃, hw, -, -⟩ := hasTypFields_cons_iff.1 hfs₂
  obtain ⟨he₃', -⟩ := List.cons.inj he₃
  obtain rfl := (Prod.mk.inj he₃').2
  exact not_typed_hostCode10 (B := B) (hn h) hw

/-- **A typed 1.0 state has no host function.** -/
theorem not_typed_host10 {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10 B) stateT (stateV hn s f)) {a : FuncAddr} {ft : V1.FuncType} {h : H}
    (hs : s.funcs[a.value]? = some (.host ft h)) : False := by
  obtain ⟨hst, -⟩ := typedV_stV_iff10.1 hz
  obtain ⟨rest, htd⟩ := findTyp_store10 (B := B)
  have hfs := Sim20.Whole.hasTypFields_of_closed htd hst
  obtain ⟨w, gs', he, hw, -, -⟩ := hasTypFields_cons_iff.1 hfs
  obtain ⟨he', -⟩ := List.cons.inj he
  obtain rfl := (Prod.mk.inj he').2
  obtain ⟨us, hus, hl⟩ := hasTyp_iterT_list_iff.1 hw
  obtain rfl := (Value.list.inj hus).symm
  have hm : funcInstV hn (.host ft h) ∈ s.funcs.map (funcInstV hn) :=
    List.mem_map_of_mem (List.mem_of_getElem? hs)
  exact not_typed_hostInst10 ft h (hasTypList_iff.1 hl _ hm)

/-- **The host-call leaf holds vacuously**: its source state is untypable. -/
theorem fwdAt10_invokeHost (s s' : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType) (h : H)
    (args : List Execution.Runtime.Value) (r : Result)
    (hs : s.funcs[a.value]? = some (.host ft h)) :
    FwdAt10 B hn ⟨s, f, values args ++ [.invoke a]⟩ ⟨s', f, result r⟩ :=
  fun hz _ _ _ => (not_typed_host10 hz hs).elim

/-- **The diverging host-call leaf holds vacuously.** -/
theorem fwdAt10_invokeHostDiverges (s : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType)
    (h : H) (args : List Execution.Runtime.Value) (hs : s.funcs[a.value]? = some (.host ft h)) :
    FwdAt10 B hn ⟨s, f, values args ++ [.invoke a]⟩ ⟨s, f, values args ++ [.invoke a]⟩ :=
  fun hz _ _ _ => (not_typed_host10 hz hs).elim

end Silmaril.Wasm.SpecTec.Sim10.Whole

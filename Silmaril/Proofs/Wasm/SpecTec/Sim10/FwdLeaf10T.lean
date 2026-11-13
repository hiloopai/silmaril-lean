module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdBase10T

/-!
# The forward leaves of `FwdLeaf` in `simEnv10T`

Round 2's twelve leaves (`unreachable`, `nop`, `drop`, `local.get`, `global.get`, `call`,
`local.set`, `label-vals`, `frame-vals`, `trap-label`, `trap-frame`, `local.tee`) at `FwdAt10T`:
the proofs are round 2's, with the firing built by `fires_of_ruleAtT` (evaluations in `simEnv10`,
quantifiers typed in `simEnv10T`) and the code-typing inversions of `FwdBase10T`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk SStep SRead SPure cfgV TypedV ValsOnly stateT
  typedV_list_iff evalExp_case evalExp_tup2 evalExp_tup3 evalExp_list1 dderives_iff_fires nT)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase matchArgs_nil_scope)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_nil evalExp_caseNil evalExp_list0
  evalExp_list2 evalExp_sub evalExp_iter eval_labelVals eval_frameVals)
open Silmaril.Wasm.SpecTec.Sim20.State (localGetRule globalGetRule callRule localSetRule)
set_option maxRecDepth 100000
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- **`unreachable` forward.** -/
theorem fwdAt10T_unreachable (s : Store H) (f : Frame) :
    FwdAt10T B hn ⟨s, f, [.source .unreachable]⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10T_of_spure (spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_unreachable B) []
    QuantsOk.nil (evalExp_tup2 (evalExp_list1 evalExp_caseNil) (evalExp_list1 evalExp_caseNil))
    prems_nil))

/-- **`nop` forward.** -/
theorem fwdAt10T_nop (s : Store H) (f : Frame) : FwdAt10T B hn ⟨s, f, [.source .nop]⟩ ⟨s, f, []⟩ :=
  fwdAt10T_of_spure (spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_nop B) [] QuantsOk.nil
    (evalExp_tup2 (evalExp_list1 evalExp_caseNil) evalExp_list0) prems_nil))

/-- **`drop` forward**, the dropped value typed from the code. -/
theorem fwdAt10T_drop (s : Store H) (f : Frame) (v : Execution.Runtime.Value) :
    FwdAt10T B hn ⟨s, f, [value v, .source .drop]⟩ ⟨s, f, []⟩ := by
  intro hz hz' hc hc'
  have hv : TypedV (simEnv10T B) (.varT "val" []) (valV v) := typedV_val_of_head10T hc
  have fu : (VarEnv.empty.bindVals [("val", valV v)]).findVal? "val" = some (valV v) := rfl
  have hcode : adminsToV [value v, .source .drop] = [valV v, caseNilV "DROP"] := by
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  have hf : Fires (simEnv10T B) "Step_pure" 2
      (.tuple [.list (adminsToV [value v, .source .drop]), .list (adminsToV [])]) := by
    rw [hcode]
    exact fires_of_ruleAtT (hasRuleAt10_drop B) _ (QuantsOk.cons fu (hv _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil) (evalExp_tup2 (evalExp_list2 (evalExp_sub (evalExp_var fu)) evalExp_caseNil)
        evalExp_list0) prems_nil
  exact fwdAt10T_of_spure (spure10T_of_fires hf) hz hz' hc hc'

/-- **`local.get` forward.** -/
theorem fwdAt10T_localGet (s : Store H) (f : Frame) (x : LocalIdx) (v : Execution.Runtime.Value)
    (hv : f.locals[x.toNat]? = some v) :
    FwdAt10T B hn ⟨s, f, [.source (.localGet x)]⟩ ⟨s, f, [value v]⟩ := by
  refine fwdAt10T_of_sread fun hz hc => sread10T_of_fires (k := 6) ?_
  obtain ⟨cs, htd, hg, -, -, -⟩ := findTyp_admininstr10_idxT (B := B)
  have hx : TypedV (simEnv10T B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10T htd hg findTyp_localidx10T (typedV_head10T hc)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have hrhs : adminsToV [value v] = [valV v] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
  rw [hrhs]
  exact fires_of_ruleAtT (hasRuleAt10_localGet B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list1 (evalExp_subE_iff.2 (evalExp_local10 rfl (evalExp_var fz) (evalExp_var fx) hv))))
    prems_nil

/-- **`global.get` forward.** -/
theorem fwdAt10T_globalGet (s : Store H) (f : Frame) (x : GlobalIdx)
    (a : Execution.Runtime.GlobalAddr) (g : GlobalInst) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a.value]? = some g) :
    FwdAt10T B hn ⟨s, f, [.source (.globalGet x)]⟩ ⟨s, f, [value g.value]⟩ := by
  refine fwdAt10T_of_sread fun hz hc => sread10T_of_fires (k := 7) ?_
  obtain ⟨cs, htd, -, -, hgg, -⟩ := findTyp_admininstr10_idxT (B := B)
  have hx : TypedV (simEnv10T B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10T htd hgg findTyp_globalidx10T (typedV_head10T hc)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have hrhs : adminsToV [value g.value] = [valV g.value] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
  rw [hrhs]
  exact fires_of_ruleAtT (hasRuleAt10_globalGet B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list1 (evalExp_subE_iff.2 (evalExp_dotE_iff.2
        ⟨_, evalExp_global10 rfl (evalExp_var fz) (evalExp_var fx) ha hg, rfl⟩))))
    prems_nil

/-- **`call` forward.** -/
theorem fwdAt10T_call (s : Store H) (f : Frame) (x : FuncIdx) (a : Execution.Runtime.FuncAddr)
    (ha : f.module.funcs[x.toNat]? = some a) :
    FwdAt10T B hn ⟨s, f, [.source (.call x)]⟩ ⟨s, f, [.invoke a]⟩ := by
  refine fwdAt10T_of_sread fun hz hc => sread10T_of_fires (k := 2) ?_
  obtain ⟨cs, htd, -, -, -, hcall⟩ := findTyp_admininstr10_idxT (B := B)
  have hx : TypedV (simEnv10T B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10T htd hcall findTyp_funcidx10T (typedV_head10T hc)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  exact fires_of_ruleAtT (hasRuleAt10_call B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list1 (evalExp_case (evalExp_idxE_iff.2 ⟨_, x.toNat,
        evalExp_funcaddr10 rfl (evalExp_var fz), evalExp_idxPayload fx,
        by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩))))
    prems_nil

/-- **`local.set` forward.** -/
theorem fwdAt10T_localSet (s : Store H) (f : Frame) (x : LocalIdx) (v old : Execution.Runtime.Value)
    (hold : f.locals[x.toNat]? = some old) :
    FwdAt10T B hn ⟨s, f, [value v, .source (.localSet x)]⟩
      ⟨s, { f with locals := f.locals.set x.toNat v }, []⟩ := by
  intro hz _ hc _
  obtain ⟨cs, htd, -, hs, -, -⟩ := findTyp_admininstr10_idxT (B := B)
  have hv : TypedV (simEnv10T B) (.varT "val" []) (valV v) := typedV_val_of_head10T hc
  have hx : TypedV (simEnv10T B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10T htd hs findTyp_localidx10T (typedV_second10T hc)
  have hlt : x.toNat < f.locals.length := (List.getElem?_eq_some_iff.1 hold).1
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("val", valV v), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fv : (VarEnv.empty.bindVals σ).findVal? "val" = some (valV v) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have hcode : adminsToV [value v, .source (.localSet x)] = [valV v, .case "LOCAL.SET" (idxV x)] := by
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  have hlhs : configV hn ⟨s, f, [value v, .source (.localSet x)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list [valV v, .case "LOCAL.SET" (idxV x)]]) := by
    rw [configV_eq_cfgV10, hcode]
  have hf : Fires (simEnv10T B) "Step" 5 (.tuple [configV hn ⟨s, f, [value v, .source (.localSet x)]⟩,
      configV hn ⟨s, { f with locals := f.locals.set x.toNat v }, []⟩]) := by
    rw [hlhs]
    exact fires_of_ruleAtT (hasRuleAt10_localSet B) σ
      (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fv (hv _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
      (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
          (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fx)))))
        (evalExp_case (evalExp_tup2 (evalExp_withLocal10 rfl (evalExp_var fz) (evalExp_var fx)
          (evalExp_var fv) hlt) evalExp_list0)))
      prems_nil
  exact sstepB10T_of_fires' hf

/-- **`label-vals` forward**: V1's `labelDone`. -/
theorem fwdAt10T_labelDone (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
    (vs : List Execution.Runtime.Value) :
    FwdAt10T B hn ⟨s, f, [.label n cont (values vs)]⟩ ⟨s, f, values vs⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  have hl : TypedV (simEnv10T B) adminT10 (.case "LABEL_%{%}%" (.tuple [.num (.natN n),
      .list (instrsToV cont), .list (vs.map valV)])) := by
    have h := typedV_head10T hc
    rwa [adminToV_label10, adminsToV_values] at h
  obtain ⟨hn', hcont, hb⟩ := label_inv10T hl
  have hvs : TypedV (simEnv10T B) valsTy10 (.list (vs.map valV)) := typedV_vals_of_admins10T hb
  let σ : List (IL.Id × Value) :=
    [("n", .num (.natN n)), ("instr*", .list (instrsToV cont)), ("val*", .list (vs.map valV))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n)) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (instrsToV cont)) := rfl
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (vs.map valV)) := rfl
  rw [adminsToV_labelF10, adminsToV_values]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_labelVals B) σ
    (QuantsOk.cons fn (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fc (hcont _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fv (hvs _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (eval_labelVals fn fc fv) prems_nil)

/-- **`frame-vals` forward**: V1's `frameDone`. -/
theorem fwdAt10T_frameDone (s : Store H) (f fr : Frame) (vs : List Execution.Runtime.Value) :
    FwdAt10T B hn ⟨s, f, [.frame vs.length fr (values vs)]⟩ ⟨s, f, values vs⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  have hl : TypedV (simEnv10T B) adminT10 (.case "FRAME_%{%}%" (.tuple [.num (.natN vs.length),
      frameV fr, .list (vs.map valV)])) := by
    have h := typedV_head10T hc
    rwa [adminToV_frame10, adminsToV_values] at h
  obtain ⟨hn', hfr, hb⟩ := frame_inv10T hl
  have hvs : TypedV (simEnv10T B) valsTy10 (.list (vs.map valV)) := typedV_vals_of_admins10T hb
  let σ : List (IL.Id × Value) :=
    [("n", .num (.natN (vs.map valV).length)), ("f", frameV fr), ("val*", .list (vs.map valV))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN (vs.map valV).length)) :=
    rfl
  have ff : (VarEnv.empty.bindVals σ).findVal? "f" = some (frameV fr) := rfl
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (vs.map valV)) := rfl
  have hn'' : TypedV (simEnv10T B) nT (.num (.natN (vs.map valV).length)) := by
    rwa [List.length_map]
  have he := eval_frameVals (env := simEnv10 B) fn ff fv
  rw [List.length_map] at he
  rw [adminsToV_frameF10, adminsToV_values]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_frameVals B) σ
    (QuantsOk.cons fn (hn'' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons ff (hfr _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fv (hvs _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))) he prems_nil)

/-- **`trap-label` forward**: V1's `labelTrap`. -/
theorem fwdAt10T_labelTrap (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) :
    FwdAt10T B hn ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨hn', hcont, -⟩ := label_inv10T (typedV_head10T hc)
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n)) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "instr'*" = some (.list (instrsToV cont)) := rfl
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_trapLabel B) σ
    (QuantsOk.cons fn (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fc (hcont _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
      (evalExp_iter (by decide) fc) (evalExp_list1 evalExp_caseNil))))
      (evalExp_list1 evalExp_caseNil)) prems_nil)

/-- **`trap-frame` forward**: V1's `frameTrap`. -/
theorem fwdAt10T_frameTrap (s : Store H) (f fr : Frame) (n : Nat) :
    FwdAt10T B hn ⟨s, f, [.frame n fr [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨hn', hfr, -⟩ := frame_inv10T (typedV_head10T hc)
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("f", frameV fr)]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n)) := rfl
  have ff : (VarEnv.empty.bindVals σ).findVal? "f" = some (frameV fr) := rfl
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_trapFrame B) σ
    (QuantsOk.cons fn (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons ff (hfr _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ff)
      (evalExp_list1 evalExp_caseNil)))) (evalExp_list1 evalExp_caseNil)) prems_nil)

/-- **`local.tee` forward.** -/
theorem fwdAt10T_localTee (s : Store H) (f : Frame) (x : LocalIdx) (v : Execution.Runtime.Value) :
    FwdAt10T B hn ⟨s, f, [value v, .source (.localTee x)]⟩
      ⟨s, f, [value v, value v, .source (.localSet x)]⟩ := by
  refine fwdAt10T_of_spure' fun hc => ?_
  obtain ⟨cs, htd, ht⟩ := findTyp_admininstr10_teeT (B := B)
  have hv : TypedV (simEnv10T B) (.varT "val" []) (valV v) := typedV_val_of_head10T hc
  have hx : TypedV (simEnv10T B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10T htd ht findTyp_localidx10T (typedV_second10T hc)
  let σ : List (IL.Id × Value) := [("val", valV v), ("x", idxV x)]
  have fu : (VarEnv.empty.bindVals σ).findVal? "val" = some (valV v) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have hl : adminsToV [value v, .source (.localTee x)] = [valV v, .case "LOCAL.TEE" (idxV x)] := by
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  have hr : adminsToV [value v, value v, .source (.localSet x)] =
      [valV v, valV v, .case "LOCAL.SET" (idxV x)] := by
    rw [adminsToV_map10, List.map_cons, List.map_cons, adminToV_value]
    rfl
  rw [hl, hr]
  exact spure10T_of_fires (fires_of_ruleAtT (hasRuleAt10_localTee B) σ
    (QuantsOk.cons fu (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (Sim20.State.eval_localTee fu fx) prems_nil)


end Silmaril.Wasm.SpecTec.Sim10.Whole

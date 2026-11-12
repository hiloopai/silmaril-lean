module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StateVar

/-!
# The 1.0 script forward at the leaves: variables, `call`, and twelve pure or read rules

`FwdNest.fwd10_nest` reduces the forward 1.0 half to its leaves. This module discharges twelve of
them, at every builtins (none of these rules consults a builtin):

* `Step_pure` 0 `unreachable`, 1 `nop`, 2 `drop` (`fwdAt10_unreachable`, `fwdAt10_nop`,
  `fwdAt10_drop`), 7 `label-vals`, 14 `frame-vals`, 18 `trap-label`, 19 `trap-frame`
  (`fwdAt10_labelDone`, `fwdAt10_frameDone`, `fwdAt10_labelTrap`, `fwdAt10_frameTrap`) and 28
  `local.tee` (`fwdAt10_localTee`), lifted by `Step/pure`;
* `Step_read` 2 `call`, 6 `local.get`, 7 `global.get` (`fwdAt10_call`, `fwdAt10_localGet`,
  `fwdAt10_globalGet`), lifted by `Step/read`;
* `Step` 5 `local.set` (`fwdAt10_localSet`).

Each rule's quantifiers are typed from the typing of the configuration: the state directly, an
index `x` from its instruction (`LOCAL.GET x` typed as `admininstr` types `x` as `localidx = idx`,
`typedV_idx_of_case10`), and a `val` from its `CONST` (`typedV_val_of_admin10`). The rule constants
and the state accessors are the backward half's (`Sim10.Whole.hasRuleAt10_*`,
`evalExp_local10`, …), and the conclusion evaluations of the shared rules are 2.0's
environment-generic ones (`Sim20.Pure.eval_labelVals`, `eval_frameVals`,
`Sim20.State.eval_localTee`), now used to build derivations. The label arity, continuation and
frame quantifiers come from `label_inv10`/`frame_inv10`.

`FwdReduce` collects these leaves, with those of `FwdLeafI32`, as the fragment `Leaf10F`.
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

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## Typing the quantifiers -/

/-- **Inversion of a closed alias.** -/
theorem hasTyp_closedAlias_inv {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id} {t : Typ}
    (htd : env.findTyp? x = some ([], [.instD [] [] (.aliasT t)])) {v : Value}
    (h : HasTyp env ρ (.varT x []) v) : HasTyp env VarEnv.empty t v := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hi'
  · obtain rfl := matchArgs_nil_scope hm
    exact hasTypDef_aliasT_iff.1 hd
  · exact absurd hi' not_hasTypInsts_nil

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- 1.0's `admininstr` at the index-carrying cases the leaves read. -/
theorem findTyp_admininstr10_idx : ∃ cs, (simEnv10 B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
    findCase cs "LOCAL.GET" = some (.varT "localidx" [], []) ∧
    findCase cs "LOCAL.SET" = some (.varT "localidx" [], []) ∧
    findCase cs "GLOBAL.GET" = some (.varT "globalidx" [], []) ∧
    findCase cs "CALL" = some (.varT "funcidx" [], []) :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem findTyp_localidx10 : (simEnv10 B).findTyp? "localidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl
theorem findTyp_globalidx10 : (simEnv10 B).findTyp? "globalidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl
theorem findTyp_funcidx10 : (simEnv10 B).findTyp? "funcidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

/-- **An index carried by a typed instruction is a typed `idx`.** -/
theorem typedV_idx_of_case10 {cs : List TypCase} {op : MixopS} {y : IL.Id} {w : Value}
    (htd : (simEnv10 B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)]))
    (hc : findCase cs op = some (.varT y [], []))
    (hy : (simEnv10 B).findTyp? y = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]))
    (h : TypedV (simEnv10 B) adminT10 (.case op w)) : TypedV (simEnv10 B) (.varT "idx" []) w :=
  typedV_of_scope valsOnly_empty (hasTyp_closedAlias_inv valsOnly_empty hy
    (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hc))

/-- The first element of typed code is a typed `admininstr`. -/
theorem typedV_head10 {a : Admin} {l : List Admin}
    (h : TypedV (simEnv10 B) adminsT (.list (adminsToV (a :: l)))) :
    TypedV (simEnv10 B) adminT10 (adminToV a) :=
  typedV_list_iff.1 h _ (.head _)

/-- The second element of typed code is a typed `admininstr`. -/
theorem typedV_second10 {a b : Admin} {l : List Admin}
    (h : TypedV (simEnv10 B) adminsT (.list (adminsToV (a :: b :: l)))) :
    TypedV (simEnv10 B) adminT10 (adminToV b) :=
  typedV_list_iff.1 h _ (.tail _ (.head _))

/-- A V1 value at the head of typed code is a typed `val`. -/
theorem typedV_val_of_head10 {v : Execution.Runtime.Value} {l : List Admin}
    (h : TypedV (simEnv10 B) adminsT (.list (adminsToV (value v :: l)))) :
    TypedV (simEnv10 B) (.varT "val" []) (valV v) := by
  have ha : TypedV (simEnv10 B) adminT10 (adminToV (value v)) := typedV_head10 h
  rw [adminToV_value] at ha
  exact typedV_val_of_admin10 (w := .tuple [valTypeV v.type, numV v]) ha

/-! ## From firings to steps -/

/-- A firing of 1.0's `Step` is a step under the backend reading. -/
theorem sstepB10_of_fires {k : Nat} {v w : Value} (hf : Fires (simEnv10 B) "Step" k (.tuple [v, w])) :
    SStepB (simEnv10 B) v w := by
  obtain ⟨t, rules, hrel⟩ := findRel_step10 B
  exact (sstepB10_iff B).2 ((dderives_iff_fires hrel).2 ⟨k, hf⟩)

/-- A firing of 1.0's `Step_pure` is a `Step_pure` step. -/
theorem spure10_of_fires {k : Nat} {is js : List Value}
    (hf : Fires (simEnv10 B) "Step_pure" k (.tuple [.list is, .list js])) :
    SPure (simEnv10 B) is js := by
  obtain ⟨t, rules, hrel⟩ := findRel_pure10 B
  exact (dderives_iff_fires hrel).2 ⟨k, hf⟩

/-- A firing of 1.0's `Step_read` is a `Step_read` step. -/
theorem sread10_of_fires {k : Nat} {c : Value} {js : List Value}
    (hf : Fires (simEnv10 B) "Step_read" k (.tuple [c, .list js])) : SRead (simEnv10 B) c js := by
  obtain ⟨t, rules, hrel⟩ := findRel_read10 B
  exact (dderives_iff_fires hrel).2 ⟨k, hf⟩

/-- A `Step_pure` step between the codes gives `FwdAt10` at a fixed state. -/
theorem fwdAt10_of_spure {s : Store H} {f : Frame} {code code' : List Admin}
    (hp : SPure (simEnv10 B) (adminsToV code) (adminsToV code')) :
    FwdAt10 B hn ⟨s, f, code⟩ ⟨s, f, code'⟩ :=
  fun hz _ hc hc' => (sstepB10_iff B).2 (sstep10_pure hz hc hc' hp)

/-- A `Step_pure` step between the codes, given the typing of the code, gives `FwdAt10`. -/
theorem fwdAt10_of_spure' {s : Store H} {f : Frame} {code code' : List Admin}
    (hp : TypedV (simEnv10 B) adminsT (.list (adminsToV code)) →
      SPure (simEnv10 B) (adminsToV code) (adminsToV code')) :
    FwdAt10 B hn ⟨s, f, code⟩ ⟨s, f, code'⟩ :=
  fun hz _ hc hc' => (sstepB10_iff B).2 (sstep10_pure hz hc hc' (hp hc))

/-- A `Step_read` step from the configuration gives `FwdAt10` at a fixed state. -/
theorem fwdAt10_of_sread {s : Store H} {f : Frame} {code code' : List Admin}
    (hp : TypedV (simEnv10 B) stateT (stateV hn s f) →
      TypedV (simEnv10 B) adminsT (.list (adminsToV code)) →
      SRead (simEnv10 B) (configV hn ⟨s, f, code⟩) (adminsToV code')) :
    FwdAt10 B hn ⟨s, f, code⟩ ⟨s, f, code'⟩ :=
  fun hz _ hc hc' => (sstepB10_iff B).2 (sstep10_read hz hc hc' (hp hz hc))

/-! ## `Step_pure`: `unreachable`, `nop`, `drop` -/

/-- **`unreachable` forward.** -/
theorem fwdAt10_unreachable (s : Store H) (f : Frame) :
    FwdAt10 B hn ⟨s, f, [.source .unreachable]⟩ ⟨s, f, [.trap]⟩ :=
  fwdAt10_of_spure (spure10_of_fires (fires_of_ruleAt (hasRuleAt10_unreachable B) []
    QuantsOk.nil (evalExp_tup2 (evalExp_list1 evalExp_caseNil) (evalExp_list1 evalExp_caseNil))
    prems_nil))

/-- **`nop` forward.** -/
theorem fwdAt10_nop (s : Store H) (f : Frame) : FwdAt10 B hn ⟨s, f, [.source .nop]⟩ ⟨s, f, []⟩ :=
  fwdAt10_of_spure (spure10_of_fires (fires_of_ruleAt (hasRuleAt10_nop B) [] QuantsOk.nil
    (evalExp_tup2 (evalExp_list1 evalExp_caseNil) evalExp_list0) prems_nil))

/-- **`drop` forward**, the dropped value typed from the code. -/
theorem fwdAt10_drop (s : Store H) (f : Frame) (v : Execution.Runtime.Value) :
    FwdAt10 B hn ⟨s, f, [value v, .source .drop]⟩ ⟨s, f, []⟩ := by
  intro hz hz' hc hc'
  have hv : TypedV (simEnv10 B) (.varT "val" []) (valV v) := typedV_val_of_head10 hc
  have fu : (VarEnv.empty.bindVals [("val", valV v)]).findVal? "val" = some (valV v) := rfl
  have hcode : adminsToV [value v, .source .drop] = [valV v, caseNilV "DROP"] := by
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  have hf : Fires (simEnv10 B) "Step_pure" 2
      (.tuple [.list (adminsToV [value v, .source .drop]), .list (adminsToV [])]) := by
    rw [hcode]
    exact fires_of_ruleAt (hasRuleAt10_drop B) _ (QuantsOk.cons fu (hv _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil) (evalExp_tup2 (evalExp_list2 (evalExp_sub (evalExp_var fu)) evalExp_caseNil)
        evalExp_list0) prems_nil
  exact fwdAt10_of_spure (spure10_of_fires hf) hz hz' hc hc'

/-! ## `Step_read`: `local.get`, `global.get`, `call` -/

/-- **`local.get` forward.** -/
theorem fwdAt10_localGet (s : Store H) (f : Frame) (x : LocalIdx) (v : Execution.Runtime.Value)
    (hv : f.locals[x.toNat]? = some v) :
    FwdAt10 B hn ⟨s, f, [.source (.localGet x)]⟩ ⟨s, f, [value v]⟩ := by
  refine fwdAt10_of_sread fun hz hc => sread10_of_fires (k := 6) ?_
  obtain ⟨cs, htd, hg, -, -, -⟩ := findTyp_admininstr10_idx (B := B)
  have hx : TypedV (simEnv10 B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10 htd hg findTyp_localidx10 (typedV_head10 hc)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have hrhs : adminsToV [value v] = [valV v] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
  rw [hrhs]
  exact fires_of_ruleAt (hasRuleAt10_localGet B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list1 (evalExp_subE_iff.2 (evalExp_local10 rfl (evalExp_var fz) (evalExp_var fx) hv))))
    prems_nil

/-- **`global.get` forward.** -/
theorem fwdAt10_globalGet (s : Store H) (f : Frame) (x : GlobalIdx)
    (a : Execution.Runtime.GlobalAddr) (g : GlobalInst) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a.value]? = some g) :
    FwdAt10 B hn ⟨s, f, [.source (.globalGet x)]⟩ ⟨s, f, [value g.value]⟩ := by
  refine fwdAt10_of_sread fun hz hc => sread10_of_fires (k := 7) ?_
  obtain ⟨cs, htd, -, -, hgg, -⟩ := findTyp_admininstr10_idx (B := B)
  have hx : TypedV (simEnv10 B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10 htd hgg findTyp_globalidx10 (typedV_head10 hc)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have hrhs : adminsToV [value g.value] = [valV g.value] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
  rw [hrhs]
  exact fires_of_ruleAt (hasRuleAt10_globalGet B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list1 (evalExp_subE_iff.2 (evalExp_dotE_iff.2
        ⟨_, evalExp_global10 rfl (evalExp_var fz) (evalExp_var fx) ha hg, rfl⟩))))
    prems_nil

/-- **`call` forward.** -/
theorem fwdAt10_call (s : Store H) (f : Frame) (x : FuncIdx) (a : Execution.Runtime.FuncAddr)
    (ha : f.module.funcs[x.toNat]? = some a) :
    FwdAt10 B hn ⟨s, f, [.source (.call x)]⟩ ⟨s, f, [.invoke a]⟩ := by
  refine fwdAt10_of_sread fun hz hc => sread10_of_fires (k := 2) ?_
  obtain ⟨cs, htd, -, -, -, hcall⟩ := findTyp_admininstr10_idx (B := B)
  have hx : TypedV (simEnv10 B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10 htd hcall findTyp_funcidx10 (typedV_head10 hc)
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("x", idxV x)]
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  exact fires_of_ruleAt (hasRuleAt10_call B) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list1 (evalExp_case (evalExp_idxE_iff.2 ⟨_, x.toNat,
        evalExp_funcaddr10 rfl (evalExp_var fz), evalExp_idxPayload fx,
        by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩))))
    prems_nil

/-! ## `Step`: `local.set` -/

/-- **`local.set` forward.** -/
theorem fwdAt10_localSet (s : Store H) (f : Frame) (x : LocalIdx) (v old : Execution.Runtime.Value)
    (hold : f.locals[x.toNat]? = some old) :
    FwdAt10 B hn ⟨s, f, [value v, .source (.localSet x)]⟩
      ⟨s, { f with locals := f.locals.set x.toNat v }, []⟩ := by
  intro hz _ hc _
  obtain ⟨cs, htd, -, hs, -, -⟩ := findTyp_admininstr10_idx (B := B)
  have hv : TypedV (simEnv10 B) (.varT "val" []) (valV v) := typedV_val_of_head10 hc
  have hx : TypedV (simEnv10 B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10 htd hs findTyp_localidx10 (typedV_second10 hc)
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
  have hf : Fires (simEnv10 B) "Step" 5 (.tuple [configV hn ⟨s, f, [value v, .source (.localSet x)]⟩,
      configV hn ⟨s, { f with locals := f.locals.set x.toNat v }, []⟩]) := by
    rw [hlhs]
    exact fires_of_ruleAt (hasRuleAt10_localSet B) σ
      (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fv (hv _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
      (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
          (evalExp_list2 (evalExp_sub (evalExp_var fv)) (evalExp_case (evalExp_var fx)))))
        (evalExp_case (evalExp_tup2 (evalExp_withLocal10 rfl (evalExp_var fz) (evalExp_var fx)
          (evalExp_var fv) hlt) evalExp_list0)))
      prems_nil
  exact sstepB10_of_fires hf

/-! ## `Step_pure`: labels and frames that are done or trapped, `local.tee` -/

/-- The image of a label instruction. -/
theorem adminToV_label10 (n : Nat) (cont : V1.Expr) (body : List Admin) :
    adminToV (.label n cont body) =
      .case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont), .list (adminsToV body)]) :=
  rfl

/-- The image of a frame instruction. -/
theorem adminToV_frame10 (n : Nat) (fr : Frame) (body : List Admin) :
    adminToV (.frame n fr body) =
      .case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV fr, .list (adminsToV body)]) :=
  rfl

/-- The image of a label. -/
theorem adminsToV_labelF10 (n : Nat) (cont : V1.Expr) (body : List Admin) :
    adminsToV [.label n cont body] =
      [.case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont), .list (adminsToV body)])] :=
  rfl

/-- The image of a frame. -/
theorem adminsToV_frameF10 (n : Nat) (fr : Frame) (body : List Admin) :
    adminsToV [.frame n fr body] =
      [.case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV fr, .list (adminsToV body)])] :=
  rfl

/-- **`label-vals` forward**: V1's `labelDone`. -/
theorem fwdAt10_labelDone (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
    (vs : List Execution.Runtime.Value) :
    FwdAt10 B hn ⟨s, f, [.label n cont (values vs)]⟩ ⟨s, f, values vs⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  have hl : TypedV (simEnv10 B) adminT10 (.case "LABEL_%{%}%" (.tuple [.num (.natN n),
      .list (instrsToV cont), .list (vs.map valV)])) := by
    have h := typedV_head10 hc
    rwa [adminToV_label10, adminsToV_values] at h
  obtain ⟨hn', hcont, hb⟩ := label_inv10 hl
  have hvs : TypedV (simEnv10 B) valsTy10 (.list (vs.map valV)) := typedV_vals_of_admins10 hb
  let σ : List (IL.Id × Value) :=
    [("n", .num (.natN n)), ("instr*", .list (instrsToV cont)), ("val*", .list (vs.map valV))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n)) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list (instrsToV cont)) := rfl
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (vs.map valV)) := rfl
  rw [adminsToV_labelF10, adminsToV_values]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_labelVals B) σ
    (QuantsOk.cons fn (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fc (hcont _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fv (hvs _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (eval_labelVals fn fc fv) prems_nil)

/-- **`frame-vals` forward**: V1's `frameDone`. -/
theorem fwdAt10_frameDone (s : Store H) (f fr : Frame) (vs : List Execution.Runtime.Value) :
    FwdAt10 B hn ⟨s, f, [.frame vs.length fr (values vs)]⟩ ⟨s, f, values vs⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  have hl : TypedV (simEnv10 B) adminT10 (.case "FRAME_%{%}%" (.tuple [.num (.natN vs.length),
      frameV fr, .list (vs.map valV)])) := by
    have h := typedV_head10 hc
    rwa [adminToV_frame10, adminsToV_values] at h
  obtain ⟨hn', hfr, hb⟩ := frame_inv10 hl
  have hvs : TypedV (simEnv10 B) valsTy10 (.list (vs.map valV)) := typedV_vals_of_admins10 hb
  let σ : List (IL.Id × Value) :=
    [("n", .num (.natN (vs.map valV).length)), ("f", frameV fr), ("val*", .list (vs.map valV))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN (vs.map valV).length)) :=
    rfl
  have ff : (VarEnv.empty.bindVals σ).findVal? "f" = some (frameV fr) := rfl
  have fv : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (vs.map valV)) := rfl
  have hn'' : TypedV (simEnv10 B) nT (.num (.natN (vs.map valV).length)) := by
    rwa [List.length_map]
  have he := eval_frameVals (env := simEnv10 B) fn ff fv
  rw [List.length_map] at he
  rw [adminsToV_frameF10, adminsToV_values]
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_frameVals B) σ
    (QuantsOk.cons fn (hn'' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons ff (hfr _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fv (hvs _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil))) he prems_nil)

/-- **`trap-label` forward**: V1's `labelTrap`. -/
theorem fwdAt10_labelTrap (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) :
    FwdAt10 B hn ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨hn', hcont, -⟩ := label_inv10 (typedV_head10 hc)
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("instr'*", .list (instrsToV cont))]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n)) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "instr'*" = some (.list (instrsToV cont)) := rfl
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_trapLabel B) σ
    (QuantsOk.cons fn (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fc (hcont _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn)
      (evalExp_iter (by decide) fc) (evalExp_list1 evalExp_caseNil))))
      (evalExp_list1 evalExp_caseNil)) prems_nil)

/-- **`trap-frame` forward**: V1's `frameTrap`. -/
theorem fwdAt10_frameTrap (s : Store H) (f fr : Frame) (n : Nat) :
    FwdAt10 B hn ⟨s, f, [.frame n fr [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨hn', hfr, -⟩ := frame_inv10 (typedV_head10 hc)
  let σ : List (IL.Id × Value) := [("n", .num (.natN n)), ("f", frameV fr)]
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n)) := rfl
  have ff : (VarEnv.empty.bindVals σ).findVal? "f" = some (frameV fr) := rfl
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_trapFrame B) σ
    (QuantsOk.cons fn (hn' _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons ff (hfr _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (evalExp_tup2 (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ff)
      (evalExp_list1 evalExp_caseNil)))) (evalExp_list1 evalExp_caseNil)) prems_nil)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- 1.0's `admininstr` at `LOCAL.TEE`. -/
theorem findTyp_admininstr10_tee : ∃ cs, (simEnv10 B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
    findCase cs "LOCAL.TEE" = some (.varT "localidx" [], []) :=
  ⟨_, rfl, rfl⟩

/-- **`local.tee` forward.** -/
theorem fwdAt10_localTee (s : Store H) (f : Frame) (x : LocalIdx) (v : Execution.Runtime.Value) :
    FwdAt10 B hn ⟨s, f, [value v, .source (.localTee x)]⟩
      ⟨s, f, [value v, value v, .source (.localSet x)]⟩ := by
  refine fwdAt10_of_spure' fun hc => ?_
  obtain ⟨cs, htd, ht⟩ := findTyp_admininstr10_tee (B := B)
  have hv : TypedV (simEnv10 B) (.varT "val" []) (valV v) := typedV_val_of_head10 hc
  have hx : TypedV (simEnv10 B) (.varT "idx" []) (idxV x) :=
    typedV_idx_of_case10 htd ht findTyp_localidx10 (typedV_second10 hc)
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
  exact spure10_of_fires (fires_of_ruleAt (hasRuleAt10_localTee B) σ
    (QuantsOk.cons fu (hv _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fx (hx _ ⟨rfl, rfl, rfl⟩)
      QuantsOk.nil))
    (Sim20.State.eval_localTee fu fx) prems_nil)

end Silmaril.Wasm.SpecTec.Sim10.Whole

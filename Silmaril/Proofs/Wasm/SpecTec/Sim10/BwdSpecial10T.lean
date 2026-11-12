module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdLeaf10T

/-!
# `memory.size` and `call_indirect-trap` backwards in `simEnv10T`

The two 1.0 leaf rules whose round 2–4 proofs read more than evaluation:

* `Step_read/memory.size` (12) bounds the page count by the typing of the result `CONST I32 (% n)`
  (`lt_of_typed_constI32_10`). In `simEnv10T`, `admininstr`'s `CONST` case is the original one
  (`fixCase10` changes only `STORE`), and its payload type `val_(valtype)` is off `tbad10`, so the
  bound holds there too (**`lt_of_typed_constI32_10T`**, **`bwd10T_memorySize`**).
* `Step_read/call_indirect-trap` (4) has an `otherwise` premise. Where V1 would call, the earlier
  rule `call_indirect-call` (3) fires on the same left-hand side in `simEnv10T`: its quantifiers
  are `z : state` (typed in `simEnv10T` by the firing itself), `i`, `x` and `a` (off `tbad10`), and
  its premises are evaluations (`body10T_callIndirect`). So `otherwise` in `simEnv10T` rules the call
  out (**`bwd10T_callIndirectTrap`**).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameTable
  frameMemory)
open Silmaril.Wasm.Execution.Runtime (Frame FuncInst TableInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV RuleBody DDerives otherwise otherwiseAt noElse
  ValsOnly evalExp_case evalExp_list1 evalExp_tup2)
open Silmaril.Wasm.SpecTec.Sim20 (TypedSome)
open Silmaril.Wasm.SpecTec.Sim20.Whole (constIE iPay caseHead memSize_inv evalExp_constN)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T fixCase10)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (adminCases10 hasTyp_off10T hasTypT hasRuleAtT
  envSame10T evalExp_back evalExps_back findTyp?_simEnv10T caseOp_fixCase10 fixCase10_of_ne)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (evalExp_of caseOp)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (goodT_of_all)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## `memory.size` -/

set_option maxRecDepth 8000000 in
/-- `adminCases10` (the cases `StoreAgree` reads) are `admininstrCases10` (the cases `ConstBound`
reads): both are the variant of `Original.d170`. -/
theorem adminCases10_eq : adminCases10 = admininstrCases10 := by
  with_unfolding_all rfl

/-- `admininstr` in `simEnv10T`. -/
theorem findTyp_admininstr10T : (simEnv10T B).findTyp? "admininstr" =
    some ([], [.instD [] [] (.variantT (adminCases10.map fixCase10))]) := by
  have ht := (StoreAgree.simEnv10T_tables B).1
  have h := StoreAgree.findTyp_admin10 B
  simp only [Env.findTyp?] at h ⊢
  simp only [ht, Sim20.StoreAgree.find?_map_repl]
  simp [h]

/-- **The case of `admininstr` named `CONST` in `simEnv10T` is the original one.** -/
theorem constCase_of_memT10 {t : Typ} {qs : List Param} {prems : List Prem}
    (h : TypCase.mk "CONST" t qs prems ∈ adminCases10.map fixCase10) :
    TypCase.mk "CONST" t qs prems = constCase10 := by
  obtain ⟨c, hc, he⟩ := List.mem_map.1 h
  have hop : caseOp c = "CONST" := by rw [← caseOp_fixCase10, he]; rfl
  rw [fixCase10_of_ne (by rw [hop]; decide)] at he
  subst he
  exact constCase_of_mem10 (adminCases10_eq ▸ hc)

/-- The scope a one-instance declaration without patterns types in is the empty one. -/
theorem matchArgs_nil_scope {env : Env} {ws : List ArgV} {σ : VarEnv}
    (h : MatchArgs env VarEnv.empty [] ws σ) : σ = VarEnv.empty := by
  obtain ⟨n, hn⟩ := h
  exact (Sim20.StoreAgree.matchArgs_nil_ok hn).1

/-- The payload of `CONST`, typed in `simEnv10T` at the case's tuple type, is below `2 ^ 32`. -/
theorem lt_of_constPayload10T {k : Nat}
    (ht : HasTyp (simEnv10T B) VarEnv.empty (.tupT [.mk "valtype" (.varT "valtype" []),
      .mk "_" (.varT "val_" [.expA (.varE "valtype")])]) (.tuple [caseNilV "I32", pctV k])) :
    k < 2 ^ 32 := by
  have ht' := (hasTyp_off10T B (by rfl) (goodT_of_all (by decide))).1 ht
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 ht'
  have evs : vs = [caseNilV "I32", pctV k] := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 (evs ▸ htup)
  obtain ⟨ey, eys⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨ey', -⟩ := List.cons.inj (eys.trans hys')
  have fvt : (VarEnv.empty.bindVal "valtype" y).findVal? "valtype" = some (caseNilV "I32") := by
    simp [← ey]
  obtain ⟨n, hn, hlt⟩ := val_i32_inv10 (Sim.evalExp_var fvt) (ey' ▸ hy')
  have e' : k = n := by simpa [pctV] using hn
  exact e' ▸ hlt

/-- The case `CONST` of `admininstr` in `simEnv10T`, inverted to its payload typing. -/
theorem constPayload_of_def10T {k : Nat}
    (hd : HasTypDef (simEnv10T B) VarEnv.empty (.variantT (adminCases10.map fixCase10))
      (.case "CONST" (.tuple [caseNilV "I32", pctV k]))) :
    HasTyp (simEnv10T B) VarEnv.empty (.tupT [.mk "valtype" (.varT "valtype" []),
      .mk "_" (.varT "val_" [.expA (.varE "valtype")])]) (.tuple [caseNilV "I32", pctV k]) := by
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
  have eow : op = "CONST" ∧ w = .tuple [caseNilV "I32", pctV k] := by
    simpa only [Value.case.injEq] using he.symm
  obtain ⟨t, qs, prems, hm, ht, -⟩ := hasTypCase_mem (eow.1 ▸ eow.2 ▸ hc)
  have e := constCase_of_memT10 hm
  simp only [constCase10, TypCase.mk.injEq, true_and] at e
  exact e.1 ▸ ht

/-- **A typed `admininstr` `CONST I32 (% k)` of `simEnv10T` has `k < 2 ^ 32`.** -/
theorem lt_of_hasTyp_constI32_10T {ρ : VarEnv} (hρ : ValsOnly ρ) {k : Nat}
    (h : HasTyp (simEnv10T B) ρ (.varT "admininstr" [])
      (.case "CONST" (.tuple [caseNilV "I32", pctV k]))) : k < 2 ^ 32 := by
  have hl : localTyp? ρ "admininstr" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  have etd := (Option.some.inj (findTyp_admininstr10T.symm.trans htd)).symm
  rcases hasTypInsts_cons_inv (etd ▸ hi) with ⟨σ, hσ, hd⟩ | hrest
  · obtain rfl := matchArgs_nil_scope hσ
    exact lt_of_constPayload10T (constPayload_of_def10T hd)
  · exact absurd hrest not_hasTypInsts_nil

/-- **Every `CONST I32 (% k)` of a typed `admininstr*` of `simEnv10T` has `k < 2 ^ 32`.** -/
theorem lt_of_typed_constI32_10T {l : List Value}
    (h : TypedSome (simEnv10T B) adminsT (.list l)) {k : Nat}
    (hm : Value.case "CONST" (.tuple [caseNilV "I32", pctV k]) ∈ l) : k < 2 ^ 32 := by
  obtain ⟨ρ, hρ, ht⟩ := h
  obtain ⟨vs, hvs, hl⟩ := hasTyp_iterT_list_iff.1 ht
  obtain rfl := (Value.list.inj hvs).symm
  exact lt_of_hasTyp_constI32_10T hρ (hasTypList_iff.1 hl _ hm)

/-- **`Step_read/memory.size` backwards in `simEnv10T`**, at a `GoodV1` configuration with a
typed result. -/
theorem bwd10T_memorySize {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c) (hw : TypedSome (simEnv10T B) adminsT (.list w))
    (hf : Fires (simEnv10T B) "Step_read" 12 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_invT (hasRuleAt10_memorySize B) hf
  obtain ⟨a₁, rfl, h₁⟩ := codes10_one hes
  obtain rfl := head10_memorySize (head10_of_caseE h₁)
  obtain ⟨⟨a, m⟩, hm⟩ := Option.isSome_iff_exists.1 (show (frameMemory s f).isSome from hg.1.1)
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ :=
    evalExp_cmpE_iff.1 (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  have ev : v₁ = .num (.natN m.data.size) :=
    (cmpValues_eq_true_iff.1 hcmp).trans (EvalExp.unique e₂ (evalExp_memLen10 rfl fz hm))
  obtain ⟨k, fn, hk⟩ := memSize_inv (evalExp_ki10 rfl) (ev ▸ e₁)
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV k])] :=
    Value.list.inj (EvalExp.unique hrh (evalExp_list1 (evalExp_constN fn)))
  have hlt : k < 2 ^ 32 := lt_of_typed_constI32_10T hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_memorySize hk hlt).symm, .memorySize s f a m hm⟩

/-! ## `call_indirect-trap` -/

/-- **`call_indirect-call` fires in `simEnv10T`** where V1 calls through the table: round 2's
`body10_callIndirect`, with the state typed in `simEnv10T` and the rest moved forward. -/
theorem body10T_callIndirect {D : Sim.Interp} {els : Prop} {s : Store H}
    {f : Frame} {x : TypeIdx} {c : BitVec 32} {t : TableInst} {fa : Execution.Runtime.FuncAddr}
    {fn : FuncInst V1.Func H} {ft : V1.FuncType}
    (tz : HasTyp (simEnv10T B) (VarEnv.empty.bindVals (ciScope (stateV hn s f) (pctV c.toNat)
      (idxV x) fa)) (.varT "state" []) (stateV hn s f))
    (ti : HasTyp (simEnv10T B) (VarEnv.empty.bindVals (ciScope (stateV hn s f) (pctV c.toNat)
      (idxV x) fa)) valI32T' (pctV c.toNat))
    (tx : HasTyp (simEnv10T B) (VarEnv.empty.bindVals (ciScope (stateV hn s f) (pctV c.toNat)
      (idxV x) fa)) (.varT "idx" []) (idxV x))
    (ht : frameTable s f = some t) (hft : f.module.types[x.toNat]? = some ft)
    (hent : t.refs[c.toNat]? = some (some fa)) (hfn : s.funcs[fa.value]? = some fn)
    (hty : fn.type = ft) :
    RuleBody (simEnv10T B) D els [] [] "%~>%" callIndirectRule10
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, c⟩, .source (.callIndirect x)]⟩,
        .list [.case "CALL_ADDR" (.num (.natN fa.value))]]) := by
  let σ := ciScope (stateV hn s f) (pctV c.toNat) (idxV x) fa
  have hS := envSame10T B
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV c.toNat) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := rfl
  have fa' : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN fa.value)) := rfl
  have hrefs : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.idxE (.dotE (.callE "table"
      [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]) "REFS") iPay)
      (.opt (some (.num (.natN fa.value)))) :=
    evalExp_idxE_iff.2 ⟨_, c.toNat, evalExp_dotE_iff.2 ⟨_, evalExp_table0_10 rfl fz ht, rfl⟩,
      Sim20.Whole.evalExp_iPay fi, by simp [Value.idx?, List.getElem?_map, hent]⟩
  have hp₁ : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT (.idxE (.dotE
      (.callE "table" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]) "REFS")
      iPay) (.optE (some (.varE "a")))) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, hrefs, evalExp_optE_some_iff.2 ⟨_, Sim.evalExp_var fa', rfl⟩,
      cmpValues_eq_true_iff.2 rfl⟩
  have hfty : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")
      (funcTypeV ft) := by
    refine evalExp_dotE_iff.2 ⟨funcInstV hn fn, evalExp_idxE_iff.2 ⟨_, fa.value,
      evalExp_funcinst10 rfl fz, Sim.evalExp_var fa', by simp [Value.idx?, List.getElem?_map, hfn]⟩,
      ?_⟩
    subst hty
    cases fn <;> rfl
  have hp₂ : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT
      (.callE "type" [.expA (.varE "z"), .expA (.varE "x")])
      (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_type10 rfl fz fx hft, hfty, cmpValues_eq_true_iff.2 rfl⟩
  have hc : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.tupE [.caseE "%;%" (.tupE [.varE "z",
          .listE [constIE, .caseE "CALL_INDIRECT" (.varE "x")]]),
        .listE [.caseE "CALL_ADDR" (.varE "a")]])
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, c⟩, .source (.callIndirect x)]⟩,
        .list [.case "CALL_ADDR" (.num (.natN fa.value))]]) :=
    evalExp_tup2 (evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
      (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
      (evalExp_case (Sim.evalExp_var fx)))))
      (evalExp_list1 (evalExp_case (Sim.evalExp_var fa')))
  refine ⟨rfl, VarEnv.empty, σ, rfl, ?_, evalExp_of hS hc, ?_⟩
  · exact QuantsOk.cons fz tz (QuantsOk.cons fi ti (QuantsOk.cons fx tx (QuantsOk.cons fa'
      (hasTypT (typedV_addr10 _ _ (Sim.valsOnly_bindVals σ))) QuantsOk.nil)))
  · intro pr hpr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · exact .ifPr (evalExp_of hS hp₁)
    · exact .ifPr (evalExp_of hS hp₂)

/-- **Where the trap rule fires in `simEnv10T`, V1 does not call**: `otherwise` in `simEnv10T`
against `body10T_callIndirect`. -/
theorem not_call_of_trap10T {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32}
    {t : TableInst} {fa : Execution.Runtime.FuncAddr} {fn : FuncInst V1.Func H} {ft : V1.FuncType}
    {w : List Value} {σ : List (IL.Id × Value)}
    (hq : QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ)
      [.expP "z" (.varT "state" []), .expP "i" valI32T', .expP "x" (.varT "idx" [])])
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x))
    (hother : otherwiseAt (simEnv10T B) "Step_read" [] 4
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, i⟩, .source (.callIndirect x)]⟩, .list w]))
    (ht : frameTable s f = some t) (hft : f.module.types[x.toNat]? = some ft)
    (hent : t.refs[i.toNat]? = some (some fa)) (hfn : s.funcs[fa.value]? = some fn) :
    fn.type ≠ ft := by
  intro hty
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Sim.valsOnly_bindVals σ
  have hρ' : ValsOnly (VarEnv.empty.bindVals (ciScope (stateV hn s f) (pctV i.toNat) (idxV x)
      fa)) := Sim.valsOnly_bindVals _
  obtain ⟨Z, fZ, tZ⟩ := hq "z" (.varT "state" []) (by simp)
  obtain ⟨I, fI, tI⟩ := hq "i" valI32T' (by simp)
  obtain ⟨X, fX, tX⟩ := hq "x" (.varT "idx" []) (by simp)
  have eZ : Z = stateV hn s f := Option.some.inj (fZ.symm.trans fz)
  have eI : I = pctV i.toNat := Option.some.inj (fI.symm.trans fi)
  have eX : X = idxV x := Option.some.inj (fX.symm.trans fx)
  have body : RuleBody (simEnv10T B) (DDerives (simEnv10T B) noElse)
      (otherwiseAt (simEnv10T B) "Step_read" [] 3
        (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, i⟩, .source (.callIndirect x)]⟩,
          .list [.case "CALL_ADDR" (.num (.natN fa.value))]]))
      [] [] "%~>%" callIndirectRule10
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, i⟩, .source (.callIndirect x)]⟩,
        .list [.case "CALL_ADDR" (.num (.natN fa.value))]]) :=
    body10T_callIndirect (eZ ▸ Sim.IntNumeric.hasTyp_varT_nil_congr hρ hρ' tZ)
      (eI ▸ hasTyp_valI32_congr10 tI) (eX ▸ Sim.IntNumeric.hasTyp_varT_nil_congr hρ hρ' tX)
      ht hft hent hfn hty
  obtain ⟨ps, tt, rules, hrel, rfl, h3⟩ := hasRuleAtT (hasRuleAt10_callIndirect B)
  rw [otherwiseAt] at hother
  exact hother 3 (by decide) [] "%~>%" tt rules callIndirectRule10 hrel h3 _ ⟨_, _, _, rfl, rfl⟩
    body

/-- **`Step_read/call_indirect-trap` backwards in `simEnv10T`**, at a `GoodV1` configuration. -/
theorem bwd10T_callIndirectTrap {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10T B) "Step_read" 4 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  have hS := envSame10T B
  obtain ⟨σ, hq, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAtT (hasRuleAt10_callIndirectTrap B)) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two (evalExps_back hS hes)
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨x, rfl⟩ := head10_callIndirect (head10_of_caseE h₂)
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) :=
    evalExp_varE_iff.1 (idx_of_caseE10 h₂ rfl)
  have hw : w = adminsToV [.trap] :=
    Value.list.inj (EvalExp.unique (evalExp_back hS hrh)
      (evalExp_list1 Sim20.Pure.evalExp_caseNil))
  have hother : otherwiseAt (simEnv10T B) "Step_read" [] 4
      (.tuple [configV hn ⟨s, f, [value ⟨.int .i32, i⟩, .source (.callIndirect x)]⟩, .list w]) := by
    cases hp _ (List.mem_singleton_self _) with
    | elsePr h => exact h
  have hres : (frameTable s f).isSome ∧ (f.module.types[x.toNat]?).isSome := hg.1.2.1
  obtain ⟨t, ht⟩ : ∃ t, frameTable s f = some t := Option.isSome_iff_exists.1 hres.1
  obtain ⟨ft, hft⟩ : ∃ ft, f.module.types[x.toNat]? = some ft := Option.isSome_iff_exists.1 hres.2
  refine ⟨[.trap], hw, ?_⟩
  match hent : t.refs[i.toNat]? with
  | none => exact .callIndirectBounds s f x i t ht hent
  | some none => exact .callIndirectNull s f x i t ht hent
  | some (some fa) =>
    have hlt : fa.value < s.funcs.length := by
      obtain ⟨ta, -, hta⟩ := frameTable_some ht
      exact hg.2.1.2 t (List.mem_of_getElem? hta) fa (List.mem_of_getElem? hent)
    have hfn : s.funcs[fa.value]? = some s.funcs[fa.value] := List.getElem?_eq_getElem hlt
    exact .callIndirectType s f x i t fa _ ft ht hft hent hfn
      (not_call_of_trap10T hq fz (evalExp_varE_iff.1 fi) fx hother ht hft hent hfn)

end Silmaril.Wasm.SpecTec.Sim10.Whole

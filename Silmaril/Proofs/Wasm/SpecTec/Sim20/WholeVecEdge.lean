module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeBwdQ
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateRefNull
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeCvtEdge

/-!
# `vtestop` at the spec's scalar builtins: the 2.0 script answers `0` where V2 answers `1`

The wasm-2.0 script declares `$lanes_` `hint(builtin)` with no clause
(`3-numerics.spectec:337`). `Sim.Floats.floatIntB P`, the builtins `Task.wholeStepBwdV` fixes,
interprets the scalar integer and float primitives only, so `$lanes_` denotes nothing there
(`not_callDef_lanes`). Rule 38 of `Step_pure`, `vtestop-true`, evaluates `$lanes_` in its first
premise, so it never fires (`not_body38`). Rule 39, `vtestop-false`, has the single premise
`-- otherwise`, which then holds at every `VCONST V128 c; VTESTOP sh ALL_TRUE`
(`otherwise_vtestopFalse`). So the script reduces `all_true` to `0` at **every** vector `c`
(`fires39`), including `c` with no zero lane, where V2's only step gives `1`
(`pureStep_allTrue_ones`).

This refutes the per-rule obligations that `Sim20.Whole.wholeStepBwdV_of_rest` asks for
(`not_bwdRestQ_floatIntB`). The whole-step refutations are in `WholeVecRefute`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk RuleBody DDerives otherwise otherwiseAt Fires PremW
  evalExp_tup2 evalExp_list1 evalExp_case evalExp_var)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (LhsIn otherwiseAt_of_table tags_of_take relRules ruleTags)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB)
open Silmaril.Wasm.SpecTec.Sim20.Pure (firesB20_of prems_one evalExp_caseNil evalExp_list2
  evalExp_pct)
open Silmaril.Wasm.SpecTec.Sim20.State (const0V)

set_option maxRecDepth 100000

/-! ## The two rules, verbatim -/

/-- `Step_pure/vtestop-true`, rule 38 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def vtestopTrueRule20 : Rule :=
  (Rule.ruleD "vtestop-true" [(Param.expP "c" (Typ.varT "vec_"
  [(Arg.expA (Exp.caseE "V128" (Exp.tupE [])))])), (Param.expP "Jnn" (Typ.varT "Jnn" [])), (Param.expP "N"
  (Typ.varT "N" [])), (Param.expP "ci_1*" (Typ.iterT (Typ.varT "lane_" [(Arg.expA (Exp.callE "lanetype"
  [(Arg.expA (Exp.caseE "%X%" (Exp.tupE [(Exp.subE (Exp.varE "Jnn") (Typ.varT "Jnn" []) (Typ.varT "lanetype"
  [])), (Exp.caseE "%" (Exp.tupE [(Exp.varE "N")]))])))]))]) Iter.list))] "%~>%" (Exp.tupE [(Exp.listE
  [(Exp.caseE "VCONST" (Exp.tupE [(Exp.caseE "V128" (Exp.tupE [])), (Exp.varE "c")])), (Exp.caseE "VTESTOP"
  (Exp.tupE [(Exp.caseE "%X%" (Exp.tupE [(Exp.subE (Exp.varE "Jnn") (Typ.varT "Jnn" []) (Typ.varT "lanetype"
  [])), (Exp.caseE "%" (Exp.tupE [(Exp.varE "N")]))])), (Exp.caseE "ALL_TRUE" (Exp.tupE []))]))]),
  (Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32" (Exp.tupE [])), (Exp.caseE "%" (Exp.tupE
  [(Exp.numE (Num.natN 1))]))]))])]) [(Prem.ifPr (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.iterE (Exp.varE "ci_1")
  (IterExp.mk Iter.list [(Dom.mk "ci_1" (Exp.varE "ci_1*"))])) (Exp.callE "lanes_" [(Arg.expA (Exp.caseE "%X%"
  (Exp.tupE [(Exp.subE (Exp.varE "Jnn") (Typ.varT "Jnn" []) (Typ.varT "lanetype" [])), (Exp.caseE "%"
  (Exp.tupE [(Exp.varE "N")]))]))), (Arg.expA (Exp.varE "c"))]))), (Prem.iterPr (Prem.ifPr (Exp.cmpE CmpOp.neOp OpTyp.boolT
  (Exp.projE (Exp.uncaseE (Exp.varE "ci_1") "%") (0 : Int)) (Exp.numE (Num.natN 0)))) (IterExp.mk Iter.list
  [(Dom.mk "ci_1" (Exp.varE "ci_1*"))]))])

/-- `Step_pure/vtestop-false`, rule 39 of `Step_pure` in `Scripts.Wasm20.fixed` (verbatim). -/
def vtestopFalseRule20 : Rule :=
  (Rule.ruleD "vtestop-false" [(Param.expP "c" (Typ.varT "vec_"
  [(Arg.expA (Exp.caseE "V128" (Exp.tupE [])))])), (Param.expP "Jnn" (Typ.varT "Jnn" [])), (Param.expP "N"
  (Typ.varT "N" []))] "%~>%" (Exp.tupE [(Exp.listE [(Exp.caseE "VCONST" (Exp.tupE [(Exp.caseE "V128"
  (Exp.tupE [])), (Exp.varE "c")])), (Exp.caseE "VTESTOP" (Exp.tupE [(Exp.caseE "%X%" (Exp.tupE [(Exp.subE
  (Exp.varE "Jnn") (Typ.varT "Jnn" []) (Typ.varT "lanetype" [])), (Exp.caseE "%" (Exp.tupE [(Exp.varE "N")]))])),
  (Exp.caseE "ALL_TRUE" (Exp.tupE []))]))]), (Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32"
  (Exp.tupE [])), (Exp.caseE "%" (Exp.tupE [(Exp.numE (Num.natN 0))]))]))])]) [Prem.elsePr])

section Prov

variable (B : Builtins)

/-- `vtestop-true` is rule 38 of `Step_pure`. -/
theorem hasRuleAt_vtestopTrue :
    HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 38 vtestopTrueRule20 := ⟨_, _, _, rfl, rfl, rfl⟩

/-- `vtestop-false` is rule 39 of `Step_pure`. -/
theorem hasRuleAt_vtestopFalse :
    HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 39 vtestopFalseRule20 := ⟨_, _, _, rfl, rfl, rfl⟩

end Prov

/-! ## `$lanes_` denotes nothing at the scalar builtins -/

/-- `floatIntB` does not answer `$lanes_`. -/
theorem floatIntB_lanes (P : Profile) (ws : List ArgV) :
    (Sim.Floats.floatIntB P).call "lanes_" ws = none := by
  have h : ("lanes_" : IL.Id) ∉ Sim.Floats.floatNames := by decide
  simp only [Sim.Floats.floatIntB, h, ↓reduceIte]
  unfold Sim.IntNumeric.intCall
  split <;> simp_all

/-- `$lanes_` has no clause in the 2.0 script. -/
theorem findDef_lanes20 (B : Builtins) :
    ∃ ps t, (simEnv20 B).findDef? "lanes_" = some (ps, t, []) := ⟨_, _, rfl⟩

/-! ## The environment facts the edge uses

`AllTrueEnv env` collects what the argument needs of an environment: rules 38 and 39 of
`Step_pure` are the two `vtestop` rules, the first 56 rules of `Step_pure` have the tags of the
2.0 script, and `$lanes_` has no clause and no answer. It holds of `simEnv20 (floatIntB P)`
(`allTrueEnv20`) and of the corrected script's environment (`StepFixRun`). -/

/-- The facts about an environment that make `vtestop-false` fire at every vector. -/
structure AllTrueEnv (env : Env) : Prop where
  r38 : HasRuleAt env "Step_pure" "%~>%" 38 vtestopTrueRule20
  r39 : HasRuleAt env "Step_pure" "%~>%" 39 vtestopFalseRule20
  tags : ((relRules env "Step_pure").map ruleTags).take 56 = pureTags20
  lanesDef : ∃ ps t, env.findDef? "lanes_" = some (ps, t, [])
  lanesNone : ∀ ws, env.builtins.call "lanes_" ws = none

/-- `simEnv20` at the scalar builtins. -/
theorem allTrueEnv20 (P : Profile) : AllTrueEnv (simEnv20 (Sim.Floats.floatIntB P)) where
  r38 := hasRuleAt_vtestopTrue _
  r39 := hasRuleAt_vtestopFalse _
  tags := by
    rw [relRules_simEnv20, pureTags20_eq]
    rfl
  lanesDef := findDef_lanes20 _
  lanesNone := floatIntB_lanes P

section Edge

variable {env : Env}

/-- **`$lanes_` denotes nothing.** -/
theorem not_callDef_lanes (E : AllTrueEnv env) {ρ : VarEnv} (hρ : ρ.findDef? "lanes_" = none)
    {args : List Arg} {v : Value} : ¬ CallDef env ρ "lanes_" args v := by
  obtain ⟨ps, t, hd⟩ := E.lanesDef
  exact Equiv.ExecBuiltins.not_callDef_of_nil hρ hd E.lanesNone

/-- **`vtestop-true` never fires**: its first premise evaluates `$lanes_`. -/
theorem not_body38 (E : AllTrueEnv env) {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop}
    {v : Value} : ¬ RuleBody env D els [] [] "%~>%" vtestopTrueRule20 v := by
  intro hb
  obtain ⟨σ, -, -, hp⟩ := Silmaril.Wasm.SpecTec.Sim.ruleBody_scope hb
  have h₁ := Pure.ifPrem (hp _ (List.mem_cons_self ..))
  obtain ⟨-, v₂, -, h₂, -⟩ := evalExp_cmpE_iff.1 h₁
  exact not_callDef_lanes E rfl (evalExp_callE_iff.1 h₂)

end Edge

/-! ## `vtestop-false` fires at every vector -/

/-- The vector with every bit set. -/
abbrev ones128 : Silmaril.Wasm.Numerics.V128 := BitVec.allOnes 128

/-- `v128.const c; i64x2.all_true`. -/
abbrev allTrueCode (c : Silmaril.Wasm.Numerics.V128) : List Admin :=
  [vconst c, .plain (.vecAllTrue .i64x2)]

/-- The image of `allTrueCode c`. -/
theorem adminsToV_allTrue (c : Silmaril.Wasm.Numerics.V128) :
    adminsToV (allTrueCode c) =
      [.case "VCONST" (.tuple [caseNilV "V128", pctV c.toNat]),
       .case "VTESTOP" (.tuple [.case "%X%" (.tuple [caseNilV "I64", pctV 2]),
         caseNilV "ALL_TRUE"])] := rfl

/-- The constructors of `VCONST V128 c; VTESTOP sh ALL_TRUE`. -/
theorem lhsIn_allTrue (c : Silmaril.Wasm.Numerics.V128) :
    LhsIn ["VCONST", "VTESTOP"] (.list (adminsToV (allTrueCode c))) := by
  refine Or.inl ⟨_, rfl, ?_⟩
  intro x hx op w hxw
  rw [adminsToV_allTrue] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> simp only [Value.case.injEq] at hxw <;> simp [← hxw.1]

section Edge

variable {env : Env}

/-- **`otherwise` holds for rule 39** at every `VCONST V128 c; VTESTOP (I64 X 2) ALL_TRUE`. -/
theorem otherwise_vtestopFalse (E : AllTrueEnv env) (c : Silmaril.Wasm.Numerics.V128)
    (b : Value) :
    otherwise env "Step_pure" [] 39 (.tuple [.list (adminsToV (allTrueCode c)), b]) := by
  obtain ⟨ps, t, rules, hrel, rfl, h38⟩ := E.r38
  refine otherwiseAt_of_table hrel (tags_of_take hrel E.tags) (by decide) (lhsIn_allTrue c)
    (exc := [38]) (by decide) ?_
  intro j hj _ r' hr' w _
  obtain rfl : j = 38 := List.mem_singleton.1 hj
  rw [h38] at hr'
  obtain rfl := (Option.some.inj hr').symm
  exact not_body38 E

/-- The assignment at which `vtestop-false` fires on `allTrueCode ones128`. -/
abbrev allTrueσ : List (IL.Id × Value) :=
  [("c", pctV (2 ^ 128 - 1)), ("Jnn", caseNilV "I64"), ("N", .num (.natN 2))]

/-- **`vtestop-false` fires** at `VCONST V128 ones; VTESTOP (I64 X 2) ALL_TRUE`, to `CONST I32 0`,
given the typing of its three quantifiers. -/
theorem fires39_of (E : AllTrueEnv env)
    (hq : QuantsOk env (VarEnv.empty.bindVals allTrueσ)
      [.expP "c" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]), .expP "Jnn" (.varT "Jnn" []),
        .expP "N" (.varT "N" [])]) :
    Fires env "Step_pure" 39
      (.tuple [.list (adminsToV (allTrueCode ones128)), .list (adminsToV [constI32 0])]) :=
  Pure.fires_of_ruleAt E.r39 allTrueσ hq ⟨100, by with_unfolding_all rfl⟩
    (prems_one (.elsePr (otherwise_vtestopFalse E ones128 _)))

end Edge

/-- **`vtestop-false` fires** at `VCONST V128 ones; VTESTOP (I64 X 2) ALL_TRUE`, to
`CONST I32 0`, at the scalar builtins. -/
theorem fires39 (P : Profile) :
    Fires (simEnv20 (Sim.Floats.floatIntB P)) "Step_pure" 39
      (.tuple [.list (adminsToV (allTrueCode ones128)), .list (adminsToV [constI32 0])]) := by
  refine fires39_of (allTrueEnv20 P) ?_
  refine QuantsOk.cons rfl ?_ (QuantsOk.cons rfl ?_ (QuantsOk.cons rfl ?_ QuantsOk.nil))
  · exact ⟨100, by with_unfolding_all rfl⟩
  · exact ⟨100, by with_unfolding_all rfl⟩
  · exact ⟨100, by with_unfolding_all rfl⟩

/-! ## V2 answers `1` -/

/-- The two `i64` lanes of `ones128`. -/
theorem lanes_ones : IntShape.i64x2.lanesOf ones128 = [BitVec.allOnes 64, BitVec.allOnes 64] := by
  simp only [ones128, IntShape.lanesOf, Silmaril.Wasm.Numerics.lanesW, IntShape.laneWidth, IntShape.lanes,
    Silmaril.Wasm.Numerics.lanesNat, BitVec.toNat_allOnes]
  constructor

/-- No lane of `ones128` is zero. -/
theorem lanes_ones_ne : ¬ ∃ l ∈ IntShape.i64x2.lanesOf ones128, l = 0 := by
  rw [lanes_ones]
  rintro ⟨l, hl, rfl⟩
  change (0 : BitVec 64) ∈ [BitVec.allOnes 64, BitVec.allOnes 64] at hl
  revert hl
  decide

set_option linter.unusedTactic false in
/-- **V2's only step from `v128.const ones; i64x2.all_true` gives `1`.** -/
theorem pureStep_allTrue_ones {P : Profile} {code' : List Admin}
    (h : PureStep P (allTrueCode ones128) code') : code' = [constI32 1] := by
  generalize hc : allTrueCode ones128 = c at h
  cases h <;> try simp_all [vals, constI32, aref, vconst]
  case trapVals =>
    have hm : Admin.trap ∈ allTrueCode ones128 := by rw [hc]; simp
    simp [allTrueCode] at hm
  case vecAllTrueFalse _ _ h =>
    obtain ⟨rfl, rfl⟩ := hc
    exact absurd ⟨0, h, rfl⟩ lanes_ones_ne

/-- No `Step_pure` rule applies to `i64x2.all_true` alone. -/
theorem not_pureStep_allTrue1 {P : Profile} {code' : List Admin} :
    ¬ PureStep P [.plain (.vecAllTrue .i64x2)] code' := by
  intro h
  generalize hc : [Admin.plain (.vecAllTrue .i64x2)] = c at h
  cases h <;> simp_all [vals, constI32, aref, vconst]
  case trapVals =>
    have hm : Admin.trap ∈ [Admin.plain (.vecAllTrue .i64x2)] := by rw [hc]; simp
    simp at hm

/-- No `Step_read` rule applies to `v128.const ones; i64x2.all_true`, nor to `i64x2.all_true`. -/
theorem not_readStep_allTrue {H : Type} {s : Store H} {f : Frame} {code code' : List Admin}
    (hc : code = allTrueCode ones128 ∨ code = [.plain (.vecAllTrue .i64x2)]) :
    ¬ ReadStep s f code code' := by
  intro h
  cases h <;> simp_all [vals, constI32, vconst]
  all_goals
    rcases hc with hc | hc <;>
      · have hl := congrArg List.getLast? hc
        simp [allTrueCode] at hl

/-- The context split of `v128.const ones; i64x2.all_true` or of `i64x2.all_true`: the non-value
part is `i64x2.all_true` alone. -/
theorem split_allTrue {vs : List Val} {is rest : List Admin} (hall : is.all Admin.isVal = false)
    (hne : vs ≠ [] ∨ rest ≠ [])
    (h : vals vs ++ is ++ rest = allTrueCode ones128 ∨
      vals vs ++ is ++ rest = [.plain (.vecAllTrue .i64x2)]) :
    is = [.plain (.vecAllTrue .i64x2)] := by
  rcases vs with _ | ⟨v, _ | ⟨v', vs⟩⟩ <;> rcases is with _ | ⟨i₁, _ | ⟨i₂, is⟩⟩ <;>
    simp_all [vals, allTrueCode, Admin.isVal, Admin.val?]

/-- The conclusion of `step_allTrue`, for a step from `is` to `is'`. -/
def AllTrueInv (is is' : List Admin) : Prop :=
  (is = allTrueCode ones128 → is' = [constI32 1]) ∧ is ≠ [.plain (.vecAllTrue .i64x2)]

/-- `Step_pure` steps satisfy `AllTrueInv`. -/
theorem allTrueInv_pure {P : Profile} {is is' : List Admin} (hp : PureStep P is is') :
    AllTrueInv is is' :=
  ⟨fun hc => pureStep_allTrue_ones (hc ▸ hp), fun hc => not_pureStep_allTrue1 (hc ▸ hp)⟩

/-- `Step_read` steps satisfy `AllTrueInv` vacuously. -/
theorem allTrueInv_read {H : Type} {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') : AllTrueInv is is' :=
  ⟨fun hc => absurd hr (not_readStep_allTrue (.inl hc)),
    fun hc => not_readStep_allTrue (.inr hc) hr⟩

/-- Code ending in `CALL_ADDR` is neither of the two codes. -/
theorem allTrueInv_callAddr (vs : List Val) (a : FuncAddr) (is' : List Admin) :
    AllTrueInv (vals vs ++ [.callAddr a]) is' := by
  have hl : ∀ l : List Admin, vals vs ++ [.callAddr a] = l → l.getLast? = some (.callAddr a) :=
    fun l hl => by rw [← hl]; simp
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · exact absurd (hl _ hc) (by simp [allTrueCode])
  · exact absurd (hl _ hc) (by simp)

/-- Code of one label or frame is neither of the two codes. -/
theorem allTrueInv_single {a : Admin} (ha : ∀ sh, a ≠ .plain (.vecAllTrue sh))
    (is' : List Admin) : AllTrueInv [a] is' :=
  ⟨fun hc => absurd hc (by simp [allTrueCode]), fun hc => ha _ (List.singleton_inj.1 hc)⟩

/-- **V2's only step from `v128.const ones; i64x2.all_true` gives `1`**, and `i64x2.all_true`
alone does not step. -/
theorem step_allTrue {H : Type} {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : AllTrueInv c.code c'.code := by
  induction h with
  | pure hp => exact allTrueInv_pure hp
  | read hr => exact allTrueInv_read hr
  | ctxtInstrs hs hne ih =>
    exact ⟨fun hc => (ih.2 (split_allTrue hs.not_allVals hne (.inl hc))).elim,
      fun hc => ih.2 (split_allTrue hs.not_allVals hne (.inr hc))⟩
  | ctxtLabel _ _ => exact allTrueInv_single (fun _ => by simp) _
  | ctxtFrame _ _ => exact allTrueInv_single (fun _ => by simp) _
  | callAddrHost => exact allTrueInv_callAddr _ _ _
  | callAddrHostDiv => exact allTrueInv_callAddr _ _ _
  | _ => exact ⟨fun hc => by simp [allTrueCode, constI32, vconst] at hc, by simp [constI32]⟩

/-! ## The per-rule obligations, refuted -/

set_option maxHeartbeats 4000000 in
/-- `v128.const ones; i64x2.all_true` is a typed `instr*`. -/
theorem typed_allTrue (B : Builtins) :
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV (allTrueCode ones128))) :=
  ⟨VarEnv.empty, ⟨rfl, rfl, rfl⟩, 100, by with_unfolding_all rfl⟩

/-- **The `Step_pure` obligation fails at `v128.const ones; i64x2.all_true`**: the script steps to
`i32.const 0`, V2 only to `i32.const 1`. -/
theorem not_pureObl_allTrue {P : Profile} :
    ¬ ∃ code', adminsToV [constI32 0] = adminsToV code' ∧
      PureStep P (allTrueCode ones128) code' := by
  rintro ⟨code', hw, hs⟩
  rw [pureStep_allTrue_ones hs] at hw
  simp [adminsToV, adminToV, instrToV, valV, numV, pctV] at hw

/-- **What `wholeStepBwdV_of_rest` asks for is false**: at the spec's scalar builtins, rule 39 of
`Step_pure` (`vtestop-false`) fires where V2 does not take the step, so `BwdRestQ CvtOkL` fails at
every encoding, host and profile. -/
theorem not_bwdRestQ_floatIntB {H : Type} (hn : H → String) (host : HostSemantics H)
    (P : Profile) : ¬ BwdRestQ CvtOkL (Sim.Floats.floatIntB P) hn P host := by
  intro R
  exact not_pureObl_allTrue (R.pure 39 (by decide) (by decide) _ _ (by simp [CvtOkL, CvtOkA])
    (typed_allTrue _) typed_const0 (fires39 P))

end Silmaril.Wasm.SpecTec.Sim20.Whole

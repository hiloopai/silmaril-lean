module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.ReadMS
public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Defs

/-!
# Round 7, memory SIMD: round 6's backend transfer at `configVD`

Round 6's transfer lemma (`Round6.Transfer.sstepB_iff_of_not_castRedex`) says that away from
cast redexes the backend reading `Round6.Reading.SStepB` and the declarative `SStep` have the
same successors at the `configV` image of every Core configuration. This file re-runs it at
`configVD`, where memory SIMD code is encoded against the IL type `instr` at every depth, in the
code and in the store's function bodies:

* `castShape_of_body_readK`: the eight cast rules of `Step_read` (2–5, 65–68) have a left-hand
  side of the shape `s; f; ref cast-instr`, under any interpretation of their premises, at **any**
  left-hand side value (round 6 states the same fact at `configV` images only);
* `castRedex_of_lhsD`: at a `configVD` image, that shape is a cast redex (`adminToVD_case`,
  `ref_of_typedD`);
* `sReadB_iff_noCastD`: `Step_read` is the same relation under both readings at the `configVD`
  image of a configuration whose redex is not a cast;
* `SubInstD`, `inst_ctxtInstrsD` … `inst_ctxtFrameD`: the instances of the context rules at a
  `configVD` image are at a smaller configuration, from round 6's `inst_*_shape` and G4's
  decoders `StructDecodeD`;
* `sstepB_iff_of_not_castRedexD`, `transferD_backend`: **the transfer at `configVD`**, for every
  `B` and encoding, with no hypothesis beyond the absence of a cast redex.

The memory SIMD rules need no special treatment: they are not cast rules, so they are plain in
`Step_read` (`Round6.Transfer.plain_read_of_not_mem`) and in `Step` (`firesB_step_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.ExecStepRules
  (readRule ctxtInstrsRule ctxtLabelRule ctxtHandlerRule ctxtFrameRule)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round6.Reading
open Round6.Transfer (TailFree tailFree_single tailFree_nil inst_read inst_ctxtInstrs_shape
  inst_ctxtLabel_shape inst_ctxtHandler_shape inst_ctxtFrame_shape firesB_iff_swap
  relRules_read)
open Round6.Target (CastRedex castInstr)
open Round5.Read (head_refTest head_refCast head_brOnCast head_brOnCastFail readDoneK)
open Bwd (codeSize stV_inj)

variable {H : Type} {hn : H → String} {B : Builtins}

/-! ## The cast rules, at any left-hand side -/

/-- **The shape of a cast rule's left-hand side**: a state, then a typed reference followed by an
instruction whose constructor is a cast's. -/
def CastShape (B : Builtins) (a : Value) : Prop :=
  ∃ (σ : List (IL.Id × Value)) (S F R W : Value) (op : MixopS), op ∈ castTags ∧
    HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R ∧
    a = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]), .list [R, .case op W]])

/-- `ref.test` and `ref.cast` (65–68) and `br_on_cast*` (2–5): the conclusion's left-hand side,
read back, at any value. -/
theorem castShape_of_body {D : Interp} {els : Prop} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} {op : MixopS} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" (.ruleD nm qs "%~>%" e prems) (.tuple [a, w]))
    (hshape : ∀ σ, QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs →
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) e (.tuple [a, w]) →
      ∃ S F R W, HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R ∧
        a = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]), .list [R, .case op W]]))
    (hop : op ∈ castTags) : CastShape B a := by
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope hb
  obtain ⟨S, F, R, W, hR, hcw⟩ := hshape σ hq he
  exact ⟨σ, S, F, R, W, op, hop, hR, hcw⟩

/-- `ref.test-true` (65). -/
theorem castShape_65 {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" refTestTrueRule (.tuple [a, w])) :
    CastShape B a := by
  refine castShape_of_body (op := "REF.TEST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, RT, hR, by concl_inv hl⟩

/-- `ref.test-false` (66). -/
theorem castShape_66 {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" refTestFalseRule (.tuple [a, w])) :
    CastShape B a := by
  refine castShape_of_body (op := "REF.TEST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, RT, hR, by concl_inv hl⟩

/-- `ref.cast-succeed` (67). -/
theorem castShape_67 {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" refCastSucceedRule (.tuple [a, w])) :
    CastShape B a := by
  refine castShape_of_body (op := "REF.CAST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, RT, hR, by concl_inv hl⟩

/-- `ref.cast-fail` (68). -/
theorem castShape_68 {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" refCastFailRule (.tuple [a, w])) :
    CastShape B a := by
  refine castShape_of_body (op := "REF.CAST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, RT, hR, by concl_inv hl⟩

/-- `br_on_cast-succeed` (2). -/
theorem castShape_2 {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" brOnCastSucceedRule (.tuple [a, w])) :
    CastShape B a := by
  refine castShape_of_body (op := "BR_ON_CAST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, .tuple [L, RT₁, RT₂], hR, by concl_inv hl⟩

/-- `br_on_cast-fail` (3). -/
theorem castShape_3 {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" brOnCastFailRule (.tuple [a, w])) :
    CastShape B a := by
  refine castShape_of_body (op := "BR_ON_CAST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, .tuple [L, RT₁, RT₂], hR, by concl_inv hl⟩

/-- `br_on_cast_fail-succeed` (4). -/
theorem castShape_4 {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" brOnCastFailSucceedRule (.tuple [a, w])) :
    CastShape B a := by
  refine castShape_of_body (op := "BR_ON_CAST_FAIL") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, .tuple [L, RT₁, RT₂], hR, by concl_inv hl⟩

/-- `br_on_cast_fail-fail` (5). -/
theorem castShape_5 {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" brOnCastFailFailRule (.tuple [a, w])) :
    CastShape B a := by
  refine castShape_of_body (op := "BR_ON_CAST_FAIL") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, .tuple [L, RT₁, RT₂], hR, by concl_inv hl⟩

/-- **The cast rules of `Step_read` fire only at a cast-shaped left-hand side, under any
interpretation of their premises.** -/
theorem castShape_of_body_readK {i : Nat} (hi : i ∈ readDoneK) {ps : List Param} {op : MixopS}
    {t : Typ} {rules : List Rule}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules)) {r : Rule}
    (hr : rules[i]? = some r) {D : Interp} {els : Prop} {a w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" r (.tuple [a, w])) : CastShape B a := by
  have RR := State.hasReadRules_simEnv B
  simp only [readDoneK, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.brOnCastSucceed hrel))
    exact castShape_2 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.brOnCastFail hrel))
    exact castShape_3 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.brOnCastFailSucceed hrel))
    exact castShape_4 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.brOnCastFailFail hrel))
    exact castShape_5 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.refTestTrue hrel))
    exact castShape_65 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.refTestFalse hrel))
    exact castShape_66 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.refCastSucceed hrel))
    exact castShape_67 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.refCastFail hrel))
    exact castShape_68 hb

/-! ## At `configVD` -/

/-- A typed reference at `adminToVD` is a reference. -/
theorem ref_of_typedD {ρ : VarEnv} (hρ : ValsOnly ρ) {a : Admin}
    (h : HasTyp (simEnv B) ρ (.varT "ref" []) (adminToVD a)) : ∃ r : Ref, a = .ref r := by
  obtain ⟨op, w, hw, hop⟩ := BwdPureStep.head_of_typed_ref hρ h
  exact BwdPureStep.head_ref ((adminToVD_case hw) ▸ hop)

/-- **A cast-shaped `configVD` image is a cast redex.** -/
theorem castRedex_of_lhsD {c : Config H} (h : CastShape B (configVD hn c)) : CastRedex c.code := by
  obtain ⟨σ, S, F, R, W, op, hop, hR, h⟩ := h
  obtain ⟨s, f, is⟩ := c
  obtain ⟨-, hcode⟩ := configVD_cfgV (z := .case "%;%" (.tuple [S, F])) (is := [R, .case op W]) h
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToVD_eq_pair hcode.symm
  obtain ⟨r, rfl⟩ := ref_of_typedD (valsOnly_bindVals σ) (h₁ ▸ hR)
  have hh : Typing.adminHead a₂ = op := (adminToVD_case h₂).symm
  have hi : ∃ i, a₂ = .plain i ∧ castInstr i = true := by
    simp only [castTags, List.mem_cons, List.mem_nil_iff, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl
    · obtain ⟨l, rt₁, rt₂, rfl⟩ := head_brOnCast hh
      exact ⟨_, rfl, rfl⟩
    · obtain ⟨l, rt₁, rt₂, rfl⟩ := head_brOnCastFail hh
      exact ⟨_, rfl, rfl⟩
    · obtain ⟨rt, rfl⟩ := head_refTest hh
      exact ⟨_, rfl, rfl⟩
    · obtain ⟨rt, rfl⟩ := head_refCast hh
      exact ⟨_, rfl, rfl⟩
  obtain ⟨i, rfl, hc⟩ := hi
  exact Round6.Target.castRedex_pair hc

/-- **`Step_read` is plain or dead at the `configVD` image of a configuration whose redex is not
a cast.** -/
theorem closedAt_noCastD {c : Config H} (hc : ¬ CastRedex c.code) :
    ClosedAt (simEnv B) (· ∈ ["Expand"]) "Step_read" (configVD hn c) := by
  intro ps op t rules hrel r hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
  have hrr := relRules_read hrel
  by_cases hk : i ∈ readDoneK
  · exact .inr fun D els b hb => hc (castRedex_of_lhsD (castShape_of_body_readK hk hrel hi
      (ruleBody_of_ruleBodyB (noOpt_read (hrr ▸ hr)) hb)))
  · exact .inl (Round6.Transfer.plain_read_of_not_mem (hrr ▸ hi) hk)

/-- **Away from cast redexes, `Step_read` is the same relation under both readings**, at the
`configVD` image of a configuration. -/
theorem sReadB_iff_noCastD {c : Config H} (hc : ¬ CastRedex c.code) {b : Value} :
    DDerivesB (simEnv B) (otherwiseB (simEnv B)) "Step_read" "%~>%" []
        (.tuple [configVD hn c, b]) ↔
      DDerives (simEnv B) (otherwise (simEnv B)) "Step_read" "%~>%" []
        (.tuple [configVD hn c, b]) := by
  obtain ⟨t, rules, hrel⟩ := findRel_read B
  exact dderivesB_iff_at (closed_expand B) hrel (closedAt_noCastD hc)

/-! ## The context rules' instances at `configVD` -/

/-- **The premise of a context rule is at a smaller configuration**, at `configVD`. -/
def SubInstD (hn : H → String) (c : Config H) (w : Value) : Prop :=
  ∃ (c' : Config H) (u : Value), w = .tuple [configVD hn c', u] ∧
    codeSize c'.code < codeSize c.code ∧ (¬ CastRedex c.code → ¬ CastRedex c'.code)

/-- `ctxt-instrs` (2), at a `configVD` image. -/
theorem inst_ctxtInstrsD {env : Env} (SD : StructDecodeD env) {D : Interp} {els : Prop}
    {c : Config H} {b w : Value}
    (h : Round6.Transfer.Inst env D els ctxtInstrsRule (.tuple [configVD hn c, b]) w) : SubInstD hn c w := by
  obtain ⟨z, z', vs, is, is', rest, ⟨ρ, hρ, hvs⟩, hne, h₁, hw⟩ := inst_ctxtInstrs_shape h
  obtain ⟨s, f, code⟩ := c
  have e₁ := configVD_cfgV h₁
  obtain ⟨A, I, R, hcode, hA, hI, hR⟩ := adminsToVD_split3 e₁.2.symm
  change code = A ++ I ++ R at hcode
  obtain ⟨vs₀, hv₀⟩ : ∃ vs₀, A = vals vs₀ := SD.vals ρ A hρ (hA ▸ hvs)
  have hneA : A ≠ [] ∨ R ≠ [] :=
    hne.imp (fun h he => h (by rw [← hA, he]; rfl)) (fun h he => h (by rw [← hR, he]; rfl))
  have e₂ : cfgV z is = configVD hn ⟨s, f, I⟩ := by rw [configVD_eq, e₁.1, hI]; rfl
  have hsz : codeSize I < codeSize code := hcode ▸ Bwd.codeSize_mid hneA
  have hcr : ¬ CastRedex code → ¬ CastRedex I := fun hnc =>
    Round6.Target.not_castRedex_mid (vs := vs₀) (c := R) (hv₀ ▸ hcode ▸ hnc)
  exact ⟨⟨s, f, I⟩, cfgV z' is', by rw [hw, e₂], hsz, hcr⟩

/-- `ctxt-label` (3), at a `configVD` image. -/
theorem inst_ctxtLabelD {env : Env} (SD : StructDecodeD env) {D : Interp} {els : Prop}
    {c : Config H} {b w : Value}
    (h : Round6.Transfer.Inst env D els ctxtLabelRule (.tuple [configVD hn c, b]) w) : SubInstD hn c w := by
  obtain ⟨z, z', m, cont, is, is', h₁, hw⟩ := inst_ctxtLabel_shape h
  obtain ⟨s, f, code⟩ := c
  have e₁ := configVD_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := SD.label a _ ha
  have hp : adminsToVD body = is := by
    simp only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] at ha
    exact ha.2.2
  have e₂ : cfgV z is = configVD hn ⟨s, f, body⟩ := by rw [configVD_eq, e₁.1, hp]; rfl
  exact ⟨⟨s, f, body⟩, cfgV z' is', by rw [hw, e₂], Bwd.codeSize_label k cont₀ body,
    Round6.Target.not_castRedex_label⟩

/-- `ctxt-handler` (4), at a `configVD` image. -/
theorem inst_ctxtHandlerD {env : Env} (SD : StructDecodeD env) {D : Interp} {els : Prop}
    {c : Config H} {b w : Value}
    (h : Round6.Transfer.Inst env D els ctxtHandlerRule (.tuple [configVD hn c, b]) w) : SubInstD hn c w := by
  obtain ⟨z, z', m, cs, is, is', h₁, hw⟩ := inst_ctxtHandler_shape h
  obtain ⟨s, f, code⟩ := c
  have e₁ := configVD_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single e₁.2.symm
  obtain ⟨k, cs₀, body, rfl⟩ := SD.handler a _ ha
  have hp : adminsToVD body = is := by
    simp only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] at ha
    exact ha.2.2
  have e₂ : cfgV z is = configVD hn ⟨s, f, body⟩ := by rw [configVD_eq, e₁.1, hp]; rfl
  exact ⟨⟨s, f, body⟩, cfgV z' is', by rw [hw, e₂], Bwd.codeSize_handler k cs₀ body,
    Round6.Target.not_castRedex_handler⟩

/-- `ctxt-frame` (5), at a `configVD` image. -/
theorem inst_ctxtFrameD {env : Env} (SD : StructDecodeD env) {D : Interp} {els : Prop}
    {c : Config H} {b w : Value}
    (h : Round6.Transfer.Inst env D els ctxtFrameRule (.tuple [configVD hn c, b]) w) : SubInstD hn c w := by
  obtain ⟨sv, sv', fv, fr, fr', m, is, is', h₁, hw⟩ := inst_ctxtFrame_shape h
  obtain ⟨s, f, code⟩ := c
  have e₁ := configVD_cfgV h₁
  have e₀ : sv = storeVD hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := SD.frame a _ ha
  have hp : frameV fi = fr ∧ adminsToVD body = is := by
    simp only [adminToVD, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] at ha
    exact ha.2
  have e₂ : cfgV (stV sv fr) is = configVD hn ⟨s, fi, body⟩ := by
    rw [configVD_eq, e₀.1, ← hp.1, hp.2]
  exact ⟨⟨s, fi, body⟩, cfgV (stV sv' fr') is', by rw [hw, e₂], Bwd.codeSize_frame k fi body,
    Round6.Target.not_castRedex_frame⟩

/-! ## The transfer, by recursion on the size of the code -/

/-- A `SubInstD` premise instance, read by the recursion. -/
theorem sub_iffD {c : Config H} (hc : ¬ CastRedex c.code)
    (ih : ∀ (c' : Config H) (w : Value), codeSize c'.code < codeSize c.code →
      ¬ CastRedex c'.code →
        (SStepB (simEnv B) (configVD hn c') w ↔ SStep (simEnv B) (configVD hn c') w))
    {w : Value} (h : SubInstD hn c w) :
    DDerivesB (simEnv B) (otherwiseB (simEnv B)) "Step" "%~>%" [] w ↔
      DDerives (simEnv B) (otherwise (simEnv B)) "Step" "%~>%" [] w := by
  obtain ⟨c', u, rfl, hlt, hcc⟩ := h
  exact ih c' u hlt (hcc hc)

/-- `read`'s premise instance, at the `configVD` image of a configuration without a cast
redex. -/
theorem read_inst_iffD {c : Config H} (hc : ¬ CastRedex c.code) {D : Interp} {els : Prop}
    {w w' : Value} (hi : Round6.Transfer.Inst (simEnv B) D els readRule (.tuple [configVD hn c, w]) w') :
    DDerivesB (simEnv B) (otherwiseB (simEnv B)) "Step_read" "%~>%" [] w' ↔
      DDerives (simEnv B) (otherwise (simEnv B)) "Step_read" "%~>%" [] w' := by
  obtain ⟨u, hu⟩ := inst_read hi
  rw [hu]
  exact sReadB_iff_noCastD hc

/-- **One rule of `Step` at the `configVD` image of a configuration without a cast redex**, given
the transfer at smaller code. -/
theorem firesStep_iff_noCastD {c : Config H} (hc : ¬ CastRedex c.code)
    (ih : ∀ (c' : Config H) (w : Value), codeSize c'.code < codeSize c.code →
      ¬ CastRedex c'.code →
        (SStepB (simEnv B) (configVD hn c') w ↔ SStep (simEnv B) (configVD hn c') w))
    (i : Nat) {w : Value} :
    FiresB (simEnv B) "Step" i (.tuple [configVD hn c, w]) ↔
      Fires (simEnv B) "Step" i (.tuple [configVD hn c, w]) := by
  have R : Equiv.ExecStepRules.HasStepRules (simEnv B) := hasStepRules_simEnv B
  have SD : StructDecodeD (simEnv B) := structDecodeD_simEnv B
  match i with
  | 0 => exact firesB_step_iff B (.inl rfl)
  | 1 => exact firesB_iff_swap R.read rfl tailFree_nil (fun _ hi => read_inst_iffD hc hi)
  | 2 =>
    exact firesB_iff_swap R.ctxtInstrs rfl (tailFree_single ⟨rfl, rfl⟩)
      (fun _ hi => sub_iffD hc ih (inst_ctxtInstrsD SD hi))
  | 3 =>
    exact firesB_iff_swap R.ctxtLabel rfl tailFree_nil
      (fun _ hi => sub_iffD hc ih (inst_ctxtLabelD SD hi))
  | 4 =>
    exact firesB_iff_swap R.ctxtHandler rfl tailFree_nil
      (fun _ hi => sub_iffD hc ih (inst_ctxtHandlerD SD hi))
  | 5 =>
    exact firesB_iff_swap R.ctxtFrame rfl tailFree_nil
      (fun _ hi => sub_iffD hc ih (inst_ctxtFrameD SD hi))
  | k + 6 => exact firesB_step_iff B (.inr (Nat.le_add_left 6 k))

/-- The recursion on the size of the code, at `configVD`. -/
theorem sstepB_iff_ltD (B : Builtins) (hn : H → String) :
    ∀ (n : Nat) (c : Config H) (w : Value), codeSize c.code < n → ¬ CastRedex c.code →
      (SStepB (simEnv B) (configVD hn c) w ↔ SStep (simEnv B) (configVD hn c) w)
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, c, w, hlt, hc => by
    obtain ⟨t, rules, hrel⟩ := Bwd.findRel_of_ruleAt (hasStepRules_simEnv B).pure
    have ih : ∀ (c' : Config H) (w' : Value), codeSize c'.code < codeSize c.code →
        ¬ CastRedex c'.code →
          (SStepB (simEnv B) (configVD hn c') w' ↔ SStep (simEnv B) (configVD hn c') w') :=
      fun c' w' h' hc' =>
        sstepB_iff_ltD B hn n c' w' (Nat.lt_of_lt_of_le h' (Nat.le_of_lt_succ hlt)) hc'
    have hB : SStepB (simEnv B) (configVD hn c) w ↔
        ∃ i, FiresB (simEnv B) "Step" i (.tuple [configVD hn c, w]) := dderivesB_iff_firesB hrel
    have hD : SStep (simEnv B) (configVD hn c) w ↔
        ∃ i, Fires (simEnv B) "Step" i (.tuple [configVD hn c, w]) := dderives_iff_fires hrel
    exact hB.trans ((exists_congr fun i => firesStep_iff_noCastD hc ih i).trans hD.symm)

/-- **The backend reading is the declarative one away from cast redexes, at `configVD`**: at the
`configVD` image of a Core configuration whose redex is not a cast, `SStepB` and `SStep` have the
same successors, for every `B` and every encoding. Memory SIMD code may occur anywhere, in the
code and in the store. -/
theorem sstepB_iff_of_not_castRedexD (B : Builtins) (hn : H → String) {c : Config H}
    (hc : ¬ CastRedex c.code) (w : Value) :
    SStepB (simEnv B) (configVD hn c) w ↔ SStep (simEnv B) (configVD hn c) w :=
  sstepB_iff_ltD B hn _ c w (Nat.lt_succ_self _) hc

/-- **`Round6.Transfer.transfer_backend` at `configVD`**: for every `B` (in particular the
round-7 builtins `withVBytes (Prims.builtins …)` and round 6's `BI`), the `Int.backend` step from
the `configVD` image of a configuration without a cast redex is the declarative one, both ways. -/
theorem transferD_backend (B : Builtins) (hn : H → String) {c : Config H}
    (hc : ¬ CastRedex c.code) (w : Value) :
    Round6.Int.backend.step B (configVD hn c) w ↔ SStep (simEnv B) (configVD hn c) w :=
  sstepB_iff_of_not_castRedexD B hn hc w

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

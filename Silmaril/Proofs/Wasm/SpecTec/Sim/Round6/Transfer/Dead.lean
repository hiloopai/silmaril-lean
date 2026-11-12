module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Transfer.Script
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# Round 6: away from cast redexes, `Step_read` is the same under both readings

`castRedex_of_fires_readK` says the eight cast rules of `Step_read` (2–5, 65–68)
fire only on cast redexes, for `Fires`. Its proofs read only the rules' conclusions and the
typing of the bound reference, so they hold for **any** interpretation of the premises
(`castRedex_of_body_readK`): at the image of a configuration whose redex is not a cast, each of
the eight is `DeadAt`. With `plain_read_of_not_mem` for the other rules, `Step_read` is
`ClosedAt` such a left-hand side (`closedAt_noCast`), and `dderivesB_iff_at`
gives `sReadB_iff_noCast`: **`SReadB` and `SRead` agree at the image of every configuration whose
redex is not a cast**, whatever casts its code holds after the redex.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Transfer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Reading
open Target (CastRedex castInstr)
open Round5.Read (cast_inv head_refTest head_refCast head_brOnCast head_brOnCastFail readDoneK)

variable {H : Type} {hn : H → String} {B : Builtins}

/-- **The left-hand side of a cast rule is a cast redex**: a reference followed by an
instruction whose constructor is a cast's. -/
theorem castRedex_of_lhs {σ : List (IL.Id × Value)} {c : Config H} {S F R W : Value}
    {op : MixopS} (hop : op ∈ castTags)
    (hR : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R)
    (h : configV hn c = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case op W]])) : CastRedex c.code := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨-, -, r, a, rfl, -, ha⟩ := cast_inv hR h
  have hh : Typing.adminHead a = op := (Typing.adminToV_case ha).symm
  have hi : ∃ i, a = .plain i ∧ castInstr i = true := by
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
  exact Target.castRedex_pair hc

/-- `ref.test` and `ref.cast` (65–68): the conclusion's left-hand side, read back. -/
theorem lhs_of_testLike {D : Interp} {els : Prop} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem} {op : MixopS} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" (.ruleD nm qs "%~>%" e prems)
      (.tuple [configV hn c, w]))
    (hshape : ∀ σ, QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs →
      EvalExp (simEnv B) (VarEnv.empty.bindVals σ) e (.tuple [configV hn c, w]) →
      ∃ S F R W, HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R ∧
        configV hn c = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]), .list [R, .case op W]]))
    (hop : op ∈ castTags) : CastRedex c.code := by
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope hb
  obtain ⟨S, F, R, W, hR, hcw⟩ := hshape σ hq he
  exact castRedex_of_lhs hop hR hcw

/-- `ref.test-true` (65). -/
theorem castRedex_of_65 {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" refTestTrueRule (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  refine lhs_of_testLike (op := "REF.TEST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, RT, hR, by concl_inv hl⟩

/-- `ref.test-false` (66). -/
theorem castRedex_of_66 {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" refTestFalseRule (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  refine lhs_of_testLike (op := "REF.TEST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, RT, hR, by concl_inv hl⟩

/-- `ref.cast-succeed` (67). -/
theorem castRedex_of_67 {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" refCastSucceedRule
      (.tuple [configV hn c, w])) : CastRedex c.code := by
  refine lhs_of_testLike (op := "REF.CAST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, RT, hR, by concl_inv hl⟩

/-- `ref.cast-fail` (68). -/
theorem castRedex_of_68 {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" refCastFailRule (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  refine lhs_of_testLike (op := "REF.CAST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, RT, hR, by concl_inv hl⟩

/-- `br_on_cast-succeed` (2). -/
theorem castRedex_of_2 {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" brOnCastSucceedRule
      (.tuple [configV hn c, w])) : CastRedex c.code := by
  refine lhs_of_testLike (op := "BR_ON_CAST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, .tuple [L, RT₁, RT₂], hR, by concl_inv hl⟩

/-- `br_on_cast-fail` (3). -/
theorem castRedex_of_3 {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" brOnCastFailRule
      (.tuple [configV hn c, w])) : CastRedex c.code := by
  refine lhs_of_testLike (op := "BR_ON_CAST") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, .tuple [L, RT₁, RT₂], hR, by concl_inv hl⟩

/-- `br_on_cast_fail-succeed` (4). -/
theorem castRedex_of_4 {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" brOnCastFailSucceedRule
      (.tuple [configV hn c, w])) : CastRedex c.code := by
  refine lhs_of_testLike (op := "BR_ON_CAST_FAIL") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, .tuple [L, RT₁, RT₂], hR, by concl_inv hl⟩

/-- `br_on_cast_fail-fail` (5). -/
theorem castRedex_of_5 {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" brOnCastFailFailRule
      (.tuple [configV hn c, w])) : CastRedex c.code := by
  refine lhs_of_testLike (op := "BR_ON_CAST_FAIL") hb (fun σ hq he => ?_) (by decide)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  exact ⟨S, F, R, .tuple [L, RT₁, RT₂], hR, by concl_inv hl⟩

/-- **The cast rules of `Step_read` fire only on cast redexes, under any interpretation of their
premises** (`Target.castRedex_of_fires_readK`, for every `RuleBody`). -/
theorem castRedex_of_body_readK {i : Nat} (hi : i ∈ readDoneK) {ps : List Param} {op : MixopS}
    {t : Typ} {rules : List Rule}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules)) {r : Rule}
    (hr : rules[i]? = some r) {D : Interp} {els : Prop} {c : Config H} {w : Value}
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" r (.tuple [configV hn c, w])) :
    CastRedex c.code := by
  have RR := State.hasReadRules_simEnv B
  simp only [readDoneK, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.brOnCastSucceed hrel))
    exact castRedex_of_2 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.brOnCastFail hrel))
    exact castRedex_of_3 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.brOnCastFailSucceed hrel))
    exact castRedex_of_4 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.brOnCastFailFail hrel))
    exact castRedex_of_5 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.refTestTrue hrel))
    exact castRedex_of_65 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.refTestFalse hrel))
    exact castRedex_of_66 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.refCastSucceed hrel))
    exact castRedex_of_67 hb
  · obtain rfl := Option.some.inj (hr.symm.trans (ruleAt_get RR.refCastFail hrel))
    exact castRedex_of_68 hb

/-- The rules of `Step_read` in `simEnv B` are the pinned script's. -/
theorem relRules_read {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules)) :
    RefsGC.relRules (envOfScript Specs.wasm30) "Step_read" = rules := by
  simp only [RefsGC.relRules, ← simEnv_findRel B, hrel]

/-- **`Step_read` is plain or dead at the image of a configuration whose redex is not a
cast.** -/
theorem closedAt_noCast {c : Config H} (hc : ¬ CastRedex c.code) :
    ClosedAt (simEnv B) (· ∈ ["Expand"]) "Step_read" (configV hn c) := by
  intro ps op t rules hrel r hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
  have hrr := relRules_read hrel
  by_cases hk : i ∈ readDoneK
  · exact .inr fun D els b hb => hc (castRedex_of_body_readK hk hrel hi
      (ruleBody_of_ruleBodyB (noOpt_read (hrr ▸ hr)) hb))
  · exact .inl (plain_read_of_not_mem (hrr ▸ hi) hk)

/-- **Away from cast redexes, `Step_read` is the same relation under both readings**, at the
image of a configuration, `otherwise` rules included. -/
theorem sReadB_iff_noCast {c : Config H} (hc : ¬ CastRedex c.code) {b : Value} :
    DDerivesB (simEnv B) (otherwiseB (simEnv B)) "Step_read" "%~>%" [] (.tuple [configV hn c, b]) ↔
      DDerives (simEnv B) (otherwise (simEnv B)) "Step_read" "%~>%" [] (.tuple [configV hn c, b]) := by
  obtain ⟨t, rules, hrel⟩ := findRel_read B
  exact dderivesB_iff_at (closed_expand B) hrel (closedAt_noCast hc)

end Silmaril.Wasm.SpecTec.Sim.Round6.Transfer

module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Zero

/-!
# Round 5, pass 2, track read: the cast rules, backward, from `RefOkB`

`br_on_cast` (2, 3), `br_on_cast_fail` (4, 5), `ref.test` (65, 66) and `ref.cast` (67, 68). The
`-succeed`/`-true` rules carry the premise `Ref_ok s ref $inst_reftype(f.MODULE, rt)`; the others
carry `otherwise` and are read back by firing the first rule, whose premise then holds. Both
directions go through track fwd's bridge `Fwd.RefOkB` (an open leaf of `Round5.Int.Open`), at a
typed store (the configuration is `Typed`) and a bounded instantiated type (`Fwd.tyBnd_instRef`,
from `ReadValidS.frame`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_refTest {a : Admin} (h : Typing.adminHead a = "REF.TEST") :
    ∃ rt, a = .plain (.refTest rt) := by
  revert h
  admin_head_inv

theorem head_refCast {a : Admin} (h : Typing.adminHead a = "REF.CAST") :
    ∃ rt, a = .plain (.refCast rt) := by
  revert h
  admin_head_inv

theorem head_brOnCast {a : Admin} (h : Typing.adminHead a = "BR_ON_CAST") :
    ∃ l rt₁ rt₂, a = .plain (.brOnCast l rt₁ rt₂) := by
  revert h
  admin_head_inv

theorem head_brOnCastFail {a : Admin} (h : Typing.adminHead a = "BR_ON_CAST_FAIL") :
    ∃ l rt₁ rt₂, a = .plain (.brOnCastFail l rt₁ rt₂) := by
  revert h
  admin_head_inv

/-- **The left-hand side of a cast rule, read back**: the state is the configuration's, the code
is a reference followed by one instruction. -/
theorem cast_inv {B : Builtins} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {is : List Admin} {S F R W : Value} {op : MixopS}
    (hR : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R)
    (h : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case op W]])) :
    S = storeV hn s ∧ F = frameV f ∧ ∃ (r : Ref) (a : Admin), is = [.ref r, a] ∧ R = refToValue r ∧
      adminToV a = .case op W := by
  obtain ⟨hZ, hcode⟩ := BwdRead.cfg_inv h
  simp only [stV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true, true_and] at hZ
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨r, rfl⟩ := BwdPureStep.ref_of_typed (valsOnly_bindVals σ) (h₁ ▸ hR)
  exact ⟨hZ.1, hZ.2, r, a₂, rfl, h₁.symm, h₂⟩

/-- The bridge at a typed configuration's store and a bounded frame module's instantiated type. -/
theorem refOkAt_cfg (KB : Fwd.RefOkB (simEnv (BI P hn host))) {s : Store H} {f : Frame}
    {is : List Admin} (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩)
    (hM : Round4.ModuleBnd f.module) (rt : RefType) :
    Fwd.RefOkAt (simEnv (BI P hn host)) hn s (f.module.instRef rt) :=
  Fwd.refOkAt_of (KB := KB) hM (((Typing.typingFacts_simEnv _ hn).config _).1 hc).1 rt

/-- **`Step_read` 65 (`ref.test-true`), backward, from `RefOkB`.** -/
theorem bwdK_refTestTrue (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 65 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.refTestTrue hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.TEST" RT]]) ∧ w = .list [State.aconstV (.case "I32" (.tuple [])) 1] := by
    refine ⟨?_, EvalExp.unique (RefsGC.rhs_of_concl he) (evalExp_list1
      (Memory.evalExp_constPct (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
        RefsGC.evalExp_num'))⟩
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨rfl, rfl, r, a, rfl, rfl, ha⟩ := cast_inv hR hcw.1
  obtain ⟨rt, rfl⟩ := head_refTest (Typing.adminToV_case ha).symm
  have eRT : RT = Encode.toValue rt := by
    injection ha with _ h
    exact h.symm
  subst eRT
  have hok := Fwd.refOk_of_premC G (refOkAt_cfg KB hc hv.frame rt) (valsOnly_bindVals σ)
    (evalExp_var fs) (evalExp_var ff) (evalExp_var fr) (evalExp_var frt) (hp _ List.mem_cons_self)
  exact ⟨[constI32 1], by rw [hcw.2]; rfl, .reference (.testTrue hok)⟩

/-- **`Step_read` 67 (`ref.cast-succeed`), backward, from `RefOkB`.** -/
theorem bwdK_refCastSucceed (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 67 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.refCastSucceed hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.CAST" RT]]) ∧ w = .list [R] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, a, rfl, rfl, ha⟩ := cast_inv hR hcw.1
  obtain ⟨rt, rfl⟩ := head_refCast (Typing.adminToV_case ha).symm
  have eRT : RT = Encode.toValue rt := by
    injection ha with _ h
    exact h.symm
  subst eRT
  have hok := Fwd.refOk_of_premC G (refOkAt_cfg KB hc hv.frame rt) (valsOnly_bindVals σ)
    (evalExp_var fs) (evalExp_var ff) (evalExp_var fr) (evalExp_var frt) (hp _ List.mem_cons_self)
  exact ⟨[.ref r], by rw [hcw.2]; rfl, .reference (.castSucceed hok)⟩

/-- `Ref_ok s ref $inst_reftype(f.MODULE, x)` as the one premise of a rule body, at an
assignment that binds the configuration's store, frame and reference and a reference type `rt`,
when the cast succeeds. -/
theorem premOk_cast (KB : Fwd.RefOkB (simEnv (BI P hn host))) {σ : List (IL.Id × Value)}
    {s : Store H} {f : Frame} {is : List Admin} {r : Ref} {rt : RefType} {x : IL.Id} {els : Prop}
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩) (hM : Round4.ModuleBnd f.module)
    (fs : (VarEnv.empty.bindVals σ).findVal? "s" = some (storeV hn s))
    (ff : (VarEnv.empty.bindVals σ).findVal? "f" = some (frameV f))
    (fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refToValue r))
    (frt : (VarEnv.empty.bindVals σ).findVal? x = some (Encode.toValue rt))
    (hok : RefOk s r (f.module.instRef rt)) :
    ∀ pr ∈ [Prem.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s", .varE "ref",
      .callE "inst_reftype" [.expA (.dotE (.varE "f") "MODULE"), .expA (.varE x)]])],
      PremW (simEnv (BI P hn host)) (DDerives (simEnv (BI P hn host)) noElse) els
        (VarEnv.empty.bindVals σ) pr := by
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .rulePr (evalArgs_nil _ _) (RefsGC.evalExp_refOkArg (Fwd.rStore_builtins hn host)
    (valsOnly_bindVals σ) (evalExp_var fs) (evalExp_var ff) (evalExp_var fr) (evalExp_var frt))
    ((refOkAt_cfg KB hc hM rt _ r).2 hok)

/-- **`Step_read` 66 (`ref.test-false`), backward, from `RefOkB`.** -/
theorem bwdK_refTestFalse (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 66 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.refTestFalse hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have ei32 : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.caseE "I32" (.tupE [])) (.case "I32" (.tuple [])) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)
  have hl := RefsGC.lhs_of_concl he
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.TEST" RT]]) ∧ w = .list [State.aconstV (.case "I32" (.tuple [])) 0] := by
    refine ⟨?_, EvalExp.unique (RefsGC.rhs_of_concl he) (evalExp_list1
      (Memory.evalExp_constPct ei32 RefsGC.evalExp_num'))⟩
    concl_inv hl
  obtain ⟨rfl, rfl, r, a, rfl, rfl, ha⟩ := cast_inv hR hcw.1
  obtain ⟨rt, rfl⟩ := head_refTest (Typing.adminToV_case ha).symm
  have eRT : RT = Encode.toValue rt := by
    injection ha with _ h
    exact h.symm
  subst eRT
  have ho := BwdPureStep.else_of_prems hp
  have hnok : ¬ RefOk s r (f.module.instRef rt) := fun hok =>
    BwdPureStep.otherwise_false ho (by decide) RR.refTestTrue ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (evalExp_list1
        (Memory.evalExp_constPct ei32 (RefsGC.evalExp_num' (m := .natN 1)))),
        premOk_cast KB hc hv.frame fs ff fr frt hok⟩
  exact ⟨[constI32 0], by rw [hcw.2]; rfl, .reference (.testFalse hnok)⟩

/-- **`Step_read` 68 (`ref.cast-fail`), backward, from `RefOkB`.** -/
theorem bwdK_refCastFail (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 68 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.refCastFail hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.CAST" RT]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, a, rfl, rfl, ha⟩ := cast_inv hR hcw.1
  obtain ⟨rt, rfl⟩ := head_refCast (Typing.adminToV_case ha).symm
  have eRT : RT = Encode.toValue rt := by
    injection ha with _ h
    exact h.symm
  subst eRT
  have ho := BwdPureStep.else_of_prems hp
  have hnok : ¬ RefOk s r (f.module.instRef rt) := fun hok =>
    BwdPureStep.otherwise_false ho (by decide) RR.refCastSucceed ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (evalExp_list1
        (RefsGC.evalExp_sub_of (evalExp_var fr))), premOk_cast KB hc hv.frame fs ff fr frt hok⟩
  exact ⟨[.trap], BwdRead.trap_out hcw.2, .reference (.castFail hnok)⟩

/-- The left-hand side of a `br_on_cast`/`br_on_cast_fail` rule, read back. -/
theorem brCast_inv {B : Builtins} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {is : List Admin} {S F R L RT₁ RT₂ : Value} {op : MixopS}
    (hR : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R)
    (hop : op = "BR_ON_CAST" ∨ op = "BR_ON_CAST_FAIL")
    (h : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case op (.tuple [L, RT₁, RT₂])]])) :
    S = storeV hn s ∧ F = frameV f ∧ ∃ (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
      is = [.ref r, .plain (if op = "BR_ON_CAST" then .brOnCast l rt₁ rt₂ else
        .brOnCastFail l rt₁ rt₂)] ∧ R = refToValue r ∧ L = Encode.toValue l ∧
      RT₂ = Encode.toValue rt₂ := by
  obtain ⟨hS, hF, r, a, rfl, rfl, ha⟩ := cast_inv hR h
  refine ⟨hS, hF, ?_⟩
  rcases hop with rfl | rfl
  · obtain ⟨l, rt₁, rt₂, rfl⟩ := head_brOnCast (Typing.adminToV_case ha).symm
    have ha' : Value.case "BR_ON_CAST" (.tuple [Encode.toValue l, Encode.toValue rt₁,
        Encode.toValue rt₂]) = _ := ha
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at ha'
    exact ⟨r, l, rt₁, rt₂, rfl, rfl, ha'.1.symm, ha'.2.2.symm⟩
  · obtain ⟨l, rt₁, rt₂, rfl⟩ := head_brOnCastFail (Typing.adminToV_case ha).symm
    have ha' : Value.case "BR_ON_CAST_FAIL" (.tuple [Encode.toValue l, Encode.toValue rt₁,
        Encode.toValue rt₂]) = _ := ha
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at ha'
    exact ⟨r, l, rt₁, rt₂, rfl, rfl, ha'.1.symm, ha'.2.2.symm⟩

/-- **`Step_read` 2 (`br_on_cast-succeed`), backward, from `RefOkB`.** -/
theorem bwdK_brOnCastSucceed (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 2 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.brOnCastSucceed hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST" (.tuple [L, RT₁, RT₂])]]) ∧ w = .list [R, .case "BR" L] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, l, rt₁, rt₂, rfl, rfl, rfl, rfl⟩ := brCast_inv hR (.inl rfl) hcw.1
  have hok := Fwd.refOk_of_premC G (refOkAt_cfg KB hc hv.frame rt₂) (valsOnly_bindVals σ)
    (evalExp_var fs) (evalExp_var ff) (evalExp_var fr) (evalExp_var frt₂) (hp _ List.mem_cons_self)
  exact ⟨[.ref r, .plain (.br l)], by rw [hcw.2]; rfl, .brOnCastSucceed hok⟩

/-- **`Step_read` 4 (`br_on_cast_fail-succeed`), backward, from `RefOkB`.** -/
theorem bwdK_brOnCastFailSucceed (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 4 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.brOnCastFailSucceed hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST_FAIL" (.tuple [L, RT₁, RT₂])]]) ∧ w = .list [R] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, l, rt₁, rt₂, rfl, rfl, rfl, rfl⟩ := brCast_inv hR (.inr rfl) hcw.1
  have hok := Fwd.refOk_of_premC G (refOkAt_cfg KB hc hv.frame rt₂) (valsOnly_bindVals σ)
    (evalExp_var fs) (evalExp_var ff) (evalExp_var fr) (evalExp_var frt₂) (hp _ List.mem_cons_self)
  exact ⟨[.ref r], by rw [hcw.2]; rfl, .brOnCastFailSucceed hok⟩

/-- **`Step_read` 3 (`br_on_cast-fail`), backward, from `RefOkB`.** -/
theorem bwdK_brOnCastFail (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 3 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.brOnCastFail hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST" (.tuple [L, RT₁, RT₂])]]) ∧ w = .list [R] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, l, rt₁, rt₂, rfl, rfl, rfl, rfl⟩ := brCast_inv hR (.inl rfl) hcw.1
  have ho := BwdPureStep.else_of_prems hp
  have hnok : ¬ RefOk s r (f.module.instRef rt₂) := fun hok =>
    BwdPureStep.otherwise_false ho (by decide) RR.brOnCastSucceed ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (RefsGC.evalExp_listE_of
        (RefsGC.evalExps_cons' (RefsGC.evalExp_sub_of (evalExp_var fr))
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fl)) RefsGC.evalExps_nil'))),
        premOk_cast KB hc hv.frame fs ff fr frt₂ hok⟩
  exact ⟨[.ref r], by rw [hcw.2]; rfl, .brOnCastFail hnok⟩

/-- **`Step_read` 5 (`br_on_cast_fail-fail`), backward, from `RefOkB`.** -/
theorem bwdK_brOnCastFailFail (KB : Fwd.RefOkB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 5 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.brOnCastFailFail hf)
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST_FAIL" (.tuple [L, RT₁, RT₂])]]) ∧
      w = .list [R, .case "BR" L] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, l, rt₁, rt₂, rfl, rfl, rfl, rfl⟩ := brCast_inv hR (.inr rfl) hcw.1
  have ho := BwdPureStep.else_of_prems hp
  have hnok : ¬ RefOk s r (f.module.instRef rt₂) := fun hok =>
    BwdPureStep.otherwise_false ho (by decide) RR.brOnCastFailSucceed ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (evalExp_list1
        (RefsGC.evalExp_sub_of (evalExp_var fr))), premOk_cast KB hc hv.frame fs ff fr frt₂ hok⟩
  exact ⟨[.ref r, .plain (.br l)], by rw [hcw.2]; rfl, .brOnCastFailFail hnok⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Read

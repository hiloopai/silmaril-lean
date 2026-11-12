module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.CastsFwd
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Thms

/-!
# Round 6: the cast rules of `Step_read`, backward, under `DDerivesB`

`br_on_cast` (2, 3), `br_on_cast_fail` (4, 5), `ref.test` (65, 66) and `ref.cast` (67, 68):
round 5's `Raw/…/Round5/Read/Cast.lean` (`Round5.Read.bwdK_*`, from `Fwd.RefOkB`), copied for
the new reading (`FiresB`, `RefOkBB`), each renamed `bwdKB_*`. The `-succeed`/`-true` rules read
`RefOk` off their `Ref_ok` premise; the `otherwise` rules refute `RefOk` by building the earlier
rule's body under `DDerivesB`. Only the plumbing changes (`firesB_body`, `otherwiseB_false`,
`ruleBodyB_of_ruleBody`). The proofs are round 5's, refactored (round 6, track casts) so that the
common steps are lemmas (`refScope`, `brScope`, `refTest_inv`, `refCast_inv`); it was `Silmaril/Raw/…/Round6/Reading/CastsBwd.lean`, and its statements are
unchanged.

Round 6, track casts-v: each rule is proved from a `CastsV.CastRefOk` hypothesis at a
configuration predicate `V` in place of `ReadValidS` (`bwdKG_*`, `read_doneKG`), which asks
`RefOkAtB` only at the casts satisfying `V`. The `RefOkBB` statements are the instances at
`V := ReadValidS` (`castRefOk_rv`), unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Round4Int (BI)
open Round5.Read (ReadValidS readDoneK)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The bridge at a typed configuration's store and a bounded frame module's instantiated type. -/
theorem refOkAtB_cfg (KB : RefOkBB (simEnv (BI P hn host))) {s : Store H} {f : Frame}
    {is : List Admin} (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩)
    (hM : Round4.ModuleBnd f.module) (rt : RefType) :
    RefOkAtB (simEnv (BI P hn host)) hn s (f.module.instRef rt) :=
  refOkAtB_of (KB := KB) hM (((Typing.typingFacts_simEnv _ hn).config _).1 hc).1 rt

/-- `RefOkBB` gives `CastRefOk` at `ReadValidS`, whose frame modules are bounded. -/
theorem castRefOk_rv {env : Env} (KB : RefOkBB env) :
    CastsV.CastRefOk env hn (ReadValidS (H := H)) :=
  castRefOk_bnd KB fun _ h => h.frame

/-- `CastRefOk` at a typed cast pair satisfying `V`. -/
theorem refOkAtB_cfgG {V : Config H → Prop} (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V)
    {s : Store H} {f : Frame} {r : Ref} {i : Instr} {rt : RefType}
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain i]⟩)
    (hv : V ⟨s, f, [.ref r, .plain i]⟩) (hi : CastsV.castTy? i = some rt) :
    RefOkAtB (simEnv (BI P hn host)) hn s (f.module.instRef rt) :=
  refOkAtG K hv hi (((Typing.typingFacts_simEnv _ hn).config _).1 hc).1

/-! ## Reading back a cast rule's scope and left-hand side -/

/-- The scope of a `ref.test`/`ref.cast` rule (quantifiers `s`, `f`, `ref`, `rt`). -/
theorem refScope {env : Env} {D : Interp} {els : Prop} {nm : IL.Id} {op : MixopS} {e : Exp}
    {prems : List Prem} {w : Value}
    (h : RuleBody env D els [] [] "%~>%" (.ruleD nm [.expP "s" (.varT "store" []),
      .expP "f" (.varT "frame" []), .expP "ref" (.varT "ref" []),
      .expP "rt" (.varT "reftype" [])] op e prems) w) :
    ∃ (σ : List (IL.Id × Value)) (S F R RT : Value),
      QuantsOk env (VarEnv.empty.bindVals σ) [.expP "s" (.varT "store" []),
        .expP "f" (.varT "frame" []), .expP "ref" (.varT "ref" []),
        .expP "rt" (.varT "reftype" [])] ∧
      (VarEnv.empty.bindVals σ).findVal? "s" = some S ∧
      (VarEnv.empty.bindVals σ).findVal? "f" = some F ∧
      (VarEnv.empty.bindVals σ).findVal? "ref" = some R ∧
      HasTyp env (VarEnv.empty.bindVals σ) (.varT "ref" []) R ∧
      (VarEnv.empty.bindVals σ).findVal? "rt" = some RT ∧
      EvalExp env (VarEnv.empty.bindVals σ) e w ∧
      ∀ pr ∈ prems, PremW env D els (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope h
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  exact ⟨σ, S, F, R, RT, hq, fs, ff, fr, hR, frt, he, hp⟩

/-- The scope of a `br_on_cast`/`br_on_cast_fail` rule (quantifiers `s`, `f`, `ref`, `l`,
`rt_1`, `rt_2`). -/
theorem brScope {env : Env} {D : Interp} {els : Prop} {nm : IL.Id} {op : MixopS} {e : Exp}
    {prems : List Prem} {w : Value}
    (h : RuleBody env D els [] [] "%~>%" (.ruleD nm [.expP "s" (.varT "store" []),
      .expP "f" (.varT "frame" []), .expP "ref" (.varT "ref" []),
      .expP "l" (.varT "labelidx" []), .expP "rt_1" (.varT "reftype" []),
      .expP "rt_2" (.varT "reftype" [])] op e prems) w) :
    ∃ (σ : List (IL.Id × Value)) (S F R L RT₁ RT₂ : Value),
      QuantsOk env (VarEnv.empty.bindVals σ) [.expP "s" (.varT "store" []),
        .expP "f" (.varT "frame" []), .expP "ref" (.varT "ref" []),
        .expP "l" (.varT "labelidx" []), .expP "rt_1" (.varT "reftype" []),
        .expP "rt_2" (.varT "reftype" [])] ∧
      (VarEnv.empty.bindVals σ).findVal? "s" = some S ∧
      (VarEnv.empty.bindVals σ).findVal? "f" = some F ∧
      (VarEnv.empty.bindVals σ).findVal? "ref" = some R ∧
      HasTyp env (VarEnv.empty.bindVals σ) (.varT "ref" []) R ∧
      (VarEnv.empty.bindVals σ).findVal? "l" = some L ∧
      (VarEnv.empty.bindVals σ).findVal? "rt_1" = some RT₁ ∧
      (VarEnv.empty.bindVals σ).findVal? "rt_2" = some RT₂ ∧
      EvalExp env (VarEnv.empty.bindVals σ) e w ∧
      ∀ pr ∈ prems, PremW env D els (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope h
  obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
  obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
  obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
  obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
  obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
  obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
  exact ⟨σ, S, F, R, L, RT₁, RT₂, hq, fs, ff, fr, hR, fl, frt₁, frt₂, he, hp⟩

/-- The left-hand side of a `ref.test` rule, read back. -/
theorem refTest_inv {B : Builtins} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {is : List Admin} {S F R RT : Value}
    (hR : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R)
    (h : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.TEST" RT]])) :
    S = storeV hn s ∧ F = frameV f ∧ ∃ (r : Ref) (rt : RefType),
      is = [.ref r, .plain (.refTest rt)] ∧ R = refToValue r ∧ RT = Encode.toValue rt := by
  obtain ⟨hS, hF, r, a, rfl, hRr, ha⟩ := Round5.Read.cast_inv hR h
  obtain ⟨rt, rfl⟩ := Round5.Read.head_refTest (Typing.adminToV_case ha).symm
  have eRT : RT = Encode.toValue rt := by
    injection ha with _ h
    exact h.symm
  exact ⟨hS, hF, r, rt, rfl, hRr, eRT⟩

/-- The left-hand side of a `ref.cast` rule, read back. -/
theorem refCast_inv {B : Builtins} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {is : List Admin} {S F R RT : Value}
    (hR : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R)
    (h : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.CAST" RT]])) :
    S = storeV hn s ∧ F = frameV f ∧ ∃ (r : Ref) (rt : RefType),
      is = [.ref r, .plain (.refCast rt)] ∧ R = refToValue r ∧ RT = Encode.toValue rt := by
  obtain ⟨hS, hF, r, a, rfl, hRr, ha⟩ := Round5.Read.cast_inv hR h
  obtain ⟨rt, rfl⟩ := Round5.Read.head_refCast (Typing.adminToV_case ha).symm
  have eRT : RT = Encode.toValue rt := by
    injection ha with _ h
    exact h.symm
  exact ⟨hS, hF, r, rt, rfl, hRr, eRT⟩

/-- `CONST I32 n`, as the right-hand side of `ref.test`. -/
theorem evalExp_constI32 {B : Builtins} {σ : List (IL.Id × Value)} (n : Nat) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.numE (.natN n)])]))
      (State.aconstV (.case "I32" (.tuple [])) n) :=
  Memory.evalExp_constPct (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    RefsGC.evalExp_num'

/-! ## The eight rules -/

/-- **`Step_read` 65 (`ref.test-true`), backward, new reading, from `CastRefOk`.** -/
theorem bwdKG_refTestTrue {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) :
    ∀ (c : Config H) (w : Value), V c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 65 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := State.hasReadRules_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  obtain ⟨σ, S, F, R, RT, -, fs, ff, fr, hR, frt, he, hp⟩ :=
    refScope (firesB_body RR.refTestTrue (by rfl) hf)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.TEST" RT]]) ∧ w = .list [State.aconstV (.case "I32" (.tuple [])) 1] := by
    refine ⟨?_, EvalExp.unique (RefsGC.rhs_of_concl he) (evalExp_list1 (evalExp_constI32 1))⟩
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨rfl, rfl, r, rt, rfl, rfl, rfl⟩ := refTest_inv hR hcw.1
  have hok : RefOk s r (f.module.instRef rt) := refOk_of_premB G (refOkAtB_cfgG K hc hv rfl)
    (valsOnly_bindVals σ) (evalExp_var fs) (evalExp_var ff) (evalExp_var fr) (evalExp_var frt)
    (hp _ List.mem_cons_self)
  exact ⟨[constI32 1], by rw [hcw.2]; rfl, .reference (.testTrue hok)⟩

/-- **`Step_read` 65 (`ref.test-true`), backward, under the new reading, from `RefOkBB`.** -/
theorem bwdKB_refTestTrue (KB : RefOkBB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 65 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  bwdKG_refTestTrue (castRefOk_rv KB)

/-- **`Step_read` 67 (`ref.cast-succeed`), backward, new reading, from `CastRefOk`.** -/
theorem bwdKG_refCastSucceed {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) :
    ∀ (c : Config H) (w : Value), V c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 67 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := State.hasReadRules_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  obtain ⟨σ, S, F, R, RT, -, fs, ff, fr, hR, frt, he, hp⟩ :=
    refScope (firesB_body RR.refCastSucceed (by rfl) hf)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.CAST" RT]]) ∧ w = .list [R] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, rt, rfl, rfl, rfl⟩ := refCast_inv hR hcw.1
  have hok : RefOk s r (f.module.instRef rt) := refOk_of_premB G (refOkAtB_cfgG K hc hv rfl)
    (valsOnly_bindVals σ) (evalExp_var fs) (evalExp_var ff) (evalExp_var fr) (evalExp_var frt)
    (hp _ List.mem_cons_self)
  exact ⟨[.ref r], by rw [hcw.2]; rfl, .reference (.castSucceed hok)⟩

/-- **`Step_read` 67 (`ref.cast-succeed`), backward, under the new reading, from `RefOkBB`.** -/
theorem bwdKB_refCastSucceed (KB : RefOkBB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 67 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  bwdKG_refCastSucceed (castRefOk_rv KB)

/-- `Ref_ok s ref $inst_reftype(f.MODULE, x)` as the one premise of a rule body, at an
assignment that binds the configuration's store, frame and reference and a reference type `rt`,
when the cast succeeds. -/
theorem premOk_castG {σ : List (IL.Id × Value)}
    {s : Store H} {f : Frame} {r : Ref} {rt : RefType} {x : IL.Id} {els : Prop}
    (hK : RefOkAtB (simEnv (BI P hn host)) hn s (f.module.instRef rt))
    (fs : (VarEnv.empty.bindVals σ).findVal? "s" = some (storeV hn s))
    (ff : (VarEnv.empty.bindVals σ).findVal? "f" = some (frameV f))
    (fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refToValue r))
    (frt : (VarEnv.empty.bindVals σ).findVal? x = some (Encode.toValue rt))
    (hok : RefOk s r (f.module.instRef rt)) :
    ∀ pr ∈ [Prem.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s", .varE "ref",
      .callE "inst_reftype" [.expA (.dotE (.varE "f") "MODULE"), .expA (.varE x)]])],
      PremW (simEnv (BI P hn host)) (DDerivesB (simEnv (BI P hn host)) noElse) els
        (VarEnv.empty.bindVals σ) pr := by
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .rulePr (evalArgs_nil _ _) (RefsGC.evalExp_refOkArg (Round5.Fwd.rStore_builtins hn host)
    (valsOnly_bindVals σ) (evalExp_var fs) (evalExp_var ff) (evalExp_var fr) (evalExp_var frt))
    ((hK _ r).2 hok)

/-- `Ref_ok s ref $inst_reftype(f.MODULE, x)` as the one premise of a rule body, at an
assignment that binds the configuration's store, frame and reference and a reference type `rt`,
when the cast succeeds. -/
theorem premOk_castB (KB : RefOkBB (simEnv (BI P hn host))) {σ : List (IL.Id × Value)}
    {s : Store H} {f : Frame} {is : List Admin} {r : Ref} {rt : RefType} {x : IL.Id} {els : Prop}
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩) (hM : Round4.ModuleBnd f.module)
    (fs : (VarEnv.empty.bindVals σ).findVal? "s" = some (storeV hn s))
    (ff : (VarEnv.empty.bindVals σ).findVal? "f" = some (frameV f))
    (fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refToValue r))
    (frt : (VarEnv.empty.bindVals σ).findVal? x = some (Encode.toValue rt))
    (hok : RefOk s r (f.module.instRef rt)) :
    ∀ pr ∈ [Prem.rulePr "Ref_ok" [] "%|-%:%" (.tupE [.varE "s", .varE "ref",
      .callE "inst_reftype" [.expA (.dotE (.varE "f") "MODULE"), .expA (.varE x)]])],
      PremW (simEnv (BI P hn host)) (DDerivesB (simEnv (BI P hn host)) noElse) els
        (VarEnv.empty.bindVals σ) pr :=
  premOk_castG (refOkAtB_cfg KB hc hM rt) fs ff fr frt hok

/-- **`Step_read` 66 (`ref.test-false`), backward, new reading, from `CastRefOk`.** -/
theorem bwdKG_refTestFalse {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) :
    ∀ (c : Config H) (w : Value), V c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 66 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := State.hasReadRules_simEnv _
  obtain ⟨σ, S, F, R, RT, hq, fs, ff, fr, hR, frt, he, hp⟩ :=
    refScope (firesB_body RR.refTestFalse (by rfl) hf)
  have hl := RefsGC.lhs_of_concl he
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.TEST" RT]]) ∧ w = .list [State.aconstV (.case "I32" (.tuple [])) 0] := by
    refine ⟨?_, EvalExp.unique (RefsGC.rhs_of_concl he) (evalExp_list1 (evalExp_constI32 0))⟩
    concl_inv hl
  obtain ⟨rfl, rfl, r, rt, rfl, rfl, rfl⟩ := refTest_inv hR hcw.1
  have hnok : ¬ RefOk s r (f.module.instRef rt) := fun hok =>
    otherwiseB_false (BwdPureStep.else_of_prems hp) (by decide) RR.refTestTrue ⟨_, _, _, rfl, rfl⟩
      (ruleBodyB_of_ruleBody ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (evalExp_list1
        (evalExp_constI32 1)), premOk_castG (refOkAtB_cfgG K hc hv rfl) fs ff fr frt hok⟩)
  exact ⟨[constI32 0], by rw [hcw.2]; rfl, .reference (.testFalse hnok)⟩

/-- **`Step_read` 66 (`ref.test-false`), backward, under the new reading, from `RefOkBB`.** -/
theorem bwdKB_refTestFalse (KB : RefOkBB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 66 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  bwdKG_refTestFalse (castRefOk_rv KB)

/-- **`Step_read` 68 (`ref.cast-fail`), backward, new reading, from `CastRefOk`.** -/
theorem bwdKG_refCastFail {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) :
    ∀ (c : Config H) (w : Value), V c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 68 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := State.hasReadRules_simEnv _
  obtain ⟨σ, S, F, R, RT, hq, fs, ff, fr, hR, frt, he, hp⟩ :=
    refScope (firesB_body RR.refCastFail (by rfl) hf)
  have hl := RefsGC.lhs_of_concl he
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "REF.CAST" RT]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, rt, rfl, rfl, rfl⟩ := refCast_inv hR hcw.1
  have hnok : ¬ RefOk s r (f.module.instRef rt) := fun hok =>
    otherwiseB_false (BwdPureStep.else_of_prems hp) (by decide) RR.refCastSucceed
      ⟨_, _, _, rfl, rfl⟩ (ruleBodyB_of_ruleBody ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl
        (evalExp_list1 (RefsGC.evalExp_sub_of (evalExp_var fr))),
        premOk_castG (refOkAtB_cfgG K hc hv rfl) fs ff fr frt hok⟩)
  exact ⟨[.trap], BwdRead.trap_out hcw.2, .reference (.castFail hnok)⟩

/-- **`Step_read` 68 (`ref.cast-fail`), backward, under the new reading, from `RefOkBB`.** -/
theorem bwdKB_refCastFail (KB : RefOkBB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 68 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  bwdKG_refCastFail (castRefOk_rv KB)

/-- **`Step_read` 2 (`br_on_cast-succeed`), backward, new reading, from `CastRefOk`.** -/
theorem bwdKG_brOnCastSucceed {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) :
    ∀ (c : Config H) (w : Value), V c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 2 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := State.hasReadRules_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  obtain ⟨σ, S, F, R, L, RT₁, RT₂, -, fs, ff, fr, hR, fl, frt₁, frt₂, he, hp⟩ :=
    brScope (firesB_body RR.brOnCastSucceed (by rfl) hf)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST" (.tuple [L, RT₁, RT₂])]]) ∧ w = .list [R, .case "BR" L] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, l, rt₁, rt₂, rfl, rfl, rfl, rfl⟩ := Round5.Read.brCast_inv hR (.inl rfl) hcw.1
  have hok : RefOk s r (f.module.instRef rt₂) := refOk_of_premB G
    (refOkAtB_cfgG K hc hv rfl) (valsOnly_bindVals σ) (evalExp_var fs) (evalExp_var ff)
    (evalExp_var fr) (evalExp_var frt₂) (hp _ List.mem_cons_self)
  exact ⟨[.ref r, .plain (.br l)], by rw [hcw.2]; rfl, .brOnCastSucceed hok⟩

/-- **`Step_read` 2 (`br_on_cast-succeed`), backward, under the new reading, from `RefOkBB`.** -/
theorem bwdKB_brOnCastSucceed (KB : RefOkBB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 2 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  bwdKG_brOnCastSucceed (castRefOk_rv KB)

/-- **`Step_read` 4 (`br_on_cast_fail-succeed`), backward, new reading, from `CastRefOk`.** -/
theorem bwdKG_brOnCastFailSucceed {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) :
    ∀ (c : Config H) (w : Value), V c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 4 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := State.hasReadRules_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  obtain ⟨σ, S, F, R, L, RT₁, RT₂, -, fs, ff, fr, hR, fl, frt₁, frt₂, he, hp⟩ :=
    brScope (firesB_body RR.brOnCastFailSucceed (by rfl) hf)
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST_FAIL" (.tuple [L, RT₁, RT₂])]]) ∧ w = .list [R] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, l, rt₁, rt₂, rfl, rfl, rfl, rfl⟩ := Round5.Read.brCast_inv hR (.inr rfl) hcw.1
  have hok : RefOk s r (f.module.instRef rt₂) := refOk_of_premB G
    (refOkAtB_cfgG K hc hv rfl) (valsOnly_bindVals σ) (evalExp_var fs) (evalExp_var ff)
    (evalExp_var fr) (evalExp_var frt₂) (hp _ List.mem_cons_self)
  exact ⟨[.ref r], by rw [hcw.2]; rfl, .brOnCastFailSucceed hok⟩

/-- **`Step_read` 4 (`br_on_cast_fail-succeed`), backward, under the new reading, from `RefOkBB`.** -/
theorem bwdKB_brOnCastFailSucceed (KB : RefOkBB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 4 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  bwdKG_brOnCastFailSucceed (castRefOk_rv KB)

/-- **`Step_read` 3 (`br_on_cast-fail`), backward, new reading, from `CastRefOk`.** -/
theorem bwdKG_brOnCastFail {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) :
    ∀ (c : Config H) (w : Value), V c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 3 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := State.hasReadRules_simEnv _
  obtain ⟨σ, S, F, R, L, RT₁, RT₂, hq, fs, ff, fr, hR, fl, frt₁, frt₂, he, hp⟩ :=
    brScope (firesB_body RR.brOnCastFail (by rfl) hf)
  have hl := RefsGC.lhs_of_concl he
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST" (.tuple [L, RT₁, RT₂])]]) ∧ w = .list [R] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, l, rt₁, rt₂, rfl, rfl, rfl, rfl⟩ := Round5.Read.brCast_inv hR (.inl rfl) hcw.1
  have hnok : ¬ RefOk s r (f.module.instRef rt₂) := fun hok =>
    otherwiseB_false (BwdPureStep.else_of_prems hp) (by decide) RR.brOnCastSucceed
      ⟨_, _, _, rfl, rfl⟩ (ruleBodyB_of_ruleBody ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl
        (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (RefsGC.evalExp_sub_of (evalExp_var fr))
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fl)) RefsGC.evalExps_nil'))),
        premOk_castG (refOkAtB_cfgG K hc hv rfl) fs ff fr frt₂ hok⟩)
  exact ⟨[.ref r], by rw [hcw.2]; rfl, .brOnCastFail hnok⟩

/-- **`Step_read` 3 (`br_on_cast-fail`), backward, under the new reading, from `RefOkBB`.** -/
theorem bwdKB_brOnCastFail (KB : RefOkBB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 3 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  bwdKG_brOnCastFail (castRefOk_rv KB)

/-- **`Step_read` 5 (`br_on_cast_fail-fail`), backward, new reading, from `CastRefOk`.** -/
theorem bwdKG_brOnCastFailFail {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) :
    ∀ (c : Config H) (w : Value), V c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 5 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hc hf
  have RR : Equiv.ExecRead.HasReadRules (simEnv (BI P hn host)) := State.hasReadRules_simEnv _
  obtain ⟨σ, S, F, R, L, RT₁, RT₂, hq, fs, ff, fr, hR, fl, frt₁, frt₂, he, hp⟩ :=
    brScope (firesB_body RR.brOnCastFailFail (by rfl) hf)
  have hl := RefsGC.lhs_of_concl he
  have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case "BR_ON_CAST_FAIL" (.tuple [L, RT₁, RT₂])]]) ∧
      w = .list [R, .case "BR" L] := by
    concl_inv he
  obtain ⟨rfl, rfl, r, l, rt₁, rt₂, rfl, rfl, rfl, rfl⟩ := Round5.Read.brCast_inv hR (.inr rfl) hcw.1
  have hnok : ¬ RefOk s r (f.module.instRef rt₂) := fun hok =>
    otherwiseB_false (BwdPureStep.else_of_prems hp) (by decide) RR.brOnCastFailSucceed
      ⟨_, _, _, rfl, rfl⟩ (ruleBodyB_of_ruleBody ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl
        (evalExp_list1 (RefsGC.evalExp_sub_of (evalExp_var fr))),
        premOk_castG (refOkAtB_cfgG K hc hv rfl) fs ff fr frt₂ hok⟩)
  exact ⟨[.ref r, .plain (.br l)], by rw [hcw.2]; rfl, .brOnCastFailFail hnok⟩

/-- **`Step_read` 5 (`br_on_cast_fail-fail`), backward, under the new reading, from `RefOkBB`.** -/
theorem bwdKB_brOnCastFailFail (KB : RefOkBB (simEnv (BI P hn host))) :
    ∀ (c : Config H) (w : Value), ReadValidS c → Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" 5 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  bwdKG_brOnCastFailFail (castRefOk_rv KB)

/-- **The cast rules, backward, under the new reading, from `CastRefOk`** (`Round5.Read.read_doneK`
for `FiresB`). -/
theorem read_doneKG {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) (i : Nat) (hi : i ∈ readDoneK)
    (c : Config H) (w : Value) (hv : V c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : FiresB (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  simp only [readDoneK, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwdKG_brOnCastSucceed K c w hv hc hf, bwdKG_brOnCastFail K c w hv hc hf,
    bwdKG_brOnCastFailSucceed K c w hv hc hf, bwdKG_brOnCastFailFail K c w hv hc hf,
    bwdKG_refTestTrue K c w hv hc hf, bwdKG_refTestFalse K c w hv hc hf,
    bwdKG_refCastSucceed K c w hv hc hf, bwdKG_refCastFail K c w hv hc hf]

/-- **The cast rules, backward, under the new reading, from `RefOkBB`** (`Round5.Read.read_doneK`
for `FiresB`). -/
theorem read_doneKB (KB : RefOkBB (simEnv (BI P hn host))) (i : Nat) (hi : i ∈ readDoneK)
    (c : Config H) (w : Value) (hv : ReadValidS c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : FiresB (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  read_doneKG (castRefOk_rv KB) i hi c w hv hc hf

/-- **`CastsBwdB` from `RefOkBB`.** -/
theorem castsBwdB_of (KB : RefOkBB (simEnv (BI P hn host))) : CastsBwdB hn P host :=
  fun i hi c w hv hc hf => read_doneKB KB i hi c w hv hc hf

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading

module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Common

/-!
# Round 5, pass 3, track read: `array.copy-le` (91), `array.copy-gt` (92), backward

Both rules carry `otherwise`, `Expand($type(z, x_2), ARRAY (mut? zt_2))` and
`sx? = $sx(zt_2)` (91 also `i_1 <= i_2`). Read back:

* the arrays exist by reference liveness (`ReadValidR.live`);
* the bounds hold and `n ≠ 0`, else `array.copy-oob1`/`-oob2`/`-zero` (88–90) would fire on the
  same left-hand side at the same assignment, against `otherwise`;
* for 92, `i_2 < i_1`, else `array.copy-le` (91) would fire;
* the `Expand` premise gives the source type and its storage type `zt_2`
  (`expandArray_inv`); `$sx(zt_2)` is Core's `storageSx` (`R4Fwd.applies_sx_any`), so `sx?`
  is the image of `storageSx zt_2`;
* the successor indices do not wrap (`Aggregates.Bounded`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)
open Round4Read (decode_refArray decode_aconst_at)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The image of `CONST I32 %(e)` evaluated from a natural. -/
theorem evalExp_const32 {env : Env} {ρ : VarEnv} {e : Exp} {n : Nat}
    (h : EvalExp env ρ e (.num (.natN n))) :
    EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [e])]))
      (aconstV (.case "I32" (.tuple [])) n) :=
  Memory.evalExp_constPct (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) h

/-- `CONST I32 i`, a variable. -/
theorem evalExp_const32v {env : Env} {ρ : VarEnv} {x : IL.Id} {n : Nat}
    (h : ρ.findVal? x = some (idxV n)) :
    EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE x]))
      (aconstV (.case "I32" (.tuple [])) n) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_var h))

/-- `i_1 <= i_2`, evaluated. -/
theorem le_of_evalExp {env : Env} {ρ : VarEnv} {x y : IL.Id} {a b : Nat}
    (fx : ρ.findVal? x = some (idxV a)) (fy : ρ.findVal? y = some (idxV b))
    (h : EvalExp env ρ (.cmpE .leOp (.numT .natT) (.projE (.uncaseE (.varE x) "%") 0)
      (.projE (.uncaseE (.varE y) "%") 0)) (.bool true)) : a ≤ b := by
  have h' := EvalExp.unique h (RefsGC.evalExp_cmpNat (op := .leOp) (t := .numT .natT)
    (c := decide (a ≤ b)) (RefsGC.evalExp_unpct (evalExp_var fx))
    (RefsGC.evalExp_unpct (evalExp_var fy)) (by simp [Num.cmp]))
  simpa using h'.symm

/-- **The shared reading of the copy rules' left-hand side, `otherwise` and `Expand`.** For an
assignment `σ` of the copy rules' quantifiers satisfying `otherwise` (below rule `i ≥ 91`) and the
`Expand` premise, on the left-hand side of an `array.copy` instruction with live operands. -/
theorem copy_facts {s : Store H} {f : Frame} {σ : List (IL.Id × Value)} {k₁ k₂ : Nat}
    {i₁ i₂ n : BitVec 32} {x₁ x₂ : TypeIdx} {i : Nat} {w : Value} (hi : 91 ≤ i)
    (hq : QuantsOk (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ) [
      .expP "z" (.varT "state" []), .expP "a_1" (.varT "addr" []),
      .expP "i_1" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "a_2" (.varT "addr" []),
      .expP "i_2" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "n" (.varT "n" []),
      .expP "x_1" (.varT "idx" []), .expP "x_2" (.varT "idx" [])])
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fa₁ : (VarEnv.empty.bindVals σ).findVal? "a_1" = some (.num (.natN k₁)))
    (fi₁ : (VarEnv.empty.bindVals σ).findVal? "i_1" = some (idxV i₁.toNat))
    (fa₂ : (VarEnv.empty.bindVals σ).findVal? "a_2" = some (.num (.natN k₂)))
    (fi₂ : (VarEnv.empty.bindVals σ).findVal? "i_2" = some (idxV i₂.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (hl : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z",
      .listE [.caseE "REF.ARRAY_ADDR" (.varE "a_1"),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i_1"]),
        .caseE "REF.ARRAY_ADDR" (.varE "a_2"),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i_2"]),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
        .caseE "ARRAY.COPY" (.tupE [.varE "x_1", .varE "x_2"])]]))
      (configV hn ⟨s, f, [arrRef k₁, constI32 i₁, arrRef k₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩))
    (ho : otherwise (simEnv (BI P hn host)) "Step_read" [] i
      (.tuple [configV hn ⟨s, f, [arrRef k₁, constI32 i₁, arrRef k₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩, w]))
    (live₁ : (s.arrays[k₁]?).isSome) (live₂ : (s.arrays[k₂]?).isSome) :
    ∃ ai₁ ai₂, s.arrays[k₁]? = some ai₁ ∧ s.arrays[k₂]? = some ai₂ ∧
      (i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length) ∧
      n ≠ 0 := by
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨ai₁, ha₁⟩ := Option.isSome_iff_exists.1 live₁
  obtain ⟨ai₂, ha₂⟩ := Option.isSome_iff_exists.1 live₂
  have hl' := evalExp_tup2 hl Round5.Read.evalExp_trapList
  have hle₁ : i₁.toNat + n.toNat ≤ ai₁.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by omega)
      RR.arrayCopyOob1 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, hl', fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi₁)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_arrayFields G (valsOnly_bindVals σ) (evalExp_var fz)
        (evalExp_var fa₁) ha₁)) (by simpa using hlt))
  have hle₂ : i₂.toNat + n.toNat ≤ ai₂.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by omega)
      RR.arrayCopyOob2 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, hl', fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi₂)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_arrayFields G (valsOnly_bindVals σ) (evalExp_var fz)
        (evalExp_var fa₂) ha₂)) (by simpa using hlt))
  refine ⟨ai₁, ai₂, ha₁, ha₂, ⟨hle₁, hle₂⟩, ?_⟩
  rintro rfl
  refine BwdPureStep.otherwise_false ho (by omega) RR.arrayCopyZero ⟨_, _, _, rfl, rfl⟩
    ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl
      (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩), fun pr hpr => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · refine .elsePr ?_
    exact RefsGC.otherwise_of_ruleAt RR.arrayCopyZero (RefsGC.readTable_simEnv _) (i := 90)
      (by decide) (exc := [88, 89]) FwdSimdAgg.lhsIn_arrayCopy (by decide) (by
        intro j hj _ r' hr' w hw
        obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
        rcases (by simpa using hj : j = 88 ∨ j = 89) with rfl | rfl
        · rw [RefsGC.relRules_of_ruleAt RR.arrayCopyOob1 hr']
          exact RefsGC.not_arrayCopyOob₁ G ha₁ hle₁
        · rw [RefsGC.relRules_of_ruleAt RR.arrayCopyOob2 hr']
          exact RefsGC.not_arrayCopyOob₂ G ha₂ hle₂)
  · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simp; exact RefsGC.evalExp_num'))

/-- **The left-hand side of a copy rule, decoded**, with the bindings of its variables. -/
theorem copy_lhs {s : Store H} {f : Frame} {is : List Admin} {σ : List (IL.Id × Value)}
    {Z A₁ I₁ A₂ I₂ N X₁ X₂ : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some Z)
    (fa₁ : (VarEnv.empty.bindVals σ).findVal? "a_1" = some A₁)
    (fi₁ : (VarEnv.empty.bindVals σ).findVal? "i_1" = some I₁)
    (fa₂ : (VarEnv.empty.bindVals σ).findVal? "a_2" = some A₂)
    (fi₂ : (VarEnv.empty.bindVals σ).findVal? "i_2" = some I₂)
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some N)
    (fx₁ : (VarEnv.empty.bindVals σ).findVal? "x_1" = some X₁)
    (fx₂ : (VarEnv.empty.bindVals σ).findVal? "x_2" = some X₂)
    (hl : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z",
      .listE [.caseE "REF.ARRAY_ADDR" (.varE "a_1"),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i_1"]),
        .caseE "REF.ARRAY_ADDR" (.varE "a_2"),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i_2"]),
        .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
        .caseE "ARRAY.COPY" (.tupE [.varE "x_1", .varE "x_2"])]]))
      (configV hn ⟨s, f, is⟩)) :
    ∃ (k₁ k₂ : Nat) (i₁ i₂ n : BitVec 32) (x₁ x₂ : TypeIdx), is = [arrRef k₁, constI32 i₁, arrRef k₂, constI32 i₂,
      constI32 n, .plain (.arrayCopy x₁ x₂)] ∧ Z = stateV hn s f ∧ A₁ = .num (.natN k₁) ∧
      I₁ = idxV i₁.toNat ∧ A₂ = .num (.natN k₂) ∧ I₂ = idxV i₂.toNat ∧
      N = .num (.natN n.toNat) ∧ X₁ = Encode.toValue x₁ ∧ X₂ = Encode.toValue x₂ := by
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A₁, .case "CONST" (.tuple [.case "I32" (.tuple []), I₁]),
      .case "REF.ARRAY_ADDR" A₂, .case "CONST" (.tuple [.case "I32" (.tuple []), I₂]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.COPY" (.tuple [X₁, X₂])]]) := by
    concl_inv hl
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩ := Bwd.adminsToV_eq_six hcode
  obtain ⟨k₁, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i₁, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨k₂, rfl, rfl⟩ := decode_refArray h₃
  obtain ⟨i₂, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₄
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₅
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x₁, x₂, rfl⟩ := Bwd.head_arrayCopy (Typing.adminToV_case h₆).symm
  have h₆' : Value.case "ARRAY.COPY" (.tuple [Encode.toValue x₁, Encode.toValue x₂]) = _ := h₆
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₆'
  exact ⟨k₁, k₂, i₁, i₂, n, x₁, x₂, rfl, hZ, rfl, rfl, rfl, rfl, rfl,
    h₆'.1.symm, h₆'.2.symm⟩

/-- `sx? = $sx(zt_2)`, read back: `sx?` evaluates to the image of Core's `storageSx`. -/
theorem sx_inv {σ : List (IL.Id × Value)} {zt : CStorageType}
    (fzt : (VarEnv.empty.bindVals σ).findVal? "zt_2" = some (tyV zt))
    (h : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")]))
        (.callE "sx" [.expA (.varE "zt_2")])) (.bool true)) :
    EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")]))
      (.opt ((storageSx zt).map Equiv.sxV)) := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hc
  have e := EvalExp.unique h₂ (Vec.evalExp_call (Aggregates.findDef_none (valsOnly_bindVals σ) _)
    (Vec.evalArgs_var fzt Equiv.evalArgs_nil)
    (R4Fwd.applies_sx_any (FwdSimdAgg.vvB_builtins (prof := P) hn host) zt))
  exact e ▸ h₁

/-- **`Step_read` 91 (`array.copy-le`), backward, under `ReadValidS`.** -/
theorem bwd_arrayCopyLe : ∀ (c : Config H) (w : Value), Round5.Read.ReadValidS c →
    Fires (simEnv (BI P hn host)) "Step_read" 91 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayCopyLe hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A₁, fa₁, -⟩ := hq "a_1" (.varT "addr" []) (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" State.num32T (by simp)
  obtain ⟨A₂, fa₂, -⟩ := hq "a_2" (.varT "addr" []) (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X₁, fx₁, -⟩ := hq "x_1" State.idxT (by simp)
  obtain ⟨X₂, fx₂, -⟩ := hq "x_2" State.idxT (by simp)
  have hl := RefsGC.lhs_of_concl he
  obtain ⟨k₁, k₂, i₁, i₂, n, x₁, x₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    copy_lhs fz fa₁ fi₁ fa₂ fi₂ fn fx₁ fx₂ hl
  obtain ⟨ai₁, ai₂, ha₁, ha₂, hb, hn0⟩ := copy_facts (le_refl _) (quantsOk_sub hq (by simp)) fz fa₁ fi₁ fa₂
    fi₂ fn hl (Round4Read.else_head hp) hv.r.live.1 hv.r.live.2.2.1
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨d, m, zt, hd, hexp, fzt, -⟩ := expandArray_inv fz fx₂ hwe hD
  obtain ⟨hle, hsx⟩ := and_true_inv (ifPrem (hp _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hle' := le_of_evalExp fi₁ fi₂ hle
  have hsx' := sx_inv fzt hsx
  have hl₁ : ai₁.fields.length < 2 ^ 32 := Aggregates.Bounded.array hv.r.read.store.aggs ha₁
  have hl₂ : ai₂.fields.length < 2 ^ 32 := Aggregates.Bounded.array hv.r.read.store.aggs ha₂
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₁))
    (RefsGC.evalExps_cons' (evalExp_const32v fi₁)
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₂))
    (RefsGC.evalExps_cons' (evalExp_const32v fi₂)
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 hsx' (evalExp_var fx₂)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx₁))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₁))
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi₁)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₂))
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi₂)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_predNat (evalExp_var fn) hn1))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx₁) (evalExp_var fx₂)))
      RefsGC.evalExps_nil')))))))))))))
  refine ⟨_, ?_, .aggregate (.arrayCopyLe ha₁ ha₂ hb hn0 hd hexp hle')⟩
  rw [hw]
  simp only [adminsToV, Round5.Read.adminToV_constI32, FwdSimdAgg.toNat_succ hb.1 hl₁ hn0,
    FwdSimdAgg.toNat_succ hb.2 hl₂ hn0, RefsGC.toNat_sub_one hn0]
  rfl

/-- **`Step_read` 92 (`array.copy-gt`), backward, under `ReadValidS`.** -/
theorem bwd_arrayCopyGt : ∀ (c : Config H) (w : Value), Round5.Read.ReadValidS c →
    Fires (simEnv (BI P hn host)) "Step_read" 92 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayCopyGt hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A₁, fa₁, -⟩ := hq "a_1" (.varT "addr" []) (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" State.num32T (by simp)
  obtain ⟨A₂, fa₂, -⟩ := hq "a_2" (.varT "addr" []) (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X₁, fx₁, -⟩ := hq "x_1" State.idxT (by simp)
  obtain ⟨X₂, fx₂, -⟩ := hq "x_2" State.idxT (by simp)
  have hl := RefsGC.lhs_of_concl he
  obtain ⟨k₁, k₂, i₁, i₂, n, x₁, x₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    copy_lhs fz fa₁ fi₁ fa₂ fi₂ fn fx₁ fx₂ hl
  have ho := Round4Read.else_head hp
  obtain ⟨ai₁, ai₂, ha₁, ha₂, hb, hn0⟩ := copy_facts (by decide) (quantsOk_sub hq (by simp)) fz
    fa₁ fi₁ fa₂ fi₂ fn hl ho hv.r.live.1 hv.r.live.2.2.1
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨d, m, zt, hd, hexp, fzt, rfl⟩ := expandArray_inv fz fx₂ hwe hD
  have hsx := ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hsx' := sx_inv fzt hsx
  have hl₁ : ai₁.fields.length < 2 ^ 32 := Aggregates.Bounded.array hv.r.read.store.aggs ha₁
  have hl₂ : ai₂.fields.length < 2 ^ 32 := Aggregates.Bounded.array hv.r.read.store.aggs ha₂
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have : Fact (Round4.ModuleBnd f.module) := ⟨hv.frame⟩
  -- `array.copy-le` would fire for `i_1 <= i_2`
  have hgt : i₂.toNat < i₁.toNat := by
    refine Nat.lt_of_not_le fun hle => BwdPureStep.otherwise_false ho (by decide) RR.arrayCopyLe
      ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl
        (RefsGC.evalExp_listE_of
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₁))
        (RefsGC.evalExps_cons' (evalExp_const32v fi₁)
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₂))
        (RefsGC.evalExps_cons' (evalExp_const32v fi₂)
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 hsx' (evalExp_var fx₂)))
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx₁))
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₁))
        (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_addNat
          (RefsGC.evalExp_unpct (evalExp_var fi₁)) (RefsGC.evalExp_num' (m := .natN 1))))
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₂))
        (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_addNat
          (RefsGC.evalExp_unpct (evalExp_var fi₂)) (RefsGC.evalExp_num' (m := .natN 1))))
        (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_predNat (evalExp_var fn) hn1))
        (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx₁) (evalExp_var fx₂)))
          RefsGC.evalExps_nil'))))))))))))), fun pr hpr => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl | rfl
    · refine .elsePr ?_
      exact RefsGC.otherwise_of_ruleAt RR.arrayCopyLe (RefsGC.readTable_simEnv _) (i := 91)
        (by decide) (exc := [88, 89, 90]) FwdSimdAgg.lhsIn_arrayCopy (by decide) (by
          intro j hj _ r' hr' w hw
          obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
          rcases (by simpa using hj : j = 88 ∨ j = 89 ∨ j = 90) with rfl | rfl | rfl
          · rw [RefsGC.relRules_of_ruleAt RR.arrayCopyOob1 hr']
            exact RefsGC.not_arrayCopyOob₁ G ha₁ hb.1
          · rw [RefsGC.relRules_of_ruleAt RR.arrayCopyOob2 hr']
            exact RefsGC.not_arrayCopyOob₂ G ha₂ hb.2
          · rw [RefsGC.relRules_of_ruleAt RR.arrayCopyZero hr']
            exact FwdSimdAgg.not_arrayCopyZero hn0)
    · exact .rulePr Equiv.evalArgs_nil hwe
        (Fwd.dderives_expandB (Int.typesB _) noElse (Fwd.tyBnd_type' hd) hexp)
    · exact .ifPr (RefsGC.evalExp_and_true (RefsGC.evalExp_leNat
        (RefsGC.evalExp_unpct (evalExp_var fi₁)) (RefsGC.evalExp_unpct (evalExp_var fi₂)) hle) hsx)
  have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₁))
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_predNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi₁)) (evalExp_var fn)) (by omega)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₂))
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_predNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi₂)) (evalExp_var fn)) (by omega)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 hsx' (evalExp_var fx₂)))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx₁))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₁))
    (RefsGC.evalExps_cons' (evalExp_const32v fi₁)
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa₂))
    (RefsGC.evalExps_cons' (evalExp_const32v fi₂)
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_predNat (evalExp_var fn) hn1))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx₁) (evalExp_var fx₂)))
      RefsGC.evalExps_nil')))))))))))))
  refine ⟨_, ?_, .aggregate (.arrayCopyGt ha₁ ha₂ hb hn0 hd hexp hgt)⟩
  rw [hw]
  simp only [adminsToV, Round5.Read.adminToV_constI32, FwdSimdAgg.toNat_last hb.1 hl₁ hn0,
    FwdSimdAgg.toNat_last hb.2 hl₂ hn0, RefsGC.toNat_sub_one hn0]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2

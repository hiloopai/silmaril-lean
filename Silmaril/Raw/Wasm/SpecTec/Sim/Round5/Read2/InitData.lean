module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Field
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Copy

/-!
# Round 5, pass 3, track read: `array.init_data-num` (102), backward, under `ReadValidS`

The rule carries `otherwise`, `Expand($type(z, x), ARRAY (mut? zt))` and
`$zbytes_(zt, c) = $data(z, y).BYTES[j : $zsize(zt)/8]`. Read back:

* the array exists (`ReadValidR.live`) and `ReadValidS.seg` resolves the data segment and gives
  the array type with `0 < |zt|`; the `Expand` premise fixes `zt` (`R4Fwd.zt_of_expand`);
* `otherwise`: the bounds hold and `n ≠ 0`, else `-oob1` (99), `-oob2` (100, pass 2's
  `Round5.Read.body_arrayInitDataOob₂`) or `-zero` (101) would fire;
* the premise: `c` is the literal of a word `k < 2 ^ |zt|` whose encoding is the slice
  (`zbytes_lit_inv`), so Core's `readField?` reads `fieldOfLit zt k` there (`readField_of_slice`),
  and `$const($cunpack(zt), $cunpacknum_(zt, c))` is its image (`R4Fwd.evalExp_constField`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)
open Round4Read (decode_refArray decode_aconst_at)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The left-hand side of an `array.init_data` step. -/
theorem lhsIn_arrayInitData {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx}
    {i j n : BitVec 32} {a : Nat} :
    RefsGC.LhsIn ["ARRAY.INIT_DATA", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩) :=
  .inr ⟨_, _, rfl, RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil))))⟩

/-- **`Step_read` 102 (`array.init_data-num`), backward, under `ReadValidS`.** -/
theorem bwd_arrayInitDataNum : ∀ (c : Config H) (w : Value), Round5.Read.ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 102 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv hct hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  have XI := R4Fwd.expandInv_builtins (prof := P) hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayInitDataNum hf)
  have hρ := valsOnly_bindVals σ
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  obtain ⟨C, fc, hC⟩ := hq "c" (.varT "lit_" [.expA (.varE "zt")]) (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A, .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.INIT_DATA" (.tuple [X, Y])]]) := by
    concl_inv hl
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₃
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := BwdRead.head_arrayInitData (Typing.adminToV_case h₅).symm
  have eXY : X = Encode.toValue x ∧ Y = Encode.toValue y := by
    have h₅' : Value.case "ARRAY.INIT_DATA" (.tuple [Encode.toValue x, Encode.toValue y]) = _ := h₅
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₅'
    exact ⟨h₅'.1.symm, h₅'.2.symm⟩
  obtain ⟨rfl, rfl⟩ := eXY
  subst hZ
  obtain ⟨hdat', d, m, zt, hd, hexp, h0⟩ := hv.seg.2.2.2.2.1
  obtain ⟨⟨da, di⟩, hdat⟩ := Option.isSome_iff_exists.1 hdat'
  obtain ⟨ai, ha⟩ := Option.isSome_iff_exists.1 hv.r.live.1
  have ho := Round4Read.else_head hp
  -- `zt`, from the `Expand` premise
  obtain ⟨w', hw', hD⟩ := RefsGC.premW_rule (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have fzt := evalExp_varE_iff.1
    (R4Fwd.zt_of_expand XI hρ hd hexp (evalExp_var fz) (evalExp_var fx) hw' hD)
  -- the bounds and `n ≠ 0`, from `otherwise`
  have hle₁ : i.toNat + n.toNat ≤ ai.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayInitDataOob1 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, quantsOk_sub hq (by simp),
        evalExp_tup2 hl Round5.Read.evalExp_trapList, fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_arrayFields G hρ (evalExp_var fz)
        (evalExp_var fa) ha)) (by simpa using hlt))
  have hle₂ : j.toNat + n.toNat * storageSize zt / 8 ≤ di.bytes.size := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayInitDataOob2 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩ ?_
    exact Round5.Read.body_arrayInitDataOob₂ (j := j) (n := n) hv.frame hd hexp hdat h0 hlt
      (((Typing.typingFacts_simEnv _ hn).config _).1 hct).1
  have hn0 : n ≠ 0 := by
    rintro rfl
    refine BwdPureStep.otherwise_false ho (by decide) RR.arrayInitDataZero ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, quantsOk_sub hq (by simp), evalExp_tup2 hl
        (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩), fun pr hpr => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · refine .elsePr ?_
      exact RefsGC.otherwise_of_ruleAt RR.arrayInitDataZero (RefsGC.readTable_simEnv _) (i := 101)
        (by decide) (exc := [99, 100]) lhsIn_arrayInitData (by decide) (by
          intro j' hj' _ r' hr' w hw
          obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
          rcases (by simpa using hj' : j' = 99 ∨ j' = 100) with rfl | rfl
          · rw [RefsGC.relRules_of_ruleAt RR.arrayInitDataOob1 hr']
            exact R4Fwd.not_arrayInitDataOob₁ G ha hle₁
          · rw [RefsGC.relRules_of_ruleAt RR.arrayInitDataOob2 hr']
            exact R4Fwd.not_arrayInitDataOob₂ XI hd hexp hdat h0 hle₂)
    · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simp; exact RefsGC.evalExp_num'))
  -- the premise `$zbytes_(zt, c) = $data(z, y).BYTES[j : $zsize(zt)/8]`
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self))))
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcmp
  have hA : Applies (simEnv (BI P hn host)) "zbytes_" [.val (tyV zt), .val C] v₁ :=
    (applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons
      (evalExp_var fzt) (Equiv.evalArgs_cons (evalExp_var fc) Equiv.evalArgs_nil))).2
      (evalExp_callE_iff.1 e₁)
  obtain ⟨K, hK, rfl, rfl⟩ := zbytes_lit_inv h0 fzt hC hA
  have hsz : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "zsize" [.expA (.varE "zt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN (storageSize zt / 8))) :=
    R4Fwd.evalExp_divBy8 (R4Fwd.dvd_storageSize zt h0) (Vec.evalExp_call
      (Aggregates.findDef_none hρ _) (Equiv.evalArgs_cons (evalExp_var fzt) Equiv.evalArgs_nil)
      (R4Fwd.applies_zsize zt h0))
  have hdata : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "data" [.expA (.varE "z"), .expA (.varE "y")]) (dataInstToValue di) := by
    obtain ⟨M, Ls, As, a', hS, hM, hA', ha', hr⟩ := Memory.dataAt_of_data? hn hdat
    exact State.evalExp_data (State.stateDefs_simEnv _) (Aggregates.findDef_none hρ _)
      (evalExp_var fz) (evalExp_var fy) hS hM hA' ha' hr
  obtain ⟨W, j', k', hW, hj', hk', hsl⟩ := evalExp_sliceE_iff.1 e₂
  obtain rfl := EvalExp.unique hW (RefsGC.evalExp_dot hdata (Memory.dataInstV_BYTES di))
  have ej : j' = j.toNat := by
    simpa using EvalExp.unique hj' (RefsGC.evalExp_unpct (evalExp_var fj))
  have ek : k' = storageSize zt / 8 := by simpa using EvalExp.unique hk' hsz
  subst ej ek
  have hread := readField_of_slice h0 hK hsl rfl
  -- the right-hand side
  have hb₁ : ai.fields.length < 2 ^ 32 := Aggregates.Bounded.array hv.r.read.store.aggs ha
  have hb₂ : di.bytes.size < 2 ^ 32 := hv.r.read.store.aggs.datas di
    (List.mem_of_getElem? (State.Store.data?_eq_some hdat).2)
  have hn₁ : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hb₂' : j.toNat + storageSize zt / 8 < 2 ^ 32 := by
    have : storageSize zt / 8 ≤ n.toNat * storageSize zt / 8 :=
      Nat.div_le_div_right (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hcst := R4Fwd.evalExp_constField (B := BI P hn host) (Prims.floatB_builtins (prof := P) hn host)
    hρ h0 hK fzt fc
  have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa))
    (RefsGC.evalExps_cons' (evalExp_const32v fi)
    (RefsGC.evalExps_cons' hcst
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa))
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fj)) hsz))
    (RefsGC.evalExps_cons' (evalExp_const32 (RefsGC.evalExp_predNat (evalExp_var fn) hn₁))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
      RefsGC.evalExps_nil'))))))))))
  refine ⟨_, ?_, .aggregate (.arrayInitDataNum (ft := .field m zt) ha hd hexp hdat
    ⟨hle₁, hle₂⟩ hn0 hread)⟩
  rw [hw]
  simp only [adminsToV, Round5.Read.adminToV_constI32, State.adminToV_toAdmin,
    FwdSimdAgg.toNat_succ hle₁ hb₁ hn0,
    R4Fwd.toNat_add_ofNat (k := storageSize (fieldStorage (Ty.field m zt)) / 8) hb₂',
    RefsGC.toNat_sub_one hn0]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2

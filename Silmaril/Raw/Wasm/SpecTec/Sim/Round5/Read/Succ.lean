module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Zero

/-!
# Round 5, pass 2, track read: `array.init_elem-succ` (97), backward, under `ReadValidS`

The rule's premises are `otherwise` and `ref = $elem(z, y).REFS[j]`. Read backwards: the array
exists (liveness) and the segment resolves (`ReadValidS.seg`); both ranges are in bounds, or
`array.init_elem-oob1`/`-oob2` (94/95) would fire on the same left-hand side; `n ≠ 0`, or
`array.init_elem-zero` (96) would fire, its own `otherwise` holding because 94 and 95 do not
(`RefsGC.not_arrayInitElemOob₁/₂`). The premise names the segment's `j`-th reference. The
successor's `i + 1`, `j + 1` do not wrap: the array and the segment have fewer than `2 ^ 32`
entries (the store bounds).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)
open Round4Read (decode_refArray decode_aconst_at)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The left-hand side of an `array.init_elem` step has its constructors among
`ARRAY.INIT_ELEM`, `REF.ARRAY_ADDR` and `CONST`. -/
theorem lhsIn_arrayInitElem {s : Store H} {f : Frame} {a : Nat} {i j n : BitVec 32}
    {x : TypeIdx} {y : ElemIdx} :
    RefsGC.LhsIn ["ARRAY.INIT_ELEM", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩) :=
  .inr ⟨_, _, rfl, RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide))
    (RefsGC.tagsIn_cons (RefsGC.tag_case (by decide)) RefsGC.tagsIn_nil))))⟩

/-- `QuantsOk` of a prefix of the quantifiers. -/
theorem quants_init {env : Env} {ρ : VarEnv} {qs : List Param} {p : Param}
    (h : QuantsOk env ρ (qs ++ [p])) : QuantsOk env ρ qs :=
  fun x t hm => h x t (List.mem_append_left _ hm)

/-- **`Step_read` 97 (`array.init_elem-succ`), backward, under `ReadValidS`.** -/
theorem bwdS_arrayInitElemSucc : ∀ (c : Config H) (w : Value), ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 97 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayInitElemSucc hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  obtain ⟨RF, fr, -⟩ := hq "ref" (.varT "ref" []) (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A, .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.INIT_ELEM" (.tuple [X, Y])]]) := by
    concl_inv hl
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₃
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := BwdRead.head_arrayInitElem (Typing.adminToV_case h₅).symm
  subst hZ
  have eXY : X = Encode.toValue x ∧ Y = Encode.toValue y := by
    injection h₅ with _ h
    injection h with h
    injection h with h₁ h
    injection h with h₂
    exact ⟨h₁.symm, h₂.symm⟩
  obtain ⟨rfl, rfl⟩ := eXY
  obtain ⟨ai, ha⟩ := Option.isSome_iff_exists.1 hv.r.live.1
  obtain ⟨⟨ea, ei⟩, hel⟩ := Option.isSome_iff_exists.1 hv.seg.2.2.2.2.1
  have ho := Round4Read.else_head hp
  have hle₁ : i.toNat + n.toNat ≤ ai.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayInitElemOob1 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, quants_init hq,
        evalExp_tup2 hl evalExp_trapList, fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_arrayFields G (valsOnly_bindVals σ) (evalExp_var fz)
        (evalExp_var fa) ha)) (by simpa using hlt))
  have hle₂ : j.toNat + n.toNat ≤ ei.refs.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayInitElemOob2 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, quants_init hq,
        evalExp_tup2 hl evalExp_trapList, fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fj)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_elemRefs G (valsOnly_bindVals σ) hel (evalExp_var fz)
        (evalExp_var fy))) (by simpa using hlt))
  have hn0 : n ≠ 0 := by
    rintro rfl
    refine BwdPureStep.otherwise_false ho (by decide) RR.arrayInitElemZero ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, quants_init hq,
        evalExp_tup2 hl (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩), fun pr hpr => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · refine .elsePr ?_
      exact RefsGC.otherwise_of_ruleAt RR.arrayInitElemZero (RefsGC.readTable_simEnv _) (i := 96)
        (by decide) (exc := [94, 95]) lhsIn_arrayInitElem (by decide) (by
          intro m hm _ r' hr' w hw
          obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
          rcases (by simpa using hm : m = 94 ∨ m = 95) with rfl | rfl
          · rw [RefsGC.relRules_of_ruleAt RR.arrayInitElemOob1 hr']
            exact RefsGC.not_arrayInitElemOob₁ G ha hle₁
          · rw [RefsGC.relRules_of_ruleAt RR.arrayInitElemOob2 hr']
            exact RefsGC.not_arrayInitElemOob₂ G hel hle₂)
    · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simp; exact RefsGC.evalExp_num'))
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  obtain ⟨r, hr⟩ : ∃ r, ei.refs[j.toNat]? = some r :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have eRF : RF = refToValue r :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (evalExp_var fr) (RefsGC.evalExp_idx (RefsGC.evalExp_elemRefs G (valsOnly_bindVals σ) hel
        (evalExp_var fz) (evalExp_var fy)) (RefsGC.evalExp_unpct (evalExp_var fj))
        (by simp [hr]))
  subst eRF
  have hlen : ai.fields.length < 2 ^ 32 := Aggregates.Bounded.array hv.r.read.store.aggs ha
  have hlen' : ei.refs.length < 2 ^ 32 := Round4Read.elem_lt32 hv.r.read.store hel
  have ei32 : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.caseE "I32" (.tupE [])) (.case "I32" (.tuple [])) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)
  have hw : w = .list [.case "REF.ARRAY_ADDR" (.num (.natN k)), aconstV (.case "I32" (.tuple []))
      i.toNat, refToValue r, .case "ARRAY.SET" (Encode.toValue x),
      .case "REF.ARRAY_ADDR" (.num (.natN k)), aconstV (.case "I32" (.tuple [])) (i.toNat + 1),
      aconstV (.case "I32" (.tuple [])) (j.toNat + 1),
      aconstV (.case "I32" (.tuple [])) (n.toNat - 1),
      .case "ARRAY.INIT_ELEM" (.tuple [Encode.toValue x, Encode.toValue y])] := by
    refine EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ei32 (evalExp_var fi)))
      (RefsGC.evalExps_cons' (RefsGC.evalExp_sub_of (evalExp_var fr))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa))
      (RefsGC.evalExps_cons' (Memory.evalExp_constPct ei32 (RefsGC.evalExp_addNat
        (RefsGC.evalExp_unpct (evalExp_var fi)) (RefsGC.evalExp_num' (m := .natN 1))))
      (RefsGC.evalExps_cons' (Memory.evalExp_constPct ei32 (RefsGC.evalExp_addNat
        (RefsGC.evalExp_unpct (evalExp_var fj)) (RefsGC.evalExp_num' (m := .natN 1))))
      (RefsGC.evalExps_cons' (Memory.evalExp_constPct ei32 (RefsGC.evalExp_predNat
        (evalExp_var fn) hn1))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
        RefsGC.evalExps_nil'))))))))))
  refine ⟨[arrRef k, constI32 i, .ref r, .plain (.arraySet x), arrRef k,
    constI32 ((show BitVec 32 from i) + 1), constI32 ((show BitVec 32 from j) + 1),
    constI32 ((show BitVec 32 from n) - 1), .plain (.arrayInitElem x y)], ?_,
    .aggregate (.arrayInitElemSucc ha hel ⟨hle₁, hle₂⟩ hn0 hr)⟩
  rw [hw]
  simp only [adminsToV, adminToV_constI32,
    RefsGC.toNat_add_one (by omega : i.toNat + 1 < 2 ^ 32),
    RefsGC.toNat_add_one (by omega : j.toNat + 1 < 2 ^ 32), RefsGC.toNat_sub_one hn0]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Read

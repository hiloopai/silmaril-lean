module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Zero

/-!
# Round 5, pass 2, track read: `array.new_elem-alloc` (74), backward, under `ReadValidS`

The premise `ref^n = $elem(z, y).REFS[i : n]` is read back: the iteration over the quantifier
`ref*` evaluates only when `ref*` has exactly `n` entries (`iterN_len`), and then to `ref*`
itself; the slice evaluates only in bounds (`slice?_eq_some_list`, upstream item U2), to
`(refs.drop i).take n`. The segment resolves by `ReadValidS.seg`. Core's `arrayNewElemAlloc`
then produces the same references.
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
open Round4Read (decode_aconst_at)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **A `^n` iteration over a list quantifier evaluates only at the list's length.** -/
theorem iterN_len {env : Env} {ρ : VarEnv} {b : Exp} {x d c : IL.Id} {ws : List Value} {k : Nat}
    {v : Value} (hc : ρ.findVal? c = some (.num (.natN k))) (hd : ρ.findVal? d = some (.list ws))
    (h : EvalExp env ρ (.iterE b (.mk (.listN (.varE c) none) [.mk x (.varE d)])) v) :
    ws.length = k := by
  obtain ⟨N, h⟩ := evalExp_iterE_iff.1 h
  rcases N with _ | _ | N
  · simp [evalIterE] at h
  · simp [evalIterE, evalDoms] at h
  · rcases N with _ | N
    · simp [evalIterE, evalDoms, evalExp] at h
    · simp [evalIterE, evalDoms, domVar, domSrc, evalExp, hd, hc, Value.asNat?] at h
      rcases N with _ | N
      all_goals simp [evalIterList, Value.asList?] at h
      all_goals exact h.1

/-- **`Step_read` 74 (`array.new_elem-alloc`), backward, under `ReadValidS`.** -/
theorem bwdS_arrayNewElemAlloc : ∀ (c : Config H) (w : Value), ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 74 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayNewElemAlloc hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  obtain ⟨RS, frs, hRS⟩ := hq "ref*" (.iterT (.varT "ref" []) .list) (by simp)
  obtain ⟨ws, rfl⟩ := hasTyp_list_isList hRS
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.NEW_ELEM" (.tuple [X, Y])]]) := by
    concl_inv hl
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Aggregates.adminsToV_eq_triple hcode
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₁
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₂
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := Bwd.head_arrayNewElem (Typing.adminToV_case h₃).symm
  have eXY : X = Encode.toValue x ∧ Y = Encode.toValue y := by
    have h₃' : Value.case "ARRAY.NEW_ELEM" (.tuple [Encode.toValue x, Encode.toValue y]) = _ := h₃
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h₃'
    exact ⟨h₃'.1.symm, h₃'.2.symm⟩
  obtain ⟨rfl, rfl⟩ := eXY
  subst hZ
  obtain ⟨⟨ea, ei⟩, hel⟩ := Option.isSome_iff_exists.1 hv.seg.2.2.1
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  have hlen : ws.length = n.toNat := iterN_len fn frs e₁
  have fn' : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN ws.length)) := by
    rw [hlen]; exact fn
  have ev₁ : v₁ = .list ws :=
    EvalExp.unique e₁ (Equiv.ExecReadAggregate.evalExp_iterNVar (by decide) fn' frs)
  subst ev₁
  obtain ⟨L, p, q, hL, hpe, hqe, hsl⟩ := evalExp_sliceE_iff.1 e₂
  have eL : L = .list (ei.refs.map refToValue) := EvalExp.unique hL
    (RefsGC.evalExp_elemRefs G (valsOnly_bindVals σ) hel (evalExp_var fz) (evalExp_var fy))
  have ep : p = i.toNat := by
    simpa using EvalExp.unique hpe (RefsGC.evalExp_unpct (evalExp_var fi))
  have eq' : q = n.toNat := by simpa using EvalExp.unique hqe (evalExp_var fn)
  subst eL ep eq'
  obtain ⟨l, hl', hbnd, rfl⟩ := Equiv.ExecReadAggregate.slice?_eq_some_list hsl
  cases hl'
  have hws : ws = ((ei.refs.map refToValue).drop i.toNat).take n.toNat := by
    have := RefsGC.eq_of_evalExp_eq (ifPrem (hp _ List.mem_cons_self))
      (Equiv.ExecReadAggregate.evalExp_iterNVar (by decide) fn' frs)
      (evalExp_sliceE_iff.2 ⟨_, _, _, hL, hpe, hqe, hsl⟩)
    simpa using this
  have hle : i.toNat + n.toNat ≤ ei.refs.length := by simpa using hbnd
  have hcon : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.iterE (.subE (.varE "ref") (.varT "ref" []) (.varT "instr" []))
        (.mk (.listN (.varE "n") none) [.mk "ref" (.varE "ref*")])) (.list (ws.map id)) :=
    evalExp_iterNMap fn' frs fun _ _ =>
      RefsGC.evalExp_sub_of (evalExp_var (findVal_bind1 (by decide)))
  have hw : w = .list (ws.map id ++ [.case "ARRAY.NEW_FIXED"
      (.tuple [Encode.toValue x, .case "%" (.tuple [.num (.natN n.toNat)])])]) :=
    EvalExp.unique (RefsGC.rhs_of_concl he) (evalExp_cat hcon (evalExp_list1 (evalExp_case
      (evalExp_tup2 (evalExp_var fx) (evalExp_case (evalExp_tupE_iff.2
        ⟨_, evalExps_cons (evalExp_var fn) evalExps_nil, rfl⟩))))))
  have hs : Step P host ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewElem x y)]⟩
      ⟨s, f, ((ei.refs.drop i.toNat).take n.toNat).map .ref ++
        [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩ :=
    .aggregate (.arrayNewElemAlloc hel hle)
  refine ⟨_, ?_, hs⟩
  rw [hw, R4Fwd.adminsToV_app, R4Fwd.adminsToV_refs, List.map_id, hws, List.map_take,
    List.map_drop]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Read

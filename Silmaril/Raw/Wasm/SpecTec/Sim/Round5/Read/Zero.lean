module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read.Fill
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Defs

/-!
# Round 5, pass 2, track read: `array.copy-zero` (90), `array.init_elem-zero` (96), backward

Both rules carry `otherwise` and `n = 0`. Core's `-zero` steps need the instances to exist and
the start indices in bounds. The arrays exist by reference liveness (`ReadValidR.live`), the
element segment of `array.init_elem` resolves by `ReadValidS.seg`. An index out of bounds would
make the matching `-oob` rule (88/89, resp. 94/95) fire on the same left-hand side at the same
assignment (the rules share their quantifiers), against `otherwise`.
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

/-- `TRAP` as the one instruction of a right-hand side. -/
theorem evalExp_trapList {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.listE [.caseE "TRAP" (.tupE [])]) (.list [.case "TRAP" (.tuple [])]) :=
  evalExp_list1 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))

/-- **`Step_read` 90 (`array.copy-zero`), backward, under reference liveness.** -/
theorem bwdR_arrayCopyZero : ∀ (c : Config H) (w : Value), Bwd.ReadValidR c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 90 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayCopyZero hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A₁, fa₁, -⟩ := hq "a_1" (.varT "addr" []) (by simp)
  obtain ⟨I₁, fi₁, -⟩ := hq "i_1" State.num32T (by simp)
  obtain ⟨A₂, fa₂, -⟩ := hq "a_2" (.varT "addr" []) (by simp)
  obtain ⟨I₂, fi₂, -⟩ := hq "i_2" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  have hc : ∃ X, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A₁, .case "CONST" (.tuple [.case "I32" (.tuple []), I₁]),
      .case "REF.ARRAY_ADDR" A₂, .case "CONST" (.tuple [.case "I32" (.tuple []), I₂]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.COPY" X]]) ∧ w = .list [] := by
    concl_inv he
  obtain ⟨X, hcfg, hw⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩ := Bwd.adminsToV_eq_six hcode
  obtain ⟨k₁, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i₁, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨k₂, rfl, rfl⟩ := decode_refArray h₃
  obtain ⟨i₂, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₄
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₅
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x₁, x₂, rfl⟩ := Bwd.head_arrayCopy (Typing.adminToV_case h₆).symm
  subst hZ
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (evalExp_var fn) RefsGC.evalExp_num'
  have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hn0
  obtain ⟨ai₁, ha₁⟩ := Option.isSome_iff_exists.1 hv.live.1
  obtain ⟨ai₂, ha₂⟩ := Option.isSome_iff_exists.1 hv.live.2.2.1
  have ho := Round4Read.else_head hp
  have hl := RefsGC.lhs_of_concl he
  have hle₁ : i₁.toNat ≤ ai₁.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayCopyOob1 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl evalExp_trapList, fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi₁)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_arrayFields G (valsOnly_bindVals σ) (evalExp_var fz)
        (evalExp_var fa₁) ha₁)) (by simpa using hlt))
  have hle₂ : i₂.toNat ≤ ai₂.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayCopyOob2 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl evalExp_trapList, fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi₂)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_arrayFields G (valsOnly_bindVals σ) (evalExp_var fz)
        (evalExp_var fa₂) ha₂)) (by simpa using hlt))
  refine ⟨[], by rw [hw]; rfl, ?_⟩
  exact .aggregate (.arrayCopyZero ha₁ ha₂ ⟨hle₁, hle₂⟩)

/-- **`Step_read` 96 (`array.init_elem-zero`), backward, under `ReadValidS`.** -/
theorem bwdS_arrayInitElemZero : ∀ (c : Config H) (w : Value), ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 96 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayInitElemZero hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "REF.ARRAY_ADDR" A, .case "CONST" (.tuple [.case "I32" (.tuple []), I]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.INIT_ELEM" (.tuple [X, Y])]]) ∧ w = .list [] := by
    concl_inv he
  obtain ⟨hcfg, hw⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨j, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₃
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, y, rfl⟩ := BwdRead.head_arrayInitElem (Typing.adminToV_case h₅).symm
  subst hZ
  have eY : Y = Encode.toValue y := by
    injection h₅ with _ h
    injection h with h
    injection h with _ h
    injection h with h
    exact h.symm
  subst eY
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (evalExp_var fn) RefsGC.evalExp_num'
  have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hn0
  obtain ⟨ai, ha⟩ := Option.isSome_iff_exists.1 hv.r.live.1
  obtain ⟨⟨ea, ei⟩, hel⟩ := Option.isSome_iff_exists.1 hv.seg.2.2.2.2.1
  have ho := Round4Read.else_head hp
  have hl := RefsGC.lhs_of_concl he
  have hle₁ : i.toNat ≤ ai.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayInitElemOob1 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl evalExp_trapList, fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_arrayFields G (valsOnly_bindVals σ) (evalExp_var fz)
        (evalExp_var fa) ha)) (by simpa using hlt))
  have hle₂ : j.toNat ≤ ei.refs.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayInitElemOob2 ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl evalExp_trapList, fun pr hpr => ?_⟩
    rw [List.mem_singleton.1 hpr]
    exact .ifPr (RefsGC.evalExp_gtNat (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fj)) (evalExp_var fn))
      (RefsGC.evalExp_len (RefsGC.evalExp_elemRefs G (valsOnly_bindVals σ) hel (evalExp_var fz)
        (evalExp_var fy))) (by simpa using hlt))
  refine ⟨[], by rw [hw]; rfl, ?_⟩
  exact .aggregate (.arrayInitElemZero ha hel ⟨hle₁, hle₂⟩)

end Silmaril.Wasm.SpecTec.Sim.Round5.Read

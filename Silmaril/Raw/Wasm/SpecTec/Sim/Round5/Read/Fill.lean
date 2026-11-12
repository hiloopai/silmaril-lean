module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms

/-!
# Round 5, pass 2, track read: `array.fill-succ` (85), backward, under reference liveness

The rule's only premise is `otherwise`. Read backwards: if `i + n > |a.FIELDS|`, `array.fill-oob`
(83) would fire on the same left-hand side; if `n = 0`, `array.fill-zero` (84) would, its own
`otherwise` holding because 82 and 83 do not fire (`RefsGC.not_arrayFillNull`,
`RefsGC.not_arrayFillOob`). Both need the array to exist, which `ReadValidR.live` gives. The
successor's `i + 1` does not wrap: `i + n ≤ |a.FIELDS| < 2 ^ 32` (`Aggregates.Bounded`).
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

/-- An `i32` constant's image. -/
theorem adminToV_constI32 (b : BitVec 32) :
    adminToV (constI32 b) = aconstV (.case "I32" (.tuple [])) b.toNat := rfl

/-- **`Step_read` 85 (`array.fill-succ`), backward, under reference liveness.** -/
theorem bwdR_arrayFillSucc : ∀ (c : Config H) (w : Value), Bwd.ReadValidR c →
    Typed (simEnv (BI P hn host)) hn c →
    Fires (simEnv (BI P hn host)) "Step_read" 85 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Fwd.rStore_builtins hn host
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayFillSucc hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨V, fv, hV⟩ := hq "val" State.valT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.ARRAY_ADDR" A,
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]), V,
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.FILL" X]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨v, rfl⟩ := (Typing.stateDecode_simEnv _).val a₃ _ (valsOnly_bindVals σ) (h₃ ▸ hV)
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, rfl⟩ := BwdRead.head_arrayFill (Typing.adminToV_case h₅).symm
  subst hZ
  have eV : V = valV v := by rw [← h₃, State.adminToV_toAdmin]
  have eX : X = idxV x.toNat := by
    injection h₅ with _ h
    exact h.symm
  subst eV eX
  obtain ⟨ai, ha⟩ := Option.isSome_iff_exists.1 hv.live.1
  have ho := Round4Read.else_head hp
  have hle : i.toNat + n.toNat ≤ ai.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      RR.arrayFillOob ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩ ?_
    exact Bwd.body_arrayFillOob _ hq (RefsGC.lhs_of_concl he) fz fa fi fn ha hlt
  have hn0 : n ≠ 0 := by
    rintro rfl
    refine BwdPureStep.otherwise_false ho (by decide) RR.arrayFillZero ⟨_, _, _, rfl, rfl⟩
      ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 (RefsGC.lhs_of_concl he)
        (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩), fun pr hpr => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · refine .elsePr ?_
      exact RefsGC.otherwise_of_ruleAt RR.arrayFillZero (RefsGC.readTable_simEnv _) (i := 84)
        (by decide) (exc := [82, 83]) RefsGC.lhsIn_arrayFill (by decide) (by
          intro j hj _ r' hr' w hw
          obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
          rcases (by simpa using hj : j = 82 ∨ j = 83) with rfl | rfl
          · rw [RefsGC.relRules_of_ruleAt RR.arrayFillNull hr']
            exact RefsGC.not_arrayFillNull
          · rw [RefsGC.relRules_of_ruleAt RR.arrayFillOob hr']
            exact RefsGC.not_arrayFillOob G ha hle)
    · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simp; exact RefsGC.evalExp_num'))
  have hlen : ai.fields.length < 2 ^ 32 := Aggregates.Bounded.array hv.read.store.aggs ha
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have ei32 : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.caseE "I32" (.tupE [])) (.case "I32" (.tuple [])) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)
  have hw : w = .list [.case "REF.ARRAY_ADDR" (.num (.natN k)), aconstV (.case "I32" (.tuple []))
      i.toNat, valV v, .case "ARRAY.SET" (idxV x.toNat), .case "REF.ARRAY_ADDR" (.num (.natN k)),
      aconstV (.case "I32" (.tuple [])) (i.toNat + 1), valV v,
      aconstV (.case "I32" (.tuple [])) (n.toNat - 1), .case "ARRAY.FILL" (idxV x.toNat)] := by
    refine EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ei32 (evalExp_var fi)))
      (RefsGC.evalExps_cons' (RefsGC.evalExp_sub_of (evalExp_var fv))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fa))
      (RefsGC.evalExps_cons' (Memory.evalExp_constPct ei32 (RefsGC.evalExp_addNat
        (RefsGC.evalExp_unpct (evalExp_var fi)) (RefsGC.evalExp_num' (m := .natN 1))))
      (RefsGC.evalExps_cons' (RefsGC.evalExp_sub_of (evalExp_var fv))
      (RefsGC.evalExps_cons' (Memory.evalExp_constPct ei32 (RefsGC.evalExp_predNat
        (evalExp_var fn) hn1))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx)) RefsGC.evalExps_nil'))))))))))
  refine ⟨[arrRef k, constI32 i, v.toAdmin, .plain (.arraySet x), arrRef k,
    constI32 ((show BitVec 32 from i) + 1), v.toAdmin, constI32 ((show BitVec 32 from n) - 1),
    .plain (.arrayFill x)], ?_, .aggregate (.arrayFillSucc ha hle hn0)⟩
  rw [hw]
  simp only [adminsToV, State.adminToV_toAdmin, adminToV_constI32,
    RefsGC.toNat_add_one (by omega : i.toNat + 1 < 2 ^ 32), RefsGC.toNat_sub_one hn0]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Read

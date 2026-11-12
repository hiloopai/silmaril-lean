module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5Bwd.AggOob

/-!
# Round 5: `array.fill-zero` (84), backward, under reference liveness

The rule's `otherwise` is read backwards as in `table.fill-zero`: if Core's
side condition `i ≤ |a.FIELDS|` failed, `array.fill-oob` (83) would fire on the same left-hand
side (`body_arrayFillOob`, built at the instance's own assignment). That needs the array to
exist, which `ReadValidR.live` gives; without it the rule is false (`not_remainingV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV)
open BwdRead (cfg_inv)
open Round4Read (decode_refArray decode_aconst_at)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

variable (B : Builtins)

/-- `|$arrayinst(z)[a].FIELDS|` at a live array, in a rule scope. -/
theorem evalExp_arrayLen {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {k : Nat}
    {ai : ArrayInst} (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN k)))
    (ha : s.arrays[k]? = some ai) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS"))
      (.num (.natN ai.fields.length)) := by
  have hl := Aggregates.evalExp_arrayinst (Aggregates.aggDefs_simEnv B) rfl (evalExp_var fz)
    (hn := hn) (s := s) (f := f)
  have hidx : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) (arrayInstV ai) :=
    evalExp_idxE_iff.2 ⟨_, k, hl, evalExp_var fa, by simp [Value.idx?, ha]⟩
  have hfs : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
      (.list (ai.fields.map fieldValV)) :=
    evalExp_dotE_iff.2 ⟨_, hidx, by simp [arrayInstV, Value.field?]⟩
  simpa using evalExp_lenE_iff.2 ⟨_, hfs, rfl⟩

/-- `array.fill-oob` (83) fires on the left-hand side of an `array.fill-zero` instance whose
range is out of bounds: the body, at that instance's assignment. -/
theorem body_arrayFillOob {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {k i n : Nat}
    {ai : ArrayInst} {L : Value} {els : Prop}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) [.expP "z" (.varT "state" []),
      .expP "a" (.varT "addr" []), .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
      .expP "val" (.varT "val" []), .expP "n" (.varT "n" []), .expP "x" (.varT "idx" [])])
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "REF.ARRAY_ADDR" (.varE "a"),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]),
      .subE (.varE "val") (.varT "val" []) (.varT "instr" []),
      .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
      .caseE "ARRAY.FILL" (.varE "x")]])) L)
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN k)))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV i))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n)))
    (ha : s.arrays[k]? = some ai) (hoob : ai.fields.length < i + n) :
    RuleBody (simEnv B) (DDerives (simEnv B) noElse) els [] [] "%~>%"
      Equiv.ExecRead.arrayFillOobRule (.tuple [L, .list [.case "TRAP" (.tuple [])]]) := by
  refine ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (evalExp_list1 (evalExp_case
    (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))), fun pr hpr => ?_⟩
  rw [List.mem_singleton.1 hpr]
  exact .ifPr (RefsGC.evalExp_cmpNat (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct
    (evalExp_var fi)) (evalExp_var fn)) (evalExp_arrayLen B fz fa ha) (by simp [Num.cmp, hoob]))

/-- **`Step_read` 84 (`array.fill-zero`), backward, under reference liveness.** -/
theorem bwdR_arrayFillZero : ∀ (c : Config H) (w : Value), ReadValidR c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 84 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayFillZero hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨V, fv, hV⟩ := hq "val" State.valT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.ARRAY_ADDR" A,
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]), V,
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.FILL" X]]) ∧ w = .list [] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨v, rfl⟩ := (Typing.stateDecode_simEnv B).val a₃ _ (valsOnly_bindVals σ) (h₃ ▸ hV)
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, rfl⟩ := BwdRead.head_arrayFill (Typing.adminToV_case h₅).symm
  subst hZ
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (evalExp_var fn) RefsGC.evalExp_num'
  have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hn0
  obtain ⟨ai, ha⟩ := Option.isSome_iff_exists.1 hv.live.1
  have ho := Round4Read.else_head hp
  have hle : i.toNat ≤ ai.fields.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      (State.hasReadRules_simEnv B).arrayFillOob ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩ ?_
    exact body_arrayFillOob B hq (RefsGC.lhs_of_concl he) fz fa fi fn ha (by simpa using hlt)
  refine ⟨[], by rw [hc.2]; rfl, ?_⟩
  exact .aggregate (.arrayFillZero ha hle)

end Silmaril.Wasm.SpecTec.Sim.Round5.Bwd

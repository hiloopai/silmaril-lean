module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4Read.Common

/-!
# Track r4-read: `Step_read/table.fill-zero` (29), `table.fill-succ` (30), backward, under
validity

Both rules carry `otherwise`. Backwards it is read as "no earlier rule fires on this left-hand
side": if Core's side condition failed, `table.fill-oob` (28), resp. `table.fill-zero` (29), would
fire on the same left-hand side, at the same assignment (the three rules share their quantifiers
and left-hand side), against the `otherwise` premise. Building those bodies evaluates
`$table(z, x)`, which needs the table to exist: `ReadValid` (index resolution) gives it. Without it
both rules fire from a dangling index where Core is stuck. The successor's `i + 1` does not wrap
because `i + n ≤ |table|` and the store bounds keep tables below `2 ^ 32` entries.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv adminsToV_eq_quad decode_tableFill decode_aconst)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The `otherwise` premise heading a premise list. -/
theorem else_head {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {ps : List Prem}
    (h : ∀ pr ∈ Prem.elsePr :: ps, PremW env D els ρ pr) : els := by
  cases h _ List.mem_cons_self with
  | elsePr h => exact h

/-- The `table.fill` configuration, as `Memory.fillCode`. -/
theorem configV_fill (s : Store H) (f : Frame) (t : AddrType) (b b' : BitVec t.intType.width)
    (v : Val) (x : TableIdx) :
    configV hn ⟨s, f, [aconst t b, v.toAdmin, aconst t b', .plain (.tableFill x)]⟩ =
      cfgV (stV (storeV hn s) (frameV f))
        (Memory.fillCode (Encode.toValue t) (valV v) b.toNat b'.toNat x.toNat) := by
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin]
  rfl

variable (B : Builtins)

/-- `table.fill-oob` (28) fires on the left-hand side of a `table.fill-zero`/`-succ` instance
whose range is out of bounds: the body, at that instance's assignment. -/
theorem body_tableFillOob {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : TableIdx}
    {ta : Nat} {ti : TableInst} {i k : Nat} {L : Value} {els : Prop}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) [.expP "z" (.varT "state" []),
      .expP "at" (.varT "addrtype" []), .expP "i" (.varT "num_" [.expA (.subE (.varE "at")
        (.varT "addrtype" []) (.varT "numtype" []))]), .expP "val" (.varT "val" []),
      .expP "n" (.varT "n" []), .expP "x" (.varT "idx" [])])
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i"]),
      .subE (.varE "val") (.varT "val" []) (.varT "instr" []),
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])]),
      .caseE "TABLE.FILL" (.varE "x")]])) L)
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV i))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN k)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (ht : s.table? f x = some (ta, ti)) (hoob : ti.refs.length < i + k) :
    RuleBody (simEnv B) (DDerives (simEnv B) noElse) els [] [] "%~>%"
      Equiv.ExecRead.tableFillOobRule (.tuple [L, .list [.case "TRAP" (.tuple [])]]) := by
  refine ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (evalExp_list1 (evalExp_case
    (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))), fun pr hpr => ?_⟩
  rw [List.mem_singleton.1 hpr]
  have hlen := State.evalExp_tableLen (State.stateDefs_simEnv B) fz fx rfl
    (State.tableAt_of_table? hn ht) (State.tableInstV_REFS ti)
  rw [List.length_map] at hlen
  exact .ifPr (RefsGC.evalExp_cmpNat (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct
    (evalExp_var fi)) (evalExp_var fn)) hlen (by simp [Num.cmp, hoob]))

/-- The shared reading of a `table.fill-zero`/`-succ` instance: the left-hand side decoded, the
table resolved. -/
theorem fill_inv {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {is : List Admin}
    {Z AT I V N X : Value}
    (hv : ReadValid (⟨s, f, is⟩ : Config H))
    (fv : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) State.valT V)
    (hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), V, .case "CONST" (.tuple [AT, .case "%" (.tuple [N])]),
      .case "TABLE.FILL" X]])) :
    ∃ (t : AddrType) (b b' : BitVec t.intType.width) (v : Val) (x : TableIdx) (ta : Nat)
      (ti : TableInst),
      is = [aconst t b, v.toAdmin, aconst t b', .plain (.tableFill x)] ∧
      Z = stV (storeV hn s) (frameV f) ∧ AT = Encode.toValue t ∧ I = idxV b.toNat ∧
      V = valV v ∧ N = .num (.natN b'.toNat) ∧ X = idxV x.toNat ∧
      s.table? f x = some (ta, ti) := by
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x, rfl, hX⟩ := decode_tableFill h₄
  obtain ⟨v, rfl⟩ := (Typing.stateDecode_simEnv B).val a₂ _ (valsOnly_bindVals σ) (h₂ ▸ fv)
  obtain ⟨t, b', rfl, hAT, hN⟩ := decode_aconst h₃
  subst hAT
  obtain ⟨b, rfl, hI⟩ := decode_aconst_at h₁
  obtain ⟨ta, ti, ht⟩ := table_of_isSome (idx_last4 hv (c := ⟨s, f, is⟩) his)
  refine ⟨t, b, b', v, x, ta, ti, his, hZ, rfl, hI, ?_, ?_, hX, ht⟩
  · rw [← h₂, State.adminToV_toAdmin]
  · simpa using hN

/-- **`Step_read` 29 (`table.fill-zero`), backward, under validity.** -/
theorem bwdV_tableFillZero : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 29 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableFillZero hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨V, fv, hV⟩ := hq "val" State.valT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "CONST" (.tuple [AT, I]),
      V, .case "CONST" (.tuple [AT, .case "%" (.tuple [N])]), .case "TABLE.FILL" X]]) ∧
      w = .list [] := by
    concl_inv he
  obtain ⟨t, b, b', v, x, ta, ti, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht⟩ := fill_inv B hv hV hc.1
  have h0 : Value.num (.natN b'.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) (evalExp_var fn) RefsGC.evalExp_num'
  have hb' : b' = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hb'
  have ho := else_head hp
  have hle : b.toNat ≤ ti.refs.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      (State.hasReadRules_simEnv B).tableFillOob ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩ ?_
    exact body_tableFillOob B hq (RefsGC.lhs_of_concl he) fz fi fn fx ht (by simpa using hlt)
  refine ⟨[], by rw [hc.2]; rfl, ?_⟩
  exact .table (.fillZero ht hle)

/-- **`Step_read` 30 (`table.fill-succ`), backward, under validity.** -/
theorem bwdV_tableFillSucc : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 30 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableFillSucc hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨V, fv, hV⟩ := hq "val" State.valT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "CONST" (.tuple [AT, I]),
      V, .case "CONST" (.tuple [AT, .case "%" (.tuple [N])]), .case "TABLE.FILL" X]]) := by
    have hl := RefsGC.lhs_of_concl he
    concl_inv hl
  obtain ⟨t, b, b', v, x, ta, ti, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht⟩ := fill_inv B hv hV hc
  have ho := else_head hp
  have hle : b.toNat + b'.toNat ≤ ti.refs.length := by
    refine Nat.le_of_not_lt fun hlt => BwdPureStep.otherwise_false ho (by decide)
      (State.hasReadRules_simEnv B).tableFillOob ⟨_, _, .list [.case "TRAP" (.tuple [])], rfl, rfl⟩ ?_
    exact body_tableFillOob B hq (RefsGC.lhs_of_concl he) fz fi fn fx ht hlt
  have hn0 : b' ≠ 0 := by
    rintro rfl
    refine BwdPureStep.otherwise_false ho (by decide)
      (State.hasReadRules_simEnv B).tableFillZero ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl,
        hq, evalExp_tup2 (RefsGC.lhs_of_concl he) (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩),
        fun pr hpr => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
    rcases hpr with rfl | rfl
    · refine .elsePr ?_
      rw [configV_fill]
      exact RefsGC.otherwise_of_ruleAt (State.hasReadRules_simEnv B).tableFillZero
        (RefsGC.readTable_simEnv B) (i := 29) (by decide) (exc := [28])
        Memory.lhsIn_tableFill (by decide) (by
          intro j hj _ r' hr' w hw
          obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
          obtain rfl : j = 28 := by simpa using hj
          rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).tableFillOob hr']
          exact Memory.not_tableFillOob (State.stateDefs_simEnv B) (State.tableAt_of_table? hn ht)
            (State.tableInstV_REFS ti) (by simpa using hle))
    · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simp; exact RefsGC.evalExp_num'))
  have hw32 := lt_width (a := t) (table_lt32 hv.store ht)
  have hb' : 1 ≤ b'.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have ea : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" [])) (Encode.toValue t) :=
    RefsGC.evalExp_sub_of (evalExp_var fa)
  have hw : w = .list [aconstV (Encode.toValue t) b.toNat, valV v, .case "TABLE.SET" (idxV x.toNat),
      aconstV (Encode.toValue t) (b.toNat + 1), valV v, aconstV (Encode.toValue t) (b'.toNat - 1),
      .case "TABLE.FILL" (idxV x.toNat)] := by
    refine EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea (evalExp_var fi)))
      (RefsGC.evalExps_cons' (RefsGC.evalExp_sub_of (evalExp_var fv))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx))
      (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea (RefsGC.evalExp_addNat
        (RefsGC.evalExp_unpct (evalExp_var fi)) (RefsGC.evalExp_num' (m := .natN 1))))
      (RefsGC.evalExps_cons' (RefsGC.evalExp_sub_of (evalExp_var fv))
      (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea (RefsGC.evalExp_predNat (evalExp_var fn)
        hb'))
      (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx)) RefsGC.evalExps_nil'))))))))
  refine ⟨[aconst t b, v.toAdmin, .plain (.tableSet x), aconst t (b + 1), v.toAdmin,
    aconst t (b' - 1), .plain (.tableFill x)], ?_, .table (.fillSucc ht hle hn0)⟩
  rw [hw]
  simp only [adminsToV, State.adminToV_aconst, State.adminToV_toAdmin,
    Memory.toNat_add_one (by omega : b.toNat + 1 < 2 ^ t.intType.width),
    Memory.toNat_sub_one hn0]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round4Read

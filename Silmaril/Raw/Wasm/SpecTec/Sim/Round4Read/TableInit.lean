module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.TableCopy

/-!
# Track r4-read: `Step_read/table.init-zero` (36), `table.init-succ` (37), backward, under
validity

As for `table.copy`: `otherwise` is read back by firing `table.init-oob` (35) on the same
left-hand side when a range is out of bounds, and `table.init-zero` (36) when the count is zero.
The three rules share quantifiers and left-hand side, so the earlier bodies reuse the instance's
assignment. Index resolution makes `$table(z, x)` and `$elem(z, y)` evaluate; the store bounds
keep `i + 1` and `j + 1` from wrapping.
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
open BwdRead (cfg_inv adminsToV_eq_quad decode_aconst decode_tableInit)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The `table.init` configuration, as `Memory.initCode`. -/
theorem configV_init (s : Store H) (f : Frame) {t : AddrType} (b : BitVec t.intType.width)
    (j n : BitVec 32) (x : TableIdx) (y : ElemIdx) :
    configV hn ⟨s, f, [aconst t b, constI32 j, constI32 n, .plain (.tableInit x y)]⟩ =
      cfgV (stV (storeV hn s) (frameV f)) (Memory.initCode (Encode.toValue t) b.toNat j.toNat
        n.toNat x.toNat y.toNat) := by
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    Memory.adminToV_constI32]
  rfl

variable (B : Builtins)

/-- The quantifiers of rules 35–37 of `Step_read`. -/
abbrev initQuants : List Param := [.expP "z" (.varT "state" []), .expP "at" (.varT "addrtype" []),
  .expP "i" (.varT "num_" [.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []))]),
  .expP "j" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "n" (.varT "n" []),
  .expP "x" (.varT "idx" []), .expP "y" (.varT "idx" [])]

/-- The left-hand side of rules 35–37 of `Step_read`. -/
abbrev initLhs : Exp := .caseE "%;%" (.tupE [.varE "z", .listE [
  .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
    .varE "i"]),
  .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"]),
  .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
  .caseE "TABLE.INIT" (.tupE [.varE "x", .varE "y"])]])

/-- The shared reading of a `table.init-zero`/`-succ` instance. -/
theorem init_inv {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {is : List Admin}
    {Z AT I J N X Y : Value}
    (hv : ReadValid (⟨s, f, is⟩ : Config H))
    (hAT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) State.addrtypeT AT)
    (hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "TABLE.INIT" (.tuple [X, Y])]])) :
    ∃ (t : AddrType) (b : BitVec t.intType.width) (j n : BitVec 32) (x : TableIdx) (y : ElemIdx)
      (ta ea : Nat) (ti : TableInst) (ei : ElemInst),
      is = [aconst t b, constI32 j, constI32 n, .plain (.tableInit x y)] ∧
      Z = stV (storeV hn s) (frameV f) ∧ AT = Encode.toValue t ∧ I = idxV b.toNat ∧
      J = idxV j.toNat ∧ N = .num (.natN n.toNat) ∧ X = idxV x.toNat ∧ Y = idxV y.toNat ∧
      s.table? f x = some (ta, ti) ∧ s.elem? f y = some (ea, ei) := by
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x, y, rfl, hXY⟩ := decode_tableInit h₄
  have hXY' : X = idxV x.toNat ∧ Y = idxV y.toNat := by
    simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hXY
  obtain ⟨t, b, rfl, hA, hI⟩ := decode_aconst_typed (valsOnly_bindVals σ) h₁ hAT
  obtain ⟨j, rfl, hJ⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₃
  have eN : N = .num (.natN n.toNat) := by
    have := Value.tuple.inj (Value.case.inj hN).2
    simp only [List.cons.injEq, and_true] at this
    exact this
  obtain ⟨ix, iy⟩ := idx_last4 hv (c := ⟨s, f, is⟩) his
  obtain ⟨ta, ti, ht⟩ := table_of_isSome ix
  obtain ⟨ea, ei, hei⟩ := elem_of_isSome iy
  exact ⟨t, b, j, n, x, y, ta, ea, ti, ei, his, hZ, hA, hI, hJ, eN, hXY'.1,
    hXY'.2, ht, hei⟩

/-- In-bounds ranges, recovered from `otherwise` after `table.init-oob` (35). -/
theorem init_inBounds {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t : AddrType}
    {b : BitVec t.intType.width} {j n : BitVec 32} {x : TableIdx} {y : ElemIdx} {ta ea : Nat}
    {ti : TableInst} {ei : ElemInst} {k : Nat} {w : Value} (hk : 35 < k)
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) initQuants)
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) initLhs
      (configV hn ⟨s, f, [aconst t b, constI32 j, constI32 n, .plain (.tableInit x y)]⟩))
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV b.toNat))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (idxV j.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fy : (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV y.toNat))
    (ht : s.table? f x = some (ta, ti)) (hei : s.elem? f y = some (ea, ei))
    (ho : otherwise (simEnv B) "Step_read" [] k (.tuple [configV hn ⟨s, f, [aconst t b,
      constI32 j, constI32 n, .plain (.tableInit x y)]⟩, w])) :
    b.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length := by
  by_contra hoob
  have hor := evalExp_or (t := .boolT)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var fi))
        (evalExp_var fn)) (evalExp_tableLen' B fz fx ht) rfl)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var fj))
        (evalExp_var fn)) (evalExp_elemLen' B fz fy hei) rfl)
  rw [decide_eq_true (by omega)] at hor
  refine BwdPureStep.otherwise_false ho hk (State.hasReadRules_simEnv B).tableInitOob
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (evalExp_list1
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))), fun pr hpr => ?_⟩
  rw [List.mem_singleton.1 hpr]
  exact .ifPr hor

/-- A non-zero count, recovered from `otherwise` after `table.init-zero` (36). -/
theorem init_nonzero {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t : AddrType}
    {b : BitVec t.intType.width} {j n : BitVec 32} {x : TableIdx} {y : ElemIdx} {ta ea : Nat}
    {ti : TableInst} {ei : ElemInst} {w : Value}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) initQuants)
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) initLhs
      (configV hn ⟨s, f, [aconst t b, constI32 j, constI32 n, .plain (.tableInit x y)]⟩))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (ht : s.table? f x = some (ta, ti)) (hei : s.elem? f y = some (ea, ei))
    (hb : b.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length)
    (ho : otherwise (simEnv B) "Step_read" [] 37 (.tuple [configV hn ⟨s, f, [aconst t b,
      constI32 j, constI32 n, .plain (.tableInit x y)]⟩, w])) : n ≠ 0 := by
  rintro rfl
  refine BwdPureStep.otherwise_false ho (by decide) (State.hasReadRules_simEnv B).tableInitZero
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq,
      evalExp_tup2 hl (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩), fun pr hpr => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · refine .elsePr ?_
    rw [configV_init]
    exact RefsGC.otherwise_of_ruleAt (State.hasReadRules_simEnv B).tableInitZero
      (RefsGC.readTable_simEnv B) (i := 36) (by decide) (exc := [35]) Memory.lhsIn_tableInit
      (by decide) (by
        intro j' hj _ r' hr' w hw
        obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
        obtain rfl : j' = 35 := by simpa using hj
        rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).tableInitOob hr']
        exact Memory.not_tableInitOob (State.stateDefs_simEnv B) (State.tableAt_of_table? hn ht)
          (State.tableInstV_REFS ti) (Memory.elemAt_of_elem? hn hei) (Memory.elemInstV_REFS ei)
          (by simpa using hb))
  · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simpa using RefsGC.evalExp_num'))

/-- **`Step_read` 36 (`table.init-zero`), backward, under validity.** -/
theorem bwdV_tableInitZero : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 36 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableInitZero hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, hAT⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "TABLE.INIT" (.tuple [X, Y])]]) ∧ w = .list [] := by
    concl_inv he
  obtain ⟨t, b, j, n, x, y, ta, ea, ti, ei, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht, hei⟩ :=
    init_inv B hv hAT hc.1
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) (evalExp_var fn) RefsGC.evalExp_num'
  have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hn0
  have hb := init_inBounds B (k := 36) (by decide) hq (RefsGC.lhs_of_concl he) fz fi fj fn fx fy
    ht hei (else_head hp)
  refine ⟨[], by rw [hc.2]; rfl, ?_⟩
  exact .table (.initZero ht hei (by simpa using hb))

/-- **`Step_read` 37 (`table.init-succ`), backward, under validity.** -/
theorem bwdV_tableInitSucc : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 37 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableInitSucc hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨AT, fa, hAT⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" (State.numAtT "at") (by simp)
  obtain ⟨J, fj, -⟩ := hq "j" State.num32T (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨Y, fy, -⟩ := hq "y" State.idxT (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "TABLE.INIT" (.tuple [X, Y])]]) := by
    concl_inv hl
  obtain ⟨t, b, j, n, x, y, ta, ea, ti, ei, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht, hei⟩ :=
    init_inv B hv hAT hc
  have ho := else_head hp
  have hb := init_inBounds B (k := 37) (by decide) hq hl fz fi fj fn fx fy ht hei ho
  have hn0 := init_nonzero B hq hl fn ht hei hb ho
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hjlt : j.toNat < ei.refs.length := by omega
  have hr : ei.refs[j.toNat]? = some ei.refs[j.toNat] := List.getElem?_eq_getElem hjlt
  have hwt := lt_width (a := t) (table_lt32 hv.store ht)
  have hwe := elem_lt32 hv.store hei
  have ea' := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var fa)
  have e₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.subE (.idxE (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE "y")]) "REFS")
        (.projE (.uncaseE (.varE "j") "%") 0)) (.varT "ref" []) (.varT "instr" []))
      (refToValue ei.refs[j.toNat]) :=
    RefsGC.evalExp_sub_of (RefsGC.evalExp_idx (RefsGC.evalExp_dot (Memory.evalExp_elem_of
      (State.stateDefs_simEnv B) (evalExp_var fz) (evalExp_var fy) (Memory.elemAt_of_elem? hn hei))
      (Memory.elemInstV_REFS ei)) (RefsGC.evalExp_unpct (evalExp_var fj)) (by simp [hr]))
  have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea' (evalExp_var fi)))
    (RefsGC.evalExps_cons' e₂
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_var fx))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea' (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct (et := .caseE "I32" (.tupE []))
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fj)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct (et := .caseE "I32" (.tupE []))
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (RefsGC.evalExp_predNat (evalExp_var fn) hn1))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
      RefsGC.evalExps_nil'))))))))
  refine ⟨[aconst t b, .ref ei.refs[j.toNat], .plain (.tableSet x), aconst t (b + 1),
    constI32 (j + 1), constI32 (n - 1), .plain (.tableInit x y)], ?_,
    .table (.initSucc ht hei hb hn0 hr)⟩
  rw [hw]
  simp only [adminsToV, State.adminToV_aconst, State.adminToV_ref,
    Memory.adminToV_constI32, Memory.toNat_add_one (by omega : b.toNat + 1 < 2 ^ t.intType.width),
    Memory.toNat_add_one (by omega : j.toNat + 1 < 2 ^ 32), Memory.toNat_sub_one hn0]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round4Read

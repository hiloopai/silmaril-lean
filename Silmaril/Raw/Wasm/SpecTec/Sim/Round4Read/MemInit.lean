module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.MemCopy

/-!
# Track r4-read: `Step_read/memory.init-zero` (61), `memory.init-succ` (62), backward, under
validity

As for `memory.copy`: `otherwise` is read back by firing `memory.init-oob` (60) on the same
left-hand side when a range is out of bounds, and `memory.init-zero` (61) when the count is zero.
The three rules share quantifiers and left-hand side, so the earlier bodies reuse the instance's
assignment. Index resolution makes `$mem(z, x)` and `$data(z, y)` evaluate; the store bounds
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
open BwdRead (cfg_inv adminsToV_eq_quad decode_aconst)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- The `memory.init` configuration, as `Memory.minitCode`. -/
theorem configV_minit (s : Store H) (f : Frame) {t : AddrType} (b : BitVec t.intType.width)
    (j n : BitVec 32) (x : MemIdx) (y : DataIdx) :
    configV hn ⟨s, f, [aconst t b, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩ =
      cfgV (stV (storeV hn s) (frameV f)) (Memory.minitCode (Encode.toValue t) b.toNat j.toNat
        n.toNat x.toNat y.toNat) := by
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    Memory.adminToV_constI32]
  rfl

variable (B : Builtins)

/-- The quantifiers of rules 60–62 of `Step_read`. -/
abbrev minitQuants : List Param := [.expP "z" (.varT "state" []), .expP "at" (.varT "addrtype" []),
  .expP "i" (.varT "num_" [.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []))]),
  .expP "j" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "n" (.varT "n" []),
  .expP "x" (.varT "idx" []), .expP "y" (.varT "idx" [])]

/-- The left-hand side of rules 60–62 of `Step_read`. -/
abbrev minitLhs : Exp := .caseE "%;%" (.tupE [.varE "z", .listE [
  .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
    .varE "i"]),
  .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"]),
  .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])]),
  .caseE "MEMORY.INIT" (.tupE [.varE "x", .varE "y"])]])

/-- The shared reading of a `memory.init-zero`/`-succ` instance. -/
theorem minit_inv {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {is : List Admin}
    {Z AT I J N X Y : Value}
    (hv : ReadValid (⟨s, f, is⟩ : Config H))
    (hAT : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) State.addrtypeT AT)
    (hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [
      .case "CONST" (.tuple [AT, I]), .case "CONST" (.tuple [.case "I32" (.tuple []), J]),
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "MEMORY.INIT" (.tuple [X, Y])]])) :
    ∃ (t : AddrType) (b : BitVec t.intType.width) (j n : BitVec 32) (x : MemIdx) (y : DataIdx)
      (ma da : Nat) (mi : MemInst) (di : DataInst),
      is = [aconst t b, constI32 j, constI32 n, .plain (.memoryInit x y)] ∧
      Z = stV (storeV hn s) (frameV f) ∧ AT = Encode.toValue t ∧ I = idxV b.toNat ∧
      J = idxV j.toNat ∧ N = .num (.natN n.toNat) ∧ X = idxV x.toNat ∧ Y = idxV y.toNat ∧
      s.mem? f x = some (ma, mi) ∧ s.data? f y = some (da, di) := by
  obtain ⟨hZ, hcode⟩ := cfg_inv hc
  obtain ⟨a₁, a₂, a₃, a₄, his, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_quad hcode
  obtain ⟨x, y, rfl, hXY⟩ := decode_memoryInit h₄
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
  obtain ⟨ma, mi, ht⟩ := mem_of_isSome ix
  obtain ⟨da, di, hdi⟩ := data_of_isSome iy
  exact ⟨t, b, j, n, x, y, ma, da, mi, di, his, hZ, hA, hI, hJ, eN, hXY'.1,
    hXY'.2, ht, hdi⟩

/-- In-bounds ranges, recovered from `otherwise` after `memory.init-oob` (60). -/
theorem minit_inBounds {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t : AddrType}
    {b : BitVec t.intType.width} {j n : BitVec 32} {x : MemIdx} {y : DataIdx} {ma da : Nat}
    {mi : MemInst} {di : DataInst} {k : Nat} {w : Value} (hk : 60 < k)
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) minitQuants)
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) minitLhs
      (configV hn ⟨s, f, [aconst t b, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩))
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (idxV b.toNat))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (idxV j.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x.toNat))
    (fy : (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV y.toNat))
    (ht : s.mem? f x = some (ma, mi)) (hdi : s.data? f y = some (da, di))
    (ho : otherwise (simEnv B) "Step_read" [] k (.tuple [configV hn ⟨s, f, [aconst t b,
      constI32 j, constI32 n, .plain (.memoryInit x y)]⟩, w])) :
    b.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size := by
  by_contra hoob
  have hor := evalExp_or (t := .boolT)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var fi))
        (evalExp_var fn)) (evalExp_memLen' B fz fx ht) rfl)
    (RefsGC.evalExp_cmpNat (op := .gtOp) (t := .numT .natT)
      (RefsGC.evalExp_addNat (t := .numT .natT) (RefsGC.evalExp_unpct (evalExp_var fj))
        (evalExp_var fn)) (evalExp_dataLen' B fz fy hdi) rfl)
  rw [decide_eq_true (by omega)] at hor
  refine BwdPureStep.otherwise_false ho hk (State.hasReadRules_simEnv B).memoryInitOob
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq, evalExp_tup2 hl (evalExp_list1
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))), fun pr hpr => ?_⟩
  rw [List.mem_singleton.1 hpr]
  exact .ifPr hor

/-- A non-zero count, recovered from `otherwise` after `memory.init-zero` (61). -/
theorem minit_nonzero {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {t : AddrType}
    {b : BitVec t.intType.width} {j n : BitVec 32} {x : MemIdx} {y : DataIdx} {ma da : Nat}
    {mi : MemInst} {di : DataInst} {w : Value}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) minitQuants)
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) minitLhs
      (configV hn ⟨s, f, [aconst t b, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (ht : s.mem? f x = some (ma, mi)) (hdi : s.data? f y = some (da, di))
    (hb : b.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size)
    (ho : otherwise (simEnv B) "Step_read" [] 62 (.tuple [configV hn ⟨s, f, [aconst t b,
      constI32 j, constI32 n, .plain (.memoryInit x y)]⟩, w])) : n ≠ 0 := by
  rintro rfl
  refine BwdPureStep.otherwise_false ho (by decide) (State.hasReadRules_simEnv B).memoryInitZero
    ⟨_, _, _, rfl, rfl⟩ ⟨rfl, VarEnv.empty, σ, rfl, hq,
      evalExp_tup2 hl (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩), fun pr hpr => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · refine .elsePr ?_
    rw [configV_minit]
    exact RefsGC.otherwise_of_ruleAt (State.hasReadRules_simEnv B).memoryInitZero
      (RefsGC.readTable_simEnv B) (i := 61) (by decide) (exc := [60]) Memory.lhsIn_memoryInit
      (by decide) (by
        intro j' hj _ r' hr' w hw
        obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
        obtain rfl : j' = 60 := by simpa using hj
        rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).memoryInitOob hr']
        exact Memory.not_memoryInitOob (State.stateDefs_simEnv B) (Memory.memAt_of_mem? hn ht)
          (Memory.memInstV_BYTES mi) (Memory.dataAt_of_data? hn hdi) (Memory.dataInstV_BYTES di)
          (by simpa using hb))
  · exact .ifPr (RefsGC.evalExp_eq_true (evalExp_var fn) (by simpa using RefsGC.evalExp_num'))

/-- **`Step_read` 61 (`memory.init-zero`), backward, under validity.** -/
theorem bwdV_memoryInitZero : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 61 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memoryInitZero hf)
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
      .case "MEMORY.INIT" (.tuple [X, Y])]]) ∧ w = .list [] := by
    concl_inv he
  obtain ⟨t, b, j, n, x, y, ma, da, mi, di, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht, hdi⟩ :=
    minit_inv B hv hAT hc.1
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) :=
    RefsGC.eq_of_evalExp_eq (ifPrem (hp _ (List.mem_cons_of_mem _ List.mem_cons_self))) (evalExp_var fn) RefsGC.evalExp_num'
  have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst hn0
  have hb := minit_inBounds B (k := 61) (by decide) hq (RefsGC.lhs_of_concl he) fz fi fj fn fx fy
    ht hdi (else_head hp)
  refine ⟨[], by rw [hc.2]; rfl, ?_⟩
  exact .memory (.initZero ht hdi (by simpa using hb))

/-- **`Step_read` 62 (`memory.init-succ`), backward, under validity.** -/
theorem bwdV_memoryInitSucc : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 62 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memoryInitSucc hf)
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
      .case "MEMORY.INIT" (.tuple [X, Y])]]) := by
    concl_inv hl
  obtain ⟨t, b, j, n, x, y, ma, da, mi, di, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht, hdi⟩ :=
    minit_inv B hv hAT hc
  have ho := else_head hp
  have hb := minit_inBounds B (k := 62) (by decide) hq hl fz fi fj fn fx fy ht hdi ho
  have hn0 := minit_nonzero B hq hl fn ht hdi hb ho
  have hn1 : 1 ≤ n.toNat := Nat.one_le_iff_ne_zero.2 fun h => hn0 (BitVec.eq_of_toNat_eq h)
  have hjlt : j.toNat < di.bytes.data.size := by
    have := hb.2
    change j.toNat < di.bytes.size
    omega
  have hbyte : di.bytes.data[j.toNat]? = some di.bytes.data[j.toNat] :=
    Array.getElem?_eq_getElem hjlt
  have hwt := lt_width (a := t) (mem_lt32 hv.store ht)
  have hwe := data_lt32 hv.store hdi
  have ea' := RefsGC.evalExp_sub_of (env := simEnv B) (t₁ := .varT "addrtype" [])
    (t₂ := .varT "numtype" []) (evalExp_var fa)
  have ei32 : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "I32" (.tupE []))
      (.case "I32" (.tuple [])) := evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)
  have hr' : (Memory.bytesL di.bytes)[j.toNat]? = some (idxV di.bytes.data[j.toNat].toNat) := by
    simp [Memory.bytesL, hbyte]
    rfl
  have e₂ := Memory.evalExp_constPct (et := .caseE "I32" (.tupE [])) ei32 (RefsGC.evalExp_unpct
    (RefsGC.evalExp_idx (RefsGC.evalExp_dot (Memory.evalExp_data_of (State.stateDefs_simEnv B)
      (evalExp_var fz) (evalExp_var fy) (Memory.dataAt_of_data? hn hdi))
      (Memory.dataInstV_BYTES di)) (RefsGC.evalExp_unpct (evalExp_var fj)) hr'))
  have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (RefsGC.evalExp_listE_of
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 ea' (evalExp_var fi)))
    (RefsGC.evalExps_cons' e₂
    (RefsGC.evalExps_cons' (Memory.evalExp_store8 (Memory.memarg0Ok_simEnv B σ) (evalExp_var fx))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct ea' (RefsGC.evalExp_addNat
      (RefsGC.evalExp_unpct (evalExp_var fi)) (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct (et := .caseE "I32" (.tupE [])) ei32
      (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fj))
        (RefsGC.evalExp_num' (m := .natN 1))))
    (RefsGC.evalExps_cons' (Memory.evalExp_constPct (et := .caseE "I32" (.tupE [])) ei32
      (RefsGC.evalExp_predNat (evalExp_var fn) hn1))
    (RefsGC.evalExps_cons' (evalExp_case (evalExp_tup2 (evalExp_var fx) (evalExp_var fy)))
      RefsGC.evalExps_nil'))))))))
  have hb32 : di.bytes.data[j.toNat].toNat < 2 ^ 32 :=
    Nat.lt_of_lt_of_le di.bytes.data[j.toNat].toNat_lt (by decide)
  refine ⟨[aconst t b, constI32 (BitVec.ofNat 32 di.bytes.data[j.toNat].toNat), store8 x,
    aconst t (b + 1), constI32 (j + 1), constI32 (n - 1), .plain (.memoryInit x y)], ?_,
    .memory (.initSucc ht hdi hb hn0 hbyte)⟩
  rw [hw]
  simp only [adminsToV, State.adminToV_aconst, Memory.adminToV_store8,
    Memory.adminToV_constI32, Memory.toNat_add_one (by omega : b.toNat + 1 < 2 ^ t.intType.width),
    Memory.toNat_add_one (by omega : j.toNat + 1 < 2 ^ 32), Memory.toNat_sub_one hn0,
    Memory.toNat_ofNat_of_lt hb32]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round4Read

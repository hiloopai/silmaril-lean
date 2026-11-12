module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Grow

/-!
# Round 4: the size-result rules backward, over bounded stores

`Step_read/table.size` (27), `memory.size` (52) and `array.len-array` (81) put the exact count
`n` in their result `CONST at (% n)`; Core's result is `BitVec.ofNat _ n`. Track bwd-read found
that the two differ for a table or array of `2 ^ 32` or more entries (or a memory of `2 ^ 48`
bytes or more), so these backward lemmas need a store bound. Round 2's `Integrate.StoreOk`
(part of `Round4.Bounded`) is enough: the count is below `2 ^ 32`, so `BitVec.ofNat` keeps it.
No validity is needed: the premises already resolve the index (`$table(z, x)`, `$mem(z, x)`,
`$arrayinst(z)[a]` evaluate only in range).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (idxV)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem head_tableSize {a : Admin} (h : Typing.adminHead a = "TABLE.SIZE") :
    ∃ x, a = .plain (.tableSize x) := by
  revert h
  admin_head_inv

theorem head_memorySize {a : Admin} (h : Typing.adminHead a = "MEMORY.SIZE") :
    ∃ x, a = .plain (.memorySize x) := by
  revert h
  admin_head_inv

/-- The only image tagged `TABLE.SIZE` is `table.size`'s. -/
theorem decode_tableSize {a : Admin} {X : Value} (h : adminToV a = .case "TABLE.SIZE" X) :
    ∃ x : TableIdx, a = .plain (.tableSize x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_tableSize (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

/-- The only image tagged `MEMORY.SIZE` is `memory.size`'s. -/
theorem decode_memorySize {a : Admin} {X : Value} (h : adminToV a = .case "MEMORY.SIZE" X) :
    ∃ x : MemIdx, a = .plain (.memorySize x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_memorySize (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

/-- An address-typed constant with a count below `2 ^ 32` is encoded with that count. -/
theorem adminToV_aconst_ofNat (a : AddrType) {k : Nat} (hk : k < 2 ^ 32) :
    adminToV (aconst a (BitVec.ofNat _ k)) =
      .case "CONST" (.tuple [Encode.toValue a, .case "%" (.tuple [.num (.natN k)])]) := by
  rw [State.adminToV_aconst,
    Memory.toNat_ofNat_of_lt (lt_of_lt_of_le hk (Memory.pow32_le a))]

/-- `n * 65536 = m` on natural numerals, read back: `n` is `m / 65536`. -/
theorem mulPage_inv {N : Value} {m : Nat}
    (h : binValues .mulOp N (.num (.natN 65536)) = .ok (.num (.natN m))) :
    N = .num (.natN (m / 65536)) := by
  cases N with
  | num k =>
    cases k <;> simp [binValues, Num.bin, Res.ofOption] at h
    rename_i k
    rw [← h, Nat.mul_div_cancel _ (by decide)]
  | _ => simp [binValues] at h

variable (B : Builtins) (NA : BwdRead.NoAcc B)
include NA

/-- **`Step_read/table.size` (27) backward, over a bounded store.** -/
theorem bwd_tableSize : ∀ (c : Config H) (w : Value), Integrate.StoreOk c.store →
    Fires (simEnv B) "Step_read" 27 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hS hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (State.hasReadRules_simEnv B).tableSize hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨LIM, fl, -⟩ := hq "lim" (.varT "limits" []) (by simp)
  obtain ⟨RT, fr, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "TABLE.SIZE" X]]) ∧
      w = .list [.case "CONST" (.tuple [AT, .case "%" (.tuple [N])])] := by
    concl_inv he
  obtain ⟨hZ, a, rfl, ha⟩ := BwdRead.cfg_single_inv hc.1
  obtain ⟨x, rfl, hX⟩ := decode_tableSize ha
  have hp₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT
      (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS"))
      (.varE "n")) (.bool true) := ifPrem (hp _ (by simp))
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hp₁
  obtain ⟨ta, ti, ht, hv₁⟩ := BwdRead.tableLen_inv B NA rfl (hZ ▸ fz) (hX ▸ fx) e₁
  have eN : N = .num (.natN ti.refs.length) :=
    (EvalExp.unique e₂ (evalExp_var fn)).symm.trans ((cmpValues_eq_true_iff.1 hcmp).symm.trans hv₁)
  have hp₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT
      (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "TYPE")
      (.caseE "%%%" (.tupE [.varE "at", .varE "lim", .varE "rt"]))) (.bool true) :=
    ifPrem (hp _ (by simp))
  obtain ⟨u₁, u₂, f₁, f₂, hcmp₂⟩ := evalExp_cmpE_iff.1 hp₂
  obtain ⟨T, hT, hTt⟩ := evalExp_dotE_iff.1 f₁
  obtain ⟨ta', ti', ht', rfl⟩ := BwdRead.table_inv B NA rfl (hZ ▸ fz) (hX ▸ fx) hT
  obtain ⟨rfl, rfl⟩ : ta = ta' ∧ ti = ti' := by
    rw [ht] at ht'
    simpa using ht'
  have eu₂ : u₂ = .case "%%%" (.tuple [AT, LIM, RT]) :=
    EvalExp.unique f₂ (evalExp_case (evalExp_tup3 (evalExp_var fa) (evalExp_var fl)
      (evalExp_var fr)))
  have eu₁ : u₁ = .case "%%%" (.tuple [Encode.toValue ti.type.address,
      Encode.toValue ti.type.limits, Silmaril.SpecTec.Equiv.Validation.tyV ti.type.element]) := by
    simpa using hTt.symm
  have eAT : AT = Encode.toValue ti.type.address := by
    have := (cmpValues_eq_true_iff.1 hcmp₂).symm.trans eu₁
    rw [eu₂] at this
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at this
    exact this.1
  have hlt : ti.refs.length < 2 ^ 32 :=
    hS.tables.1 ti (List.mem_of_getElem? (Store.table?_spec ht).2)
  refine ⟨[aconst ti.type.address (BitVec.ofNat _ ti.refs.length)], ?_, .table (.size ht)⟩
  simp only [hc.2, eAT, eN, adminsToV, adminToV_aconst_ofNat _ hlt]

/-- **`Step_read/memory.size` (52) backward, over a bounded store.** -/
theorem bwd_memorySize : ∀ (c : Config H) (w : Value), Integrate.StoreOk c.store →
    Fires (simEnv B) "Step_read" 52 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hS hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).memorySize hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  obtain ⟨AT, fa, -⟩ := hq "at" State.addrtypeT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨LIM, fl, -⟩ := hq "lim" (.varT "limits" []) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "MEMORY.SIZE" X]]) ∧
      w = .list [.case "CONST" (.tuple [AT, .case "%" (.tuple [N])])] := by
    concl_inv he
  obtain ⟨hZ, a, rfl, ha⟩ := BwdRead.cfg_single_inv hc.1
  obtain ⟨x, rfl, hX⟩ := decode_memorySize ha
  have hp₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT
      (.binE .mulOp (.numT .natT) (.varE "n")
        (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])))
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")))
      (.bool true) := ifPrem (hp _ (by simp))
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hp₁
  obtain ⟨ma, mi, hm, hv₂⟩ := BwdRead.memLen_inv B NA rfl (hZ ▸ fz) (hX ▸ fx) e₂
  have hpage : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])) (.num (.natN 65536)) :=
    evalExp_binE_iff.2 ⟨_, evalExp_num, .inr ⟨by simp [boolShort], _,
      Memory.kiOk_simEnv B σ, by simp [binValues, Num.bin, Res.ofOption]⟩⟩
  obtain ⟨n₁, h₁, hs | ⟨-, n₂, h₂, hb⟩⟩ := evalExp_binE_iff.1 e₁
  · simp [boolShort] at hs
  have en₁ : n₁ = N := EvalExp.unique h₁ (evalExp_var fn)
  have en₂ : n₂ = .num (.natN 65536) := EvalExp.unique h₂ hpage
  have ev₁ : v₁ = .num (.natN mi.bytes.size) := (cmpValues_eq_true_iff.1 hcmp).trans hv₂
  rw [en₁, en₂, ev₁] at hb
  have eN := mulPage_inv hb
  have hp₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.cmpE .eqOp .boolT
      (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "TYPE")
      (.caseE "%%PAGE" (.tupE [.varE "at", .varE "lim"]))) (.bool true) :=
    ifPrem (hp _ (by simp))
  obtain ⟨u₁, u₂, f₁, f₂, hcmp₂⟩ := evalExp_cmpE_iff.1 hp₂
  obtain ⟨M, hM, hMt⟩ := evalExp_dotE_iff.1 f₁
  obtain ⟨ma', mi', hm', rfl⟩ := BwdRead.mem_inv B NA rfl (hZ ▸ fz) (hX ▸ fx) hM
  obtain ⟨rfl, rfl⟩ : ma = ma' ∧ mi = mi' := by
    rw [hm] at hm'
    simpa using hm'
  have eu₂ : u₂ = .case "%%PAGE" (.tuple [AT, LIM]) :=
    EvalExp.unique f₂ (evalExp_case (evalExp_tup2 (evalExp_var fa) (evalExp_var fl)))
  have eu₁ : u₁ = .case "%%PAGE" (.tuple [Encode.toValue mi.type.address,
      Encode.toValue mi.type.limits]) := by
    simpa using hMt.symm
  have eAT : AT = Encode.toValue mi.type.address := by
    have := (cmpValues_eq_true_iff.1 hcmp₂).symm.trans eu₁
    rw [eu₂] at this
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at this
    exact this.1
  have hsz : mi.bytes.size < 2 ^ 32 :=
    (hS.mems mi (List.mem_of_getElem? (Store.mem?_spec hm).2)).2
  have hpg : mi.pages = mi.bytes.size / 65536 := rfl
  have hlt : mi.pages < 2 ^ 32 := by rw [hpg]; omega
  refine ⟨[aconst mi.type.address (BitVec.ofNat _ mi.pages)], ?_, .memory (.size hm)⟩
  simp only [hc.2, eAT, eN, adminsToV]
  rw [adminToV_aconst_ofNat _ hlt, hpg]

omit NA in
/-- **`Step_read/array.len-array` (81) backward, over a bounded store.** -/
theorem bwd_arrayLenArray : ∀ (c : Config H) (w : Value), Integrate.StoreOk c.store →
    Fires (simEnv B) "Step_read" 81 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hS hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayLenArray hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.ARRAY_ADDR" A,
      .case "ARRAY.LEN" (.tuple [])]]) ∧ ∃ R, EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.lenE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")) R ∧
        w = .list [.case "CONST" (.tuple [caseNilV "I32", .case "%" (.tuple [R])])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := BwdRead.cfg_inv hc.1
  obtain ⟨R, hR, hw⟩ := hc.2
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨k, rfl⟩ := BwdPureStep.head_refArray (Typing.adminToV_case h₁).symm
  obtain rfl := BwdRead.aggDecode.arrayLen a₂ _ h₂
  have eA : A = .num (.natN k) := by
    have h₁' : Value.case "REF.ARRAY_ADDR" (.num (.natN k)) = .case "REF.ARRAY_ADDR" A := h₁
    exact (Value.case.inj h₁').2.symm
  obtain ⟨fs, hfs, rfl⟩ := evalExp_lenE_iff.1 hR
  obtain ⟨V, hV, hVf⟩ := evalExp_dotE_iff.1 hfs
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 hV
  have eL : L = .list (s.arrays.map arrayInstV) :=
    EvalExp.unique hL (Aggregates.evalExp_arrayinst (Aggregates.aggDefs_simEnv B) rfl
      (evalExp_var (hZ ▸ fz)))
  have ej : j = k := by
    have := EvalExp.unique hj (evalExp_var fa)
    rw [eA] at this
    simpa using this
  subst eL ej
  have hmap : (s.arrays[j]?).map arrayInstV = some V := by simpa [Value.idx?] using hLj
  obtain ⟨ai, hai, rfl⟩ := Option.map_eq_some_iff.1 hmap
  have efs : fs = ai.fields.map fieldValV := by simpa [arrayInstV] using hVf.symm
  have hlt : ai.fields.length < 2 ^ 32 := hS.aggs.arrays ai (List.mem_of_getElem? hai)
  refine ⟨[constI32 (BitVec.ofNat 32 ai.fields.length)], ?_, .aggregate (.arrayLenArray hai)⟩
  have e32 : adminToV (constI32 (BitVec.ofNat 32 ai.fields.length)) =
      .case "CONST" (.tuple [caseNilV "I32", .case "%" (.tuple [.num (.natN ai.fields.length)])]) := by
    rw [show adminToV (constI32 (BitVec.ofNat 32 ai.fields.length)) =
      adminToV (aconst .i32 (BitVec.ofNat _ ai.fields.length)) from rfl,
      adminToV_aconst_ofNat .i32 hlt]
    rfl
  simp only [hw, efs, List.length_map, adminsToV, e32]

end Silmaril.Wasm.SpecTec.Sim.Round4

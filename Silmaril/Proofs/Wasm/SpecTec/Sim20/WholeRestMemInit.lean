module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestInit

/-!
# `memory.init`, `-zero` and `-succ`, backwards

`Step_read` 44–46 are `memory.init-trap` (`i + n > |$data(z, x).BYTES|` or
`j + n > |$mem(z, 0).BYTES|`), `-zero` and `-succ`, the `memory` counterparts of `table.init`
(`WholeRestInit`). `-succ` reads the byte `$data(z, x).BYTES[i]` (`evalExp_data20`); the encoding
of a byte string lists `ByteArray.data` in order (`byteArray_toList_eq`), so it is V2's
`di.bytes.data[i]`.

This discharges `Step_read` 45 and 46 (`bwdRead_memoryInitZero`, `bwdRead_memoryInitSucc`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 evalExp_idxPayload HasClause1 idxPayload)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Byte strings and `$data` -/

theorem toList_loop_stop (bs : ByteArray) {i : Nat} {r : List UInt8} (hi : ¬ i < bs.size) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  have hd : bs.data.toList.drop i = [] := by
    apply List.drop_eq_nil_of_le
    rw [Array.length_toList]
    exact Nat.le_of_not_lt hi
  rw [ByteArray.toList.loop, ite_eq_right hi, hd, List.append_nil]

theorem toList_loop_next (bs : ByteArray) {i : Nat} {r : List UInt8} (hi : i < bs.size) :
    ByteArray.toList.loop bs i r =
      ByteArray.toList.loop bs (i + 1) (bs.data.toList[i]'(by simpa using hi) :: r) := by
  have hget : bs.get! i = bs.data.toList[i]'(by simpa using hi) := by
    obtain ⟨d⟩ := bs
    simp only [ByteArray.get!, Array.getElem_toList]
    exact getElem!_pos d i hi
  rw [ByteArray.toList.loop, ite_eq_left hi, hget]

theorem toList_loop_eq (bs : ByteArray) :
    ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro k
  induction k with
  | zero => exact fun i r hk => toList_loop_stop bs (by omega)
  | succ k ih =>
    intro i r hk
    have hi : i < bs.size := by omega
    have hi' : i < bs.data.toList.length := by simpa using hi
    rw [toList_loop_next bs hi, ih (i + 1) _ (by omega), List.drop_eq_getElem_cons hi']
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- **The list of a byte string is its data, in order.** -/
theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  have := toList_loop_eq bs bs.size 0 [] (by simp)
  simpa [ByteArray.toList] using this

theorem hasClause_data20 : HasClause1 (simEnv20 B) "data" State.sfxPat
    (.idxE (.dotE (.varE "s") "DATAS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "DATAS")
      idxPayload)) := ⟨_, _, _, rfl⟩

/-- **`$data(z, x)`**. -/
theorem evalExp_data20 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : DataIdx}
    {a : Nat} {di : DataInst} (hρ : ρ.findDef? "data" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (ha : f.module.datas[x.toNat]? = some a) (hd : s.datas[a]? = some di) :
    EvalExp (simEnv20 B) ρ (.callE "data" [.expA ez, .expA ex]) (dataInstV di) :=
  evalExp_call1 hasClause_data20 hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil))
    State.matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, a, evalExp_dotE_iff.2 ⟨storeV hn s,
      evalExp_var rfl, rfl⟩, evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2
        ⟨moduleInstV f.module, evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl,
          State.frameV_module f⟩, rfl⟩, evalExp_idxPayload rfl,
        by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
      by simp [Value.idx?, List.getElem?_map, hd]⟩)

/-- `$data(z, x).BYTES`. -/
abbrev dataBytesE : Exp := .dotE (.callE "data" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES"

/-- `$data(z, x).BYTES`, evaluated. -/
theorem evalExp_dataBytes20 {ρ : VarEnv} {s : Store H} {f : Frame} {x : DataIdx} {a : Nat}
    {di : DataInst} (hρ : ρ.findDef? "data" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (idxV x)) (ha : f.module.datas[x.toNat]? = some a)
    (hd : s.datas[a]? = some di) :
    EvalExp (simEnv20 B) ρ dataBytesE (bytesV di.bytes) :=
  evalExp_dotE_iff.2 ⟨dataInstV di, evalExp_data20 hρ (evalExp_var fz) (evalExp_var fx) ha hd, rfl⟩

/-! ## `memory.init`, verbatim -/

/-- The quantifiers of the `memory.init` rules. -/
abbrev memInitQs : List Param :=
  [.expP "z" (.varT "state" []), .expP "j" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]),
    .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "n" (.varT "n" []),
    .expP "x" (.varT "idx" [])]

/-- `MEMORY.INIT x`. -/
abbrev memInitE : Exp := .caseE "MEMORY.INIT" (.varE "x")

/-- The left-hand side of the `memory.init` rules. -/
abbrev memInitLhs : Exp :=
  .caseE "%;%" (.tupE [.varE "z", .listE [constJE, constIE, constNE, memInitE]])

/-- `Step_read/memory.init-trap`, rule 44 (verbatim). -/
def memInitTrapRule : Rule :=
  .ruleD "memory.init-trap" memInitQs "%~>%" (.tupE [memInitLhs, trapRhs])
    [.ifPr (.binE .orOp .boolT
      (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) iPay (.varE "n")) (.lenE dataBytesE))
      (.cmpE .gtOp (.numT .natT) (.binE .addOp (.numT .natT) jPay (.varE "n")) memLenE))]

/-- `Step_read/memory.init-zero`, rule 45 (verbatim). -/
def memInitZeroRule : Rule :=
  .ruleD "memory.init-zero" memInitQs "%~>%" (.tupE [memInitLhs, .listE []])
    [.elsePr, .ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0)))]

/-- `$data(z, x).BYTES[i].%.0`. -/
abbrev dataByteE : Exp := .projE (.uncaseE (.idxE dataBytesE iPay) "%") 0

/-- `Step_read/memory.init-succ`, rule 46 (verbatim). -/
def memInitSuccRule : Rule :=
  .ruleD "memory.init-succ" memInitQs "%~>%" (.tupE [memInitLhs, .listE [constJE,
    constPE dataByteE, store8E, constSuccE jPay, constSuccE iPay, constPE predE, memInitE]])
    [.elsePr]

theorem hasRuleAt_memInitTrap : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 44 memInitTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_memInitZero : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 45 memInitZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_memInitSucc : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 46 memInitSuccRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem head20_memoryInit {a : Admin} (h : adminHead20 a = "MEMORY.INIT") :
    ∃ x, a = .plain (.memoryInit x) := by
  revert h; admin_head_inv20

/-- A defined data segment, from `InstrResOk`. -/
theorem data_of_isSome {s : Store H} {f : Frame} {x : DataIdx}
    (h : ((⟨s, f⟩ : State H).data? x).isSome) :
    ∃ a di, f.module.datas[x.toNat]? = some a ∧ s.datas[a]? = some di :=
  data_of_res (x := x) h

/-- **A firing `memory.init` rule after 44 gives both bounds.** -/
theorem memInit_bound {k : Nat} (hk : 44 < k) {σ : List (IL.Id × Value)} {c : Config H}
    {w : Value} {j i n : BitVec 32} {x : DataIdx} {am ad : Nat} {mi : MemInst} {di : DataInst}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) memInitQs)
    (hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) memInitLhs (configV hn c))
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame))
    (fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.toNat))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN n.toNat)))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x))
    (ham : c.frame.module.memAddr? memIdx0 = some am) (hm : c.store.memInst? am = some mi)
    (had : c.frame.module.datas[x.toNat]? = some ad) (hd : c.store.datas[ad]? = some di)
    (ho : Sim.otherwise (simEnv20 B) "Step_read" [] k (.tuple [configV hn c, w])) :
    i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size := by
  by_contra hb
  refine otherwise_absurd hasRuleAt_memInitTrap hk ho (b' := .list [caseNilV "TRAP"])
    (body_ifRule hq (evalExp_tup2 hl evalExp_trapRhs) ?_)
  have hdl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.lenE dataBytesE)
      (.num (.natN di.bytes.size)) := by
    refine evalExp_lenE_iff.2 ⟨_, evalExp_dataBytes20 rfl fz fx had hd, ?_⟩
    rw [(bytesV_length20 di.bytes).2]
  refine evalExp_or (evalExp_gtNat (evalExp_addNat20 (evalExp_iPay fi) (evalExp_var fn)) hdl)
    (evalExp_gtNat (evalExp_addNat20 (evalExp_jPay fj) (evalExp_var fn))
      (evalExp_memLen20 rfl fz ham hm)) ?_
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

/-! ## The two rules backwards -/

theorem bwdRead_memoryInitZero {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 45 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_memInitZero hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x, rfl⟩ := head20_memoryInit (head20_of_caseE h₄)
  have fx := idx_of_caseE (X := idxV x) h₄ rfl
  have hres : InstrResOk (⟨s, f⟩ : State H) (.memoryInit x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨am, mi, ham, hm⟩ := mem_of_isSome hres.1
  obtain ⟨ad, di, had, hd⟩ := data_of_isSome hres.2
  have hb := memInit_bound (by decide) hq hl fz fj fi fn fx ham hm had hd
    (else_of_prem (hp _ (List.mem_cons_self ..)))
  obtain rfl := zero_of_prem fn
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have ew : w = [] := Value.list.inj (EvalExp.unique hr Pure.evalExp_list0)
  refine ⟨[], ew, .memoryInitZero (mi := mi) (di := di) (by simp [State.mem?, ham, hm])
    (by simp [State.data?, ModuleInst.dataAddr?, Store.dataInst?, had, hd]) ?_⟩
  simpa using hb

/-- The image of `memory.init-succ`'s V2 right-hand side. -/
theorem adminsToV_memoryInitSucc (j i n : BitVec 32) (b : UInt8) (x : DataIdx)
    (hj : j.toNat + 1 < 2 ^ 32) (hi : i.toNat + 1 < 2 ^ 32) (hn : n ≠ 0) :
    adminsToV [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8, constI32 (j + 1),
        constI32 (i + 1), constI32 (n - 1), .plain (.memoryInit x)] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
        .case "CONST" (.tuple [caseNilV "I32", pctV b.toNat]), adminToV store8,
        .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
        .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
        .case "MEMORY.INIT" (idxV x)] := by
  have hb : (BitVec.ofNat 32 b.toNat).toNat = b.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans b.toNat_lt (by decide))]
  simp only [adminsToV, adminToV_constI32, hb, toNat_add_one hj, toNat_add_one hi,
    toNat_sub_one hn]
  rfl

/-- The byte `$data(z, x).BYTES[i].%.0`, evaluated. -/
theorem evalExp_dataByte20 {ρ : VarEnv} {s : Store H} {f : Frame} {x : DataIdx} {a : Nat}
    {di : DataInst} {i : BitVec 32} {b : UInt8} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (idxV x)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (hρ : ρ.findDef? "data" = none) (ha : f.module.datas[x.toNat]? = some a)
    (hd : s.datas[a]? = some di) (hb : di.bytes.data[i.toNat]? = some b) :
    EvalExp (simEnv20 B) ρ dataByteE (.num (.natN b.toNat)) := by
  have hidx : (bytesV di.bytes).idx? i.toNat = some (pctV b.toNat) := by
    rw [(bytesV_length20 di.bytes).1, byteArray_toList_eq]
    simp [Value.idx?, List.getElem?_map, Array.getElem?_toList, hb]
  exact evalExp_projE_iff.2 ⟨[.num (.natN b.toNat)], evalExp_uncaseE_iff.2
    (evalExp_idxE_iff.2 ⟨_, i.toNat, evalExp_dataBytes20 hρ fz fx ha hd, evalExp_iPay fi, hidx⟩),
    Int.le_refl 0, rfl⟩

theorem bwdRead_memoryInitSucc {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 46 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, hl, fz, hes, hr, hp⟩ := firesCfg_lhs20 hasRuleAt_memInitSucc hf
  obtain ⟨j, i, n, a₄, rfl, fj, fi, fn, h₄⟩ := const3_of_lhs hes
  obtain ⟨x, rfl⟩ := head20_memoryInit (head20_of_caseE h₄)
  have fx := idx_of_caseE (X := idxV x) h₄ rfl
  have hres : InstrResOk (⟨s, f⟩ : State H) (.memoryInit x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.2.1
  obtain ⟨am, mi, ham, hm⟩ := mem_of_isSome hres.1
  obtain ⟨ad, di, had, hd⟩ := data_of_isSome hres.2
  have hb := memInit_bound (by decide) hq hl fz fj fi fn fx ham hm had hd
    (else_of_prem (hp _ (List.mem_singleton_self _)))
  have h6 : ∃ u, EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) predE u := by
    obtain ⟨_, h₆⟩ := sixth_of_list hr
    exact constPE_inv h₆
  obtain ⟨u, hu⟩ := h6
  have hn1 : 1 ≤ n.toNat := (pred_inv fn hu).1
  have hn : n ≠ 0 := ne_zero_of_toNat hn1
  have hlt : i.toNat < di.bytes.data.size := by
    have h1 : di.bytes.size = di.bytes.data.size := rfl
    have := hb.1
    omega
  have hbyte : di.bytes.data[i.toNat]? = some di.bytes.data[i.toNat] :=
    Array.getElem?_eq_getElem hlt
  have ew : w = [.case "CONST" (.tuple [caseNilV "I32", pctV j.toNat]),
      .case "CONST" (.tuple [caseNilV "I32", pctV di.bytes.data[i.toNat].toNat]), adminToV store8,
      .case "CONST" (.tuple [caseNilV "I32", pctV (j.toNat + 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (i.toNat + 1)]),
      .case "CONST" (.tuple [caseNilV "I32", pctV (n.toNat - 1)]),
      .case "MEMORY.INIT" (idxV x)] :=
    Value.list.inj (EvalExp.unique hr (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_constVar fj)
      (evalExps_cons (evalExp_constPE (evalExp_dataByte20 fz fx fi rfl had hd hbyte))
      (evalExps_cons (evalExp_store8 rfl)
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_jPay fj) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_addNat20 (evalExp_iPay fi) (evalExp_numE_iff.2 rfl)))
      (evalExps_cons (evalExp_constPE (evalExp_pred hn1 fn))
      (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil)))))), rfl⟩))
  have hj1 : j.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  have hi1 : i.toNat + 1 < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew])
  exact ⟨_, ew.trans (adminsToV_memoryInitSucc j i n _ x hj1 hi1 hn).symm,
    .memoryInitSucc (mi := mi) (di := di) (by simp [State.mem?, ham, hm])
      (by simp [State.data?, ModuleInst.dataAddr?, Store.dataInst?, had, hd]) hb hn hbyte⟩

/-! ## What is left -/

/-- **What is left of `BwdRestW7`**: without `Step_read` 45, 46. Of `Step_read`, only the `-gt`
rules 18 and 43 remain. -/
structure BwdRestW8 (B : Builtins) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) : Prop where
  read : ∀ (i : Nat), i ∉ deadRead20 → i ∉ [7, 8] → i ∉ inertRead20 → i ∉ doneRead4 →
    i ∉ [11, 36] → i ∉ [13, 14, 38, 39] → i ∉ doneRead7 → i ∉ [45, 46] →
    ∀ (c : Config H) (w : List Value),
    GoodW c → TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 6 ≤ i → i ∉ inertStep20 → i ∉ doneStep4 → ∀ (c : Config H) (w : Value),
    GoodW c → Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- `BwdRestW7` from what is left. -/
theorem bwdRestW7_of_rest8 {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (R : BwdRestW8 B hn P host) : BwdRestW7 B hn P host where
  read i hd h78 hin hdn hsz hfl hd7 c w hg hc hw hf := by
    by_cases e45 : i = 45
    · subst e45; exact bwdRead_memoryInitZero hg hf
    by_cases e46 : i = 46
    · subst e46; exact bwdRead_memoryInitSucc hg hw hf
    exact R.read i hd h78 hin hdn hsz hfl hd7 (by simp [e45, e46]) c w hg hc hw hf
  step := R.step

/-- The `Step_read` rules a `BwdRestW8` still needs: only 18 and 43. -/
theorem read8_left {i : Nat} (hi : i < 47) (hd : i ∉ deadRead20) (h78 : i ∉ [7, 8])
    (hin : i ∉ inertRead20) (hdn : i ∉ doneRead4) (hsz : i ∉ [11, 36]) (hfl : i ∉ [13, 14, 38, 39])
    (hd7 : i ∉ doneRead7) (h45 : i ∉ [45, 46]) : i = 18 ∨ i = 43 := by
  simp only [deadRead20, inertRead20, doneRead4, doneRead7, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hd h78 hin hdn hsz hfl hd7 h45
  omega

/-- **`Task.wholeStepBwdW` from what is left after the `init` rules** (`BwdRestW8`). -/
theorem wholeStepBwdW_of_rest8
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
        BwdRestW8 (Sim.Floats.floatIntB (Silmaril.Wasm.Numerics.Profile.spec nd r)) hn
          (Silmaril.Wasm.Numerics.Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest7 fun H hn hinj host nd r => bwdRestW7_of_rest8 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole

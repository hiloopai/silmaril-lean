module

public import Silmaril.Wasm.SpecTec.Sim.Round4.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.RefOk.Thms
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms

/-!
# Round 5: `table.grow` and `memory.grow`, backward, under `ReadValid`

`Step` 15 (`table.grow-succeed`), 16 (`table.grow-fail`), 26 (`memory.grow-succeed`) and 27
(`memory.grow-fail`), at the concrete `B := Prims.builtins P hn host`, from a source satisfying
`ReadValid`.

* The fail rules have no premise. `ReadValid` resolves the grown index, so Core's `growFail`
  applies whenever the profile lets growth fail (r4-validity's `bwd_tableGrowFail` did this from
  `ConfigOk`; here it is redone from `ReadValid`, the premise `RemainingV.step` carries).
* The succeed rules test `ti = $growtable($table(z, x), n, ref)` (resp. `$growmem`). The table is
  resolved by `ReadValid`, `$growtable` is answered by `B` with the image of Core's
  `TableInst.grow?` (round 3's `RefOk.growtableCall_image`), so the bound `ti` is the image of a
  successful Core growth; the right-hand side is evaluated forward and compared by
  `EvalExp.unique`. The result `CONST at (% |table.REFS|)` is Core's
  `aconst at (ofNat |refs|)` because the store bounds keep the table below `2 ^ 32` entries
  (and the memory below `2 ^ 32` bytes).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.RuntimeBridge (tableInstToValue memInstToValue refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open BwdPureStep (fires_step codes_two codes_three payload_of_caseE head_of_caseE ref_of_var
  idx_of_var)
open Round4Int (BI)
open Round4Read (ReadValid idx_last table_of_isSome mem_of_isSome table_lt32 mem_lt32 mem_pages
  lt_width)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Decoding the `CONST at (% n)` operand -/

/-- **A `CONST at (% n)` element of a left-hand side**: an address-typed constant, with `at` and
`n` bound to its type and value. -/
theorem aconstN_of_lhs' {B : Builtins} {σ : List (IL.Id × Value)} {qs : List Param} {a : Admin}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP "at" (.varT "addrtype" []) ∈ qs)
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])])) (adminToV a)) :
    ∃ (at_ : AddrType) (b : BitVec at_.intType.width), a = aconst at_ b ∧
      (VarEnv.empty.bindVals σ).findVal? "at" = some (Encode.toValue at_) ∧
      (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN b.toNat)) := by
  obtain ⟨at_, b, rfl, fa⟩ := Round4.aconstN_of_lhs hq hm h
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  rw [State.adminToV_aconst] at he
  have eu : u = .tuple [Encode.toValue at_, State.idxV b.toNat] := (Value.case.inj he).2.symm
  subst eu
  have h₂ := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup hu)).2).1
  have h₃ := (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv h₂))).1
  exact ⟨at_, b, rfl, fa, evalExp_varE_iff.1 h₃⟩

/-! ## `$growtable` and `$growmem`, read back -/

/-- **`$growtable` at images, read back**: whatever `B`'s `$growtable` gives at the image of a
table instance, a count and a reference is the image of Core's successful `grow?`. -/
theorem growtable_inv {ti : TableInst} {n : Nat} {r : Ref} {v : Value}
    (h : Applies (simEnv (BI P hn host)) "growtable"
      [.val (tableInstToValue CT ti), .val (.num (.natN n)), .val (refToValue r)] v) :
    ∃ ti', ti.grow? n r = some ti' ∧ v = tableInstToValue CT ti' := by
  obtain ⟨ps, t, cs, hd, hu⟩ := RefOk.growtable_undef (RefOk.growDefs_simEnv (BI P hn host))
    (tableInstToValue CT ti) (.num (.natN n)) (refToValue r)
  obtain ⟨ps', t', cs', hd', hc⟩ := h
  rw [hd] at hd'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd'
  rcases hc with hc | ⟨-, hb⟩
  · exact absurd hu (fun h => Equiv.ExecNumeric.not_tryClauses_and_undef hc h)
  · rw [simEnv, Env.builtins_withBuiltins, RefOk.call_growtable, RefOk.growtableCall_image] at hb
    obtain ⟨ti', hg, he⟩ := Option.map_eq_some_iff.1 hb
    exact ⟨ti', hg, he.symm⟩

/-- **`$growmem` at images, read back.** -/
theorem growmem_inv {mi : MemInst} {n : Nat} {v : Value}
    (h : Applies (simEnv (BI P hn host)) "growmem"
      [.val (memInstToValue mi), .val (.num (.natN n))] v) :
    ∃ mi', mi.grow? n = some mi' ∧ v = memInstToValue mi' := by
  obtain ⟨ps, t, cs, hd, hu⟩ := RefOk.growmem_undef (RefOk.growDefs_simEnv (BI P hn host))
    (memInstToValue mi) (.num (.natN n))
  obtain ⟨ps', t', cs', hd', hc⟩ := h
  rw [hd] at hd'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd'
  rcases hc with hc | ⟨-, hb⟩
  · exact absurd hu (fun h => Equiv.ExecNumeric.not_tryClauses_and_undef hc h)
  · rw [simEnv, Env.builtins_withBuiltins, RefOk.call_growmem, RefOk.growmemCall_image] at hb
    obtain ⟨mi', hg, he⟩ := Option.map_eq_some_iff.1 hb
    exact ⟨mi', hg, he.symm⟩

/-! ## The fail rules, from `ReadValid` -/

/-- **`Step/table.grow-fail` (16) backward, under `ReadValid`.** -/
theorem bwd_tableGrowFail {B : Builtins} (hP : ∀ k a n d, P.growMayFail k a n d) {c : Config H}
    (hv : ReadValid c) {w : Value} (hf : Fires (simEnv B) "Step" 16 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).tableGrowFail hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨r, rfl, -⟩ := ref_of_var hq (.tail _ (.head _)) h₁
  obtain ⟨at_, b, rfl, fa⟩ := Round4.aconstN_of_lhs hq (.tail _ (.tail _ (.head _))) h₂
  obtain ⟨x, rfl⟩ := Round4.head_tableGrow (head_of_caseE h₃)
  obtain ⟨ta, ti, ht⟩ := table_of_isSome (idx_last (l := [_, _]) hv.idx)
  refine ⟨⟨s, f, [aconst at_ (BitVec.allOnes _)]⟩, Round4.growFail_rhs fz fa hr, ?_⟩
  exact .table (.growFail ht (.inl (hP _ _ _ _)))

/-- **`Step/memory.grow-fail` (27) backward, under `ReadValid`.** -/
theorem bwd_memoryGrowFail {B : Builtins} (hP : ∀ k a n d, P.growMayFail k a n d) {c : Config H}
    (hv : ReadValid c) {w : Value} (hf : Fires (simEnv B) "Step" 27 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).memoryGrowFail hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes_two hes
  obtain ⟨at_, b, rfl, fa⟩ := Round4.aconstN_of_lhs hq (.tail _ (.head _)) h₁
  obtain ⟨x, rfl⟩ := Round4.head_memoryGrow (head_of_caseE h₂)
  obtain ⟨ma, mi, hm⟩ := mem_of_isSome (idx_last (l := [_]) hv.idx)
  refine ⟨⟨s, f, [aconst at_ (BitVec.allOnes _)]⟩, Round4.growFail_rhs fz fa hr, ?_⟩
  exact .memory (.growFail hm (.inl (hP _ _ _ _)))

/-! ## The succeed rules -/

/-- `$with_tableinst(z, x, ti)` at a resolved table, evaluated forward. -/
theorem withTableinst_eval {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H}
    {f : Frame} {x : TableIdx} {ta : Nat} {ti ti' : TableInst}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (State.idxV x.toNat))
    (fti : ρ.findVal? "ti" = some (tableInstToValue CT ti'))
    (ht : s.table? f x = some (ta, ti)) :
    EvalExp (simEnv B) ρ
      (.callE "with_tableinst" [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "ti")])
      (stateV hn (s.setTable ta ti') f) := by
  obtain ⟨hta, hti⟩ := State.Store.table?_eq_some ht
  have hl : ta < s.tables.length := (List.getElem?_eq_some_iff.1 hti).1
  exact State.evalExp_call1 (Memory.withInstDefs_simEnv B).withTableinst
    (Prims.findDef_none_of_valsOnly hρ _)
    (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fx)
      (Equiv.evalArgs_cons (evalExp_var fti) Equiv.evalArgs_nil)))
    (Memory.matchArgs_zxyPat rfl)
    (Memory.evalExp_withInstBody (State.stateDefs_simEnv B) rfl rfl rfl rfl rfl
      (State.storeV_TABLES hn s) (State.frameV_MODULE f) (State.moduleV_TABLES _)
      (State.getElem?_map_natN hta) (by simpa using hl) (State.storeV_setTable hn s ta ti'))

/-- `$with_meminst(z, x, mi)` at a resolved memory, evaluated forward. -/
theorem withMeminst_eval {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H}
    {f : Frame} {x : MemIdx} {ma : Nat} {mi mi' : MemInst}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (State.idxV x.toNat))
    (fmi : ρ.findVal? "mi" = some (memInstToValue mi'))
    (hm : s.mem? f x = some (ma, mi)) :
    EvalExp (simEnv B) ρ
      (.callE "with_meminst" [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "mi")])
      (stateV hn (s.setMem ma mi') f) := by
  obtain ⟨hma, hmi⟩ := Memory.Store.mem?_eq_some hm
  have hl : ma < s.mems.length := (List.getElem?_eq_some_iff.1 hmi).1
  exact State.evalExp_call1 (Memory.withInstDefs_simEnv B).withMeminst
    (Prims.findDef_none_of_valsOnly hρ _)
    (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fx)
      (Equiv.evalArgs_cons (evalExp_var fmi) Equiv.evalArgs_nil)))
    (Memory.matchArgs_zxyPat rfl)
    (Memory.evalExp_withInstBody (State.stateDefs_simEnv B) rfl rfl rfl rfl rfl
      (State.storeV_MEMS hn s) (State.frameV_MODULE f) (State.moduleV_MEMS _)
      (State.getElem?_map_natN hma) (by simpa using hl) (by simp [storeV, Store.setMem,
        List.map_set]))

/-- **`Step/table.grow-succeed` (15) backward, under `ReadValid`**, in every profile in which
growth may succeed. -/
theorem bwd_tableGrowSucceed (hP : ∀ k a n d, P.growMaySucceed k a n d) {c : Config H}
    (hv : ReadValid c) {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step" 15 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv _).tableGrowSucceed hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨r, rfl, fr⟩ := ref_of_var hq (.tail _ (.head _)) h₁
  obtain ⟨at_, b, rfl, fa, fn⟩ := aconstN_of_lhs' hq (.tail _ (.tail _ (.head _))) h₂
  obtain ⟨x, rfl⟩ := Round4.head_tableGrow (head_of_caseE h₃)
  have fx := idx_of_var h₃ rfl
  have hρ := valsOnly_bindVals σ
  obtain ⟨ta, ti, ht⟩ := table_of_isSome (idx_last (l := [_, _]) hv.idx)
  have et : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) (tableInstToValue CT ti) :=
    State.evalExp_table_of (State.stateDefs_simEnv _) (Prims.findDef_none_of_valsOnly hρ _)
      (evalExp_var fz) (evalExp_var fx) (State.tableAt_of_table? hn ht)
  -- the premise `ti = $growtable($table(z, x), n, ref)`
  obtain ⟨TI, fTI, -⟩ := hq "ti" _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨v₂, e₁, e₂⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have eTI : TI = v₂ := EvalExp.unique (evalExp_var fTI) e₁
  have ha := Equiv.evalArgs_cons et (Equiv.evalArgs_cons (evalExp_var fn)
    (Equiv.evalArgs_cons (evalExp_var fr) Equiv.evalArgs_nil))
  obtain ⟨ti', hg, rfl⟩ := growtable_inv ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly hρ _) ha).2 (evalExp_callE_iff.1 e₂))
  subst eTI
  -- the right-hand side
  have hlt : ti.refs.length < 2 ^ at_.intType.width := lt_width (table_lt32 hv.store ht)
  have elen : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS"))
      (.num (.natN ti.refs.length)) := by
    simpa only [List.length_map] using RefsGC.evalExp_len (RefsGC.evalExp_dot et
      (State.tableInstV_REFS ti))
  refine ⟨⟨s.setTable ta ti', f, [aconst at_ (BitVec.ofNat _ ti.refs.length)]⟩, ?_,
    .table (.growSucceed ht hg (hP _ _ _ _))⟩
  refine EvalExp.unique hr ?_
  show EvalExp _ _ _ (cfgV _ [adminToV (aconst at_ (BitVec.ofNat _ ti.refs.length))])
  rw [State.adminToV_aconst, Memory.toNat_ofNat_of_lt hlt]
  exact evalExp_case (evalExp_tup2 (withTableinst_eval hρ fz fx fTI ht)
    (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons'
      (Memory.evalExp_constPct (Memory.evalExp_subAt fa) elen) RefsGC.evalExps_nil')))

/-- **`Step/memory.grow-succeed` (26) backward, under `ReadValid`**, in every profile in which
growth may succeed. -/
theorem bwd_memoryGrowSucceed (hP : ∀ k a n d, P.growMaySucceed k a n d) {c : Config H}
    (hv : ReadValid c) {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step" 26 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv _).memoryGrowSucceed hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes_two hes
  obtain ⟨at_, b, rfl, fa, fn⟩ := aconstN_of_lhs' hq (.tail _ (.head _)) h₁
  obtain ⟨x, rfl⟩ := Round4.head_memoryGrow (head_of_caseE h₂)
  have fx := idx_of_var h₂ rfl
  have hρ := valsOnly_bindVals σ
  obtain ⟨ma, mi, hm⟩ := mem_of_isSome (idx_last (l := [_]) hv.idx)
  have em : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) (memInstToValue mi) :=
    Memory.evalExp_mem_of (State.stateDefs_simEnv _) (evalExp_var fz) (evalExp_var fx)
      (Memory.memAt_of_mem? hn hm)
  obtain ⟨MI, fMI, -⟩ := hq "mi" _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨v₂, e₁, e₂⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have eMI : MI = v₂ := EvalExp.unique (evalExp_var fMI) e₁
  have ha := Equiv.evalArgs_cons em (Equiv.evalArgs_cons (evalExp_var fn) Equiv.evalArgs_nil)
  obtain ⟨mi', hg, rfl⟩ := growmem_inv ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly hρ _) ha).2 (evalExp_callE_iff.1 e₂))
  subst eMI
  have hpg := mem_pages hv.store hm
  have hlt : mi.pages < 2 ^ at_.intType.width := by
    have h32 := mem_lt32 hv.store hm
    refine lt_width (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h32)
  have hp' : (Memory.bytesL mi.bytes).length = mi.pages * 65536 := by
    rw [Memory.bytesL_length, MemInst.pages]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpg)).symm
  have elen : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES"))
      (.num (.natN (mi.pages * 65536))) :=
    hp' ▸ RefsGC.evalExp_len (RefsGC.evalExp_dot em (Memory.memInstV_BYTES mi))
  refine ⟨⟨s.setMem ma mi', f, [aconst at_ (BitVec.ofNat _ mi.pages)]⟩, ?_,
    .memory (.growSucceed hm hg (hP _ _ _ _))⟩
  refine EvalExp.unique hr ?_
  show EvalExp _ _ _ (cfgV _ [adminToV (aconst at_ (BitVec.ofNat _ mi.pages))])
  rw [State.adminToV_aconst, Memory.toNat_ofNat_of_lt hlt]
  exact evalExp_case (evalExp_tup2 (withMeminst_eval hρ fz fx fMI hm)
    (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons'
      (Memory.evalExp_constPct (Memory.evalExp_subAt fa) (Memory.evalExp_pages _ elen))
      RefsGC.evalExps_nil')))

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

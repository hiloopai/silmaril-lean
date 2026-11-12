module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeConstBound

/-!
# `table.size` and `memory.size` backwards, at any `GoodW` configuration

* `Step_read` 11 (`table.size`): `z; TABLE.SIZE x ~> CONST I32 (% n)` under
  `|$table(z, x).REFS| = n` (`bwdRead_tableSize`).
* `Step_read` 36 (`memory.size`): `z; MEMORY.SIZE ~> CONST I32 (% n)` under
  `n * 64 * $Ki = |$mem(z, 0).BYTES|` (`bwdRead_memorySize`).

V2's result is `i32.const (BitVec.ofNat 32 n)`. The count is below `2 ^ 32` because the result
`instr*` is IL-typed (`lt_of_typed_constI32`); V2's stores do not bound it. The table and the
memory exist by `ResOkL`. `$mem` and `$Ki` are evaluated forward (`evalExp_mem20`, `evalExp_ki20`),
and the length of the encoding of a byte string is its size (`bytesV_length20`).
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
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 evalExp_idxPayload HasClause1 idxPayload)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

theorem head20_tableSize {a : Admin} (h : adminHead20 a = "TABLE.SIZE") :
    ∃ x, a = .plain (.tableSize x) := by
  revert h; admin_head_inv20

theorem head20_memorySize {a : Admin} (h : adminHead20 a = "MEMORY.SIZE") :
    a = .plain .memorySize := by
  revert h; admin_head_inv20

/-! ## Byte strings, `$mem`, `$Ki` -/

theorem toList_loop_length (bs : ByteArray) :
    ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
      (ByteArray.toList.loop bs i r).length = r.length + (bs.size - i) := by
  intro k
  induction k with
  | zero =>
    intro i r hk
    rw [ByteArray.toList.loop]
    have : ¬ i < bs.size := by omega
    simp [this, hk]
  | succ k ih =>
    intro i r hk
    rw [ByteArray.toList.loop]
    have hi : i < bs.size := by omega
    simp only [hi, ↓reduceIte]
    rw [ih (i + 1) _ (by omega)]
    simp only [List.length_cons]
    omega

/-- The length of a byte string's list is its size. -/
theorem byteArray_toList_length (bs : ByteArray) : bs.toList.length = bs.size := by
  have := toList_loop_length bs bs.size 0 [] (by simp)
  simpa [ByteArray.toList] using this

/-- The encoding of a byte string has its size as length. -/
theorem bytesV_length20 (bs : ByteArray) : bytesV bs = .list (bs.toList.map fun x => pctV x.toNat) ∧
    (bs.toList.map fun x => pctV x.toNat).length = bs.size := by
  exact ⟨rfl, by simp [byteArray_toList_length]⟩

theorem hasClause_mem20 : HasClause1 (simEnv20 B) "mem" State.sfxPat
    (.idxE (.dotE (.varE "s") "MEMS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS")
      idxPayload)) := ⟨_, _, _, rfl⟩

theorem hasClause_ki20 : HasClause1 (simEnv20 B) "Ki" [] (.numE (.natN 1024)) := ⟨_, _, _, rfl⟩

/-- `$Ki = 1024`. -/
theorem evalExp_ki20 {ρ : VarEnv} (hρ : ρ.findDef? "Ki" = none) :
    EvalExp (simEnv20 B) ρ (.callE "Ki" []) (.num (.natN 1024)) :=
  evalExp_call1 (ρ₀ := VarEnv.empty) hasClause_ki20 hρ evalArgs_nil matchArgs_nil
    (evalExp_numE_iff.2 rfl)

/-- **`$mem(z, x)`**, at a module listing memory address `a` at `x` and a store holding a memory
there. -/
theorem evalExp_mem20 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : MemIdx}
    {a : Nat} {mi : MemInst} (hρ : ρ.findDef? "mem" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (ha : f.module.mems[x.toNat]? = some a) (hm : s.mems[a]? = some mi) :
    EvalExp (simEnv20 B) ρ (.callE "mem" [.expA ez, .expA ex]) (memInstV mi) :=
  evalExp_call1 hasClause_mem20 hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil))
    State.matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, a, evalExp_dotE_iff.2 ⟨storeV hn s,
      evalExp_var rfl, rfl⟩, evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2
        ⟨moduleInstV f.module, evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl,
          State.frameV_module f⟩, rfl⟩, evalExp_idxPayload rfl,
        by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
      by simp [Value.idx?, List.getElem?_map, hm]⟩)

/-- `$mem(z, %0)`, the literal memory index of the 2.0 rules. -/
abbrev mem0E : Exp := .callE "mem" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]

/-- `|$mem(z, 0).BYTES|`. -/
theorem evalExp_memLen20 {ρ : VarEnv} {s : Store H} {f : Frame} {a : Nat} {mi : MemInst}
    (hρ : ρ.findDef? "mem" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi) :
    EvalExp (simEnv20 B) ρ (.lenE (.dotE mem0E "BYTES")) (.num (.natN mi.bytes.size)) := by
  have hx : EvalExp (simEnv20 B) ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (idxV memIdx0) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)
  refine evalExp_lenE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨memInstV mi,
    evalExp_mem20 hρ (evalExp_var fz) hx ha hm, rfl⟩, ?_⟩
  rw [(bytesV_length20 mi.bytes).2]

/-! ## The rules, verbatim -/

/-- `CONST I32 (% n)` on the right-hand side. -/
abbrev constNRhs : Exp := .listE [constNE]

/-- `Step_read/table.size`, rule 11 of `Step_read` (verbatim). -/
def tableSizeRule : Rule :=
  .ruleD "table.size" [.expP "z" (.varT "state" []), .expP "x" (.varT "idx" []),
    .expP "n" (.varT "n" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "TABLE.SIZE" (.varE "x")]]), constNRhs])
    [.ifPr (.cmpE .eqOp .boolT tableLenE (.varE "n"))]

/-- `Step_read/memory.size`, rule 36 of `Step_read` (verbatim). -/
def memorySizeRule : Rule :=
  .ruleD "memory.size" [.expP "z" (.varT "state" []), .expP "n" (.varT "n" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "MEMORY.SIZE" (.tupE [])]]), constNRhs])
    [.ifPr (.cmpE .eqOp .boolT (.binE .mulOp (.numT .natT) (.binE .mulOp (.numT .natT) (.varE "n")
      (.numE (.natN 64))) (.callE "Ki" [])) (.lenE (.dotE mem0E "BYTES")))]

theorem hasRuleAt_tableSize : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 11 tableSizeRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_memorySize : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 36 memorySizeRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `CONST I32 (% n)` evaluated, at `n = k`. -/
theorem evalExp_constN {env : Env} {ρ : VarEnv} {k : Nat} (fn : ρ.findVal? "n" = some (.num (.natN k))) :
    EvalExp env ρ constNE (.case "CONST" (.tuple [caseNilV "I32", pctV k])) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var fn) evalExps_nil, rfl⟩)))

/-! ## The rules backwards -/

/-- **`Step_read/table.size` backwards**, at a `GoodW` configuration with a typed result. -/
theorem bwdRead_tableSize {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 11 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_tableSize hf
  obtain ⟨a₁, rfl, h₁⟩ := codes20_one hes
  obtain ⟨x, rfl⟩ := head20_tableSize (head20_of_caseE h₁)
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableSize x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2
  obtain ⟨a, ti, ha, ht⟩ := table_of_isSome hres
  have fx := idx_of_caseE (X := idxV x) h₁ rfl
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  have ev : v₂ = .num (.natN ti.refs.length) :=
    (cmpValues_eq_true_iff.1 hcmp).symm.trans (EvalExp.unique e₁ (evalExp_tableLen20 rfl fz fx ha ht))
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN ti.refs.length)) :=
    ev ▸ evalExp_varE_iff.1 e₂
  have ew : Value.list w = .list [.case "CONST" (.tuple [caseNilV "I32", pctV ti.refs.length])] :=
    EvalExp.unique hr (evalExp_list1 (evalExp_constN fn))
  have ew' := Value.list.inj ew
  have hlt : ti.refs.length < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew'])
  refine ⟨[constI32 (BitVec.ofNat 32 ti.refs.length)], ?_, .tableSize (ti := ti) (by
    simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, ha, ht]) ?_⟩
  · rw [ew']
    exact (congrArg (fun v => [v]) (adminToV_constI32_ofNat hlt)).symm
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- A product `k * 64 * 1024 = m` on numerals, read back. -/
theorem memSize_inv {env : Env} {ρ : VarEnv} {m : Nat} (hki : EvalExp env ρ (.callE "Ki" [])
    (.num (.natN 1024)))
    (h : EvalExp env ρ (.binE .mulOp (.numT .natT) (.binE .mulOp (.numT .natT) (.varE "n")
      (.numE (.natN 64))) (.callE "Ki" [])) (.num (.natN m))) :
    ∃ k, ρ.findVal? "n" = some (.num (.natN k)) ∧ k * 64 * 1024 = m := by
  obtain ⟨m₁, hm₁, hs₁ | ⟨-, m₂, hm₂, hb₁⟩⟩ := evalExp_binE_iff.1 h
  · simp [boolShort] at hs₁
  obtain ⟨m₃, hm₃, hs₂ | ⟨-, m₄, hm₄, hb₂⟩⟩ := evalExp_binE_iff.1 hm₁
  · simp [boolShort] at hs₂
  rw [EvalExp.unique hm₂ hki] at hb₁
  rw [EvalExp.unique hm₄ (evalExp_numE_iff.2 rfl)] at hb₂
  have fn := evalExp_varE_iff.1 hm₃
  cases m₃ with
  | num q =>
    cases q with
    | natN k =>
      simp only [binValues, Num.bin, Option.map_some, Res.ofOption] at hb₂
      obtain rfl := (Except.ok.inj hb₂).symm
      simp only [binValues, Num.bin, Option.map_some, Res.ofOption, Except.ok.injEq,
        Value.num.injEq, Num.natN.injEq] at hb₁
      exact ⟨k, fn, hb₁⟩
    | _ => simp [binValues, Num.bin, Res.ofOption] at hb₂
  | _ => simp [binValues] at hb₂

/-- **`Step_read/memory.size` backwards**, at a `GoodW` configuration with a typed result. -/
theorem bwdRead_memorySize {c : Config H} {w : List Value} (hg : GoodW c)
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w))
    (hf : Fires (simEnv20 B) "Step_read" 36 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_memorySize hf
  obtain ⟨a₁, rfl, h₁⟩ := codes20_one hes
  obtain rfl := head20_memorySize (head20_of_caseE h₁)
  have hres : InstrResOk (⟨s, f⟩ : State H) .memorySize := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2
  obtain ⟨a, mi, ha, hm⟩ := mem_of_isSome hres
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  have ev : v₁ = .num (.natN mi.bytes.size) :=
    (cmpValues_eq_true_iff.1 hcmp).trans (EvalExp.unique e₂ (evalExp_memLen20 rfl fz ha hm))
  obtain ⟨k, fn, hk⟩ := memSize_inv (evalExp_ki20 rfl) (ev ▸ e₁)
  have ew : Value.list w = .list [.case "CONST" (.tuple [caseNilV "I32", pctV k])] :=
    EvalExp.unique hr (evalExp_list1 (evalExp_constN fn))
  have ew' := Value.list.inj ew
  have hlt : k < 2 ^ 32 := lt_of_typed_constI32 hw (by simp [ew'])
  refine ⟨[constI32 (BitVec.ofNat 32 k)], ?_, .memorySize (mi := mi) (by
    simp [State.mem?, ha, hm]) ?_⟩
  · rw [ew']
    exact (congrArg (fun v => [v]) (adminToV_constI32_ofNat hlt)).symm
  · show (BitVec.ofNat 32 k).toNat * 65536 = mi.bytes.size
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, ← hk]
    omega

/-! ## What is left -/

/-- **What is left of `BwdRestW4`** after this module: `BwdRestW4` without `table.size` (11) and
`memory.size` (36). -/
structure BwdRestW5 (B : Builtins) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) : Prop where
  read : ∀ (i : Nat), i ∉ deadRead20 → i ∉ [7, 8] → i ∉ inertRead20 → i ∉ doneRead4 →
    i ∉ [11, 36] → ∀ (c : Config H) (w : List Value), GoodW c →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 6 ≤ i → i ∉ inertStep20 → i ∉ doneStep4 → ∀ (c : Config H) (w : Value),
    GoodW c → Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- `BwdRestW4` from what is left. -/
theorem bwdRestW4_of_rest5 {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    (R : BwdRestW5 B hn P host) : BwdRestW4 B hn P host where
  read i hd h78 hin hdn c w hg hc hw hf := by
    by_cases e11 : i = 11
    · subst e11; exact bwdRead_tableSize hg hw hf
    by_cases e36 : i = 36
    · subst e36; exact bwdRead_memorySize hg hw hf
    exact R.read i hd h78 hin hdn (by simp [e11, e36]) c w hg hc hw hf
  step := R.step

/-- **`Task.wholeStepBwdW` from what is left after this module** (`BwdRestW5`). -/
theorem wholeStepBwdW_of_rest5
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
        BwdRestW5 (Sim.Floats.floatIntB (Silmaril.Wasm.Numerics.Profile.spec nd r)) hn
          (Silmaril.Wasm.Numerics.Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest4 fun H hn hinj host nd r => bwdRestW4_of_rest5 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole

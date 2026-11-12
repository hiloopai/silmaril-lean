module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Inert
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestStoreTrap

/-!
# The 1.0 load and store trap rules, backwards

`Step_read` 8 (`load-num-trap`), 10 (`load-pack-trap`) and `Step` 7 (`store-num-trap`), 9
(`store-pack-trap`) of the wasm-1.0 script trap under `i + ao.OFFSET + w/8 > |$mem(z, 0).BYTES|`,
where `w` is `$size(t)` or the pack width `n`. The premise is 2.0's (`Sim20.Whole.storeTrapPrem`,
whose evaluation lemmas `evalExp_div8`, `evalExp_addNat20`, `evalExp_iPay`, `cmp_of_prem` are
environment-generic). What is 1.0's:

* the rules themselves (transcribed, kernel `rfl` at the 1.0 indices): 1.0's `LOAD` carries
  `loadop_(valtype)?` with the pack `n _ sx`, and its values are `CONST valtype val_(valtype)`;
* `$mem(z, 0)` and `$size(t)` at the 1.0 encoding (`evalExp_memLen10`, `evalExp_size10`);
* V1's side: out of bounds, `loadInt`, `loadFloat`, `storeInt` and `storeFloat` answer `none`
  (`loadInt_none`, …), which is the premise of V1's `intLoadTrap`, `floatLoadTrap`,
  `intStoreTrap` and `floatStoreTrap`.

The memory exists by `ResOkL10`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress loadInt loadFloat storeInt storeFloat)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (natV evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.State (HasClause1 idxPayload evalExp_call1 evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.Whole (div8E addrE storeTrapPrem trapRhs evalExp_trapRhs zTrapRhs
  constIE mem0E memLenE evalExp_div8 evalExp_addNat20 evalExp_iPay cmp_of_prem tup_of_caseE
  var_fst var_snd snd_of3 thd_of3 numTypeV_inj width_cases byteArray_toList_length)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## `$mem(z, 0)` and `$size(t)` at the 1.0 encoding -/

theorem hasClause_mem10 : HasClause1 (simEnv10 B) "mem" Sim20.State.sfxPat
    (.idxE (.dotE (.varE "s") "MEMS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS")
      idxPayload)) := ⟨_, _, _, rfl⟩

/-- The memory of a frame, unfolded. -/
theorem frameMemory_some {s : Store H} {f : Frame} {a : Execution.Runtime.MemAddr} {m : MemInst}
    (h : frameMemory s f = some (a, m)) :
    f.module.memories[0]? = some a ∧ s.memories[a.value]? = some m := by
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', ha', m', hm', rfl, rfl⟩ := h
  exact ⟨ha', hm'⟩

/-- **`|$mem(z, 0).BYTES|`** at the 1.0 encoding: the size of the frame's memory. -/
theorem evalExp_memLen10 {ρ : VarEnv} {s : Store H} {f : Frame} {a : Execution.Runtime.MemAddr}
    {m : MemInst} (hρ : ρ.findDef? "mem" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (hm : frameMemory s f = some (a, m)) :
    EvalExp (simEnv10 B) ρ memLenE (.num (.natN m.data.size)) := by
  obtain ⟨ha, hs⟩ := frameMemory_some hm
  have hx : EvalExp (simEnv10 B) ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (pctV 0) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)
  have hmem : EvalExp (simEnv10 B) ρ mem0E (memInstV m) :=
    evalExp_call1 hasClause_mem10 hρ (evalArgs_cons (evalExp_var fz) (evalArgs_cons hx evalArgs_nil))
      Sim20.State.matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, a.value, evalExp_dotE_iff.2 ⟨storeV hn s,
        evalExp_var rfl, rfl⟩, evalExp_idxE_iff.2 ⟨_, 0, evalExp_dotE_iff.2
          ⟨moduleInstV f.module, evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, rfl⟩, rfl⟩,
          evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
        by simp [Value.idx?, List.getElem?_map, hs]⟩)
  refine evalExp_lenE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨memInstV m, hmem, rfl⟩, ?_⟩
  simp [byteArray_toList_length]

theorem findDef_size10 : ∃ ps t cs, (simEnv10 B).findDef? "size" = some (ps, t, cs) ∧
    cs = [.defD [] [.expA (.caseE "I32" (.tupE []))] (.numE (.natN 32)) [],
      .defD [] [.expA (.caseE "I64" (.tupE []))] (.numE (.natN 64)) [],
      .defD [] [.expA (.caseE "F32" (.tupE []))] (.numE (.natN 32)) [],
      .defD [] [.expA (.caseE "F64" (.tupE []))] (.numE (.natN 64)) []] :=
  ⟨_, _, _, rfl, rfl⟩

/-- **`$size(t)`** is the width, at every 1.0 value type. -/
theorem evalExp_size10 (t : V1.ValType) {ρ : VarEnv} {e : Exp} (hρ : ρ.findDef? "size" = none)
    (he : EvalExp (simEnv10 B) ρ e (valTypeV t)) :
    EvalExp (simEnv10 B) ρ (.callE "size" [.expA e]) (.num (.natN t.width)) := by
  obtain ⟨ps, ty, cs, hd, rfl⟩ := findDef_size10 (B := B)
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd (evalArgs_cons he evalArgs_nil) ?_)
  rcases t with (_ | _) | (_ | _) <;>
  · repeat (refine tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (matchExp_caseE_undef (by decide)))) ?_)
    exact tryClauses_hit (ρ₀ := VarEnv.empty)
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
      premsHold_nil evalExp_num

/-! ## The premise, read back -/

/-- `ao.OFFSET.%.0` at a 1.0 memarg. -/
theorem evalExp_off10 {env : Env} {ρ : VarEnv} {a : V1.MemArg}
    (h : ρ.findVal? "ao" = some (memargV a)) :
    EvalExp env ρ Sim20.Whole.offE (.num (.natN a.offset.val)) :=
  evalExp_projE_iff.2 ⟨[.num (.natN a.offset.val)], evalExp_uncaseE_iff.2
    (evalExp_dotE_iff.2 ⟨_, evalExp_var h, rfl⟩), Int.le_refl 0, rfl⟩

/-- **The trap premise, read back** at the 1.0 encoding. -/
theorem trap_of_prem10 {σ : List (IL.Id × Value)} {e : Exp} {s : Store H} {f : Frame}
    {i : BitVec 32} {ao : V1.MemArg} {w : Nat} {a : Execution.Runtime.MemAddr} {m : MemInst}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao))
    (he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) e (.num (.natN w)))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (hm : frameMemory s f = some (a, m))
    (hp : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.cmpE .gtOp (.numT .natT) (addrE (div8E e)) memLenE) (.bool true)) :
    m.data.size < effectiveAddress i ao + w / 8 := by
  have h := cmp_of_prem hp (evalExp_addNat20 (evalExp_addNat20 (evalExp_iPay fi)
    (evalExp_off10 fa)) (evalExp_div8 he hw)) (evalExp_memLen10 rfl fz hm)
  have h' : m.data.size < i.toNat + ao.offset.val + w / 8 := by
    simpa [cmpValues, Num.cmp, Res.ofOption] using h
  exact h'

/-! ## V1 out of bounds -/

theorem loadInt_none {t : IntType} {p : Option (V1.PackSize × Signedness)} {m : Execution.Memory.Bytes}
    {start : Nat} (h : m.size < start + ((p.map (·.1.width)).getD t.width) / 8) :
    loadInt t p m start = none := by
  rcases p with _ | ⟨q, sx⟩
  · have : ¬ start + t.width / 8 ≤ m.size := by simp at h; omega
    simp [loadInt, Execution.Memory.load, Execution.Memory.readBytes, this]
  · have : ¬ start + q.width / 8 ≤ m.size := by simp at h; omega
    simp [loadInt, Execution.Memory.load, Execution.Memory.readBytes, this]

theorem loadFloat_none {t : FloatType} {m : Execution.Memory.Bytes} {start : Nat}
    (h : m.size < start + t.width / 8) : loadFloat t m start = none := by
  have : ¬ start + t.width / 8 ≤ m.size := by omega
  simp [loadFloat, Execution.Memory.load, Execution.Memory.readBytes, this]

theorem storeInt_none {t : IntType} {p : Option V1.PackSize} {m : Execution.Memory.Bytes} {start : Nat}
    {x : BitVec t.width} (h : m.size < start + ((p.map V1.PackSize.width).getD t.width) / 8) :
    storeInt t p m start x = none := by
  have : ¬ start + ((p.map V1.PackSize.width).getD t.width) / 8 ≤ m.size := by omega
  simp only [storeInt, Execution.Memory.store, Execution.Memory.writeBytes, Execution.Memory.encodeLE_size]
  simp [this]

theorem storeFloat_none {t : FloatType} {m : Execution.Memory.Bytes} {start : Nat} {x : BitVec t.width}
    (h : m.size < start + t.width / 8) : storeFloat t m start x = none := by
  have : ¬ start + t.width / 8 ≤ m.size := by omega
  simp only [storeFloat, Execution.Memory.store, Execution.Memory.writeBytes, Execution.Memory.encodeLE_size]
  simp [this]

/-! ## The rules, transcribed -/

/-- `Inn <: valtype`. -/
abbrev innE10 : Exp := .subE (.varE "Inn") (.varT "Inn" []) (.varT "valtype" [])

/-- `val_(I32)`. -/
abbrev valI32T' : Typ := .varT "val_" [.expA (.caseE "I32" (.tupE []))]

/-- `$size(t)`. -/
abbrev sizeTE : Exp := .callE "size" [.expA (.varE "t")]

/-- `Step_read/load-num-trap` of 1.0. -/
def loadNumTrapRule10 : Rule :=
  .ruleD "load-num-trap" [.expP "z" (.varT "state" []), .expP "i" valI32T',
    .expP "t" (.varT "valtype" []), .expP "ao" (.varT "memarg" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "LOAD" (.tupE [.varE "t", .optE none, .varE "ao"])]]), trapRhs])
    [storeTrapPrem sizeTE]

/-- `Step_read/load-pack-trap` of 1.0. -/
def loadPackTrapRule10 : Rule :=
  .ruleD "load-pack-trap" [.expP "z" (.varT "state" []), .expP "i" valI32T',
    .expP "Inn" (.varT "Inn" []), .expP "n" (.varT "n" []), .expP "sx" (.varT "sx" []),
    .expP "ao" (.varT "memarg" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "LOAD" (.tupE [innE10, .optE (some (.caseE "%_%" (.tupE [.caseE "%" (.tupE
        [.varE "n"]), .varE "sx"]))), .varE "ao"])]]), trapRhs])
    [storeTrapPrem (.varE "n")]

/-- `Step/store-num-trap` of 1.0. -/
def storeNumTrapRule10 : Rule :=
  .ruleD "store-num-trap" [.expP "z" (.varT "state" []), .expP "i" valI32T',
    .expP "t" (.varT "valtype" []), .expP "c" (.varT "val_" [.expA (.varE "t")]),
    .expP "ao" (.varT "memarg" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "CONST" (.tupE [.varE "t", .varE "c"]),
      .caseE "STORE" (.tupE [.varE "t", .optE none, .varE "ao"])]]), zTrapRhs])
    [storeTrapPrem sizeTE]

/-- `Step/store-pack-trap` of 1.0. -/
def storePackTrapRule10 : Rule :=
  .ruleD "store-pack-trap" [.expP "z" (.varT "state" []), .expP "i" valI32T',
    .expP "Inn" (.varT "Inn" []), .expP "c" (.varT "val_" [.expA innE10]),
    .expP "n" (.varT "n" []), .expP "ao" (.varT "memarg" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "CONST" (.tupE [innE10, .varE "c"]),
      .caseE "STORE" (.tupE [innE10, .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"])]]),
      zTrapRhs])
    [storeTrapPrem (.varE "n")]

variable (B) in
theorem hasRuleAt10_loadNumTrap : HasRuleAt (simEnv10 B) "Step_read" "%~>%" 8 loadNumTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable (B) in
theorem hasRuleAt10_loadPackTrap :
    HasRuleAt (simEnv10 B) "Step_read" "%~>%" 10 loadPackTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable (B) in
theorem hasRuleAt10_storeNumTrap : HasRuleAt (simEnv10 B) "Step" "%~>%" 7 storeNumTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

variable (B) in
theorem hasRuleAt10_storePackTrap : HasRuleAt (simEnv10 B) "Step" "%~>%" 9 storePackTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Decoding the left-hand sides -/

/-- The payload of a tuple-headed left-hand side element. -/
theorem tup_of_caseE10 {env : Env} {ρ : VarEnv} {op : MixopS} {es : List Exp} {a : Admin}
    {us : List Value} (h : EvalExp env ρ (.caseE op (.tupE es)) (adminToV a))
    (ha : adminToV a = .case op (.tuple us)) : EvalExps env ρ es us := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  have e : u = .tuple us := (Value.case.inj (he.symm.trans ha)).2
  subst e
  exact Sim.RefsGC.elems_of_tup hu

/-- The payload of a tuple-headed pattern, at a known value. -/
theorem tup_of_caseV {env : Env} {ρ : VarEnv} {op : MixopS} {es : List Exp} {us : List Value}
    (h : EvalExp env ρ (.caseE op (.tupE es)) (.case op (.tuple us))) : EvalExps env ρ es us := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  have e : u = .tuple us := (Value.case.inj he).2.symm
  subst e
  exact Sim.RefsGC.elems_of_tup hu

theorem head10_load {a : Admin} (h : adminHead10 a = "LOAD") :
    (∃ t p ao, a = .source (.intLoad t p ao)) ∨ (∃ t ao, a = .source (.floatLoad t ao)) := by
  revert h
  cases a with
  | source i => cases i <;> simp [adminHead10, instrHead10]
  | _ => simp [adminHead10]

theorem head10_store {a : Admin} (h : adminHead10 a = "STORE") :
    (∃ t p ao, a = .source (.intStore t p ao)) ∨ (∃ t ao, a = .source (.floatStore t ao)) := by
  revert h
  cases a with
  | source i => cases i <;> simp [adminHead10, instrHead10]
  | _ => simp [adminHead10]

/-- A `CONST t c` operand of a left-hand side is a V1 value, and `t` is bound to its type. -/
theorem const_tc10 {ρ : VarEnv} {e : Exp} {a : Admin}
    (h : EvalExp (simEnv10 B) ρ (.caseE "CONST" (.tupE [e, .varE "c"])) (adminToV a)) :
    ∃ v : Execution.Runtime.Value, a = value v ∧ EvalExp (simEnv10 B) ρ e (valTypeV v.type) := by
  obtain ⟨u, -, hcu⟩ := evalExp_caseE_iff.1 h
  obtain ⟨v, rfl⟩ := admin_of_const10 hcu
  have hs := tup_of_caseE10 h (us := [valTypeV v.type, numV v]) (by rw [adminToV_value]; rfl)
  obtain ⟨w, ws, hw, -, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hs
  obtain ⟨rfl, -⟩ := List.cons.inj he
  exact ⟨v, rfl, hw⟩

/-- The first component `Inn <: valtype`, read back as the variable. -/
theorem inn_of_eval10 {ρ : VarEnv} {u : Value} (h : EvalExp (simEnv10 B) ρ innE10 u) :
    ρ.findVal? "Inn" = some u :=
  evalExp_varE_iff.1 (evalExp_subE_iff.1 h)

/-- The first component of a three-element payload. -/
theorem fst_of3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h : EvalExps env ρ [e₁, e₂, e₃] [v₁, v₂, v₃]) : EvalExp env ρ e₁ v₁ := by
  obtain ⟨w₁, ws, hw, -, he₁⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  obtain ⟨rfl, -⟩ := List.cons.inj he₁
  exact hw

/-- The pattern `% n`, read back at a pack width. -/
theorem width_of_pctN {ρ : VarEnv} {sz : V1.PackSize}
    (h : EvalExp (simEnv10 B) ρ (.caseE "%" (.tupE [.varE "n"])) (szV sz)) :
    ρ.findVal? "n" = some (.num (.natN sz.width)) := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  have eu : u = .tuple [.num (.natN sz.width)] := by
    simp only [szV, pctV, Value.case.injEq] at hcu
    exact hcu.2.symm
  exact var_fst (Sim.RefsGC.elems_of_tup (eu ▸ hu))

theorem packWidth10_cases (sz : V1.PackSize) :
    sz.width = 8 ∨ sz.width = 16 ∨ sz.width = 32 ∨ sz.width = 64 ∨ sz.width = 128 := by
  cases sz <;> simp [V1.PackSize.width]

/-- The memory of a `GoodV1` configuration whose last instruction names it (of two). -/
theorem mem_of_good2 {s : Store H} {f : Frame} {a₁ : Admin} {i : V1.Instr}
    (hg : GoodV1 (⟨s, f, [a₁, .source i]⟩ : Config H))
    (hi : InstrResOk10 s f i → (frameMemory s f).isSome) :
    ∃ a m, frameMemory s f = some (a, m) := by
  have h : InstrResOk10 s f i := hg.1.2.1
  obtain ⟨⟨a, m⟩, hm⟩ := Option.isSome_iff_exists.1 (hi h)
  exact ⟨a, m, hm⟩

/-- The memory of a `GoodV1` configuration whose last instruction names it (of three). -/
theorem mem_of_good3 {s : Store H} {f : Frame} {a₁ a₂ : Admin} {i : V1.Instr}
    (hg : GoodV1 (⟨s, f, [a₁, a₂, .source i]⟩ : Config H))
    (hi : InstrResOk10 s f i → (frameMemory s f).isSome) :
    ∃ a m, frameMemory s f = some (a, m) := by
  have h : InstrResOk10 s f i := hg.1.2.2.1
  obtain ⟨⟨a, m⟩, hm⟩ := Option.isSome_iff_exists.1 (hi h)
  exact ⟨a, m, hm⟩

/-- `z; TRAP` at the 1.0 encoding. -/
theorem evalExp_zTrap10 {ρ : VarEnv} {s : Store H} {f : Frame}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) :
    EvalExp (simEnv10 B) ρ zTrapRhs (configV hn ⟨s, f, [.trap]⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var fz) evalExp_trapRhs)

/-! ## The V1 trap steps, from the bound -/

/-- An `i32` address operand. -/
abbrev addr32 (i : BitVec 32) : Admin := value ⟨.int .i32, i⟩

theorem step_intLoadTrap {host : HostSemantics H} {s : Store H} {f : Frame} {i : BitVec 32}
    {t : IntType} {p : Option (V1.PackSize × Signedness)} {ao : V1.MemArg}
    {a : Execution.Runtime.MemAddr} {m : MemInst} (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress i ao + ((p.map (·.1.width)).getD t.width) / 8) :
    Step host ⟨s, f, [addr32 i, .source (.intLoad t p ao)]⟩ ⟨s, f, [.trap]⟩ :=
  .intLoadTrap s f t p ao i a m hm (loadInt_none hlt)

theorem step_floatLoadTrap {host : HostSemantics H} {s : Store H} {f : Frame} {i : BitVec 32}
    {t : FloatType} {ao : V1.MemArg} {a : Execution.Runtime.MemAddr} {m : MemInst}
    (hm : frameMemory s f = some (a, m)) (hlt : m.data.size < effectiveAddress i ao + t.width / 8) :
    Step host ⟨s, f, [addr32 i, .source (.floatLoad t ao)]⟩ ⟨s, f, [.trap]⟩ :=
  .floatLoadTrap s f t ao i a m hm (loadFloat_none hlt)

theorem step_intStoreTrap {host : HostSemantics H} {s : Store H} {f : Frame} {i : BitVec 32}
    {t : IntType} {x : BitVec t.width} {p : Option V1.PackSize} {ao : V1.MemArg}
    {a : Execution.Runtime.MemAddr} {m : MemInst} (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress i ao + ((p.map V1.PackSize.width).getD t.width) / 8) :
    Step host ⟨s, f, [addr32 i, value ⟨.int t, x⟩, .source (.intStore t p ao)]⟩ ⟨s, f, [.trap]⟩ :=
  .intStoreTrap s f t p ao i x a m hm (storeInt_none hlt)

theorem step_floatStoreTrap {host : HostSemantics H} {s : Store H} {f : Frame} {i : BitVec 32}
    {t : FloatType} {x : BitVec t.width} {ao : V1.MemArg} {a : Execution.Runtime.MemAddr}
    {m : MemInst} (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress i ao + t.width / 8) :
    Step host ⟨s, f, [addr32 i, value ⟨.float t, x⟩, .source (.floatStore t ao)]⟩ ⟨s, f, [.trap]⟩ :=
  .floatStoreTrap s f t ao i x a m hm (storeFloat_none hlt)

/-! ## The `LOAD` and `STORE` operands, read back -/

/-- `LOAD t ε ao`, read back. -/
theorem loadNum_decode {ρ : VarEnv} {a : Admin}
    (h : EvalExp (simEnv10 B) ρ (.caseE "LOAD" (.tupE [.varE "t", .optE none, .varE "ao"]))
      (adminToV a)) :
    ∃ (t : V1.ValType) (ao : V1.MemArg), ρ.findVal? "t" = some (valTypeV t) ∧
      ρ.findVal? "ao" = some (memargV ao) ∧
      ((∃ t', t = .int t' ∧ a = .source (.intLoad t' none ao)) ∨
        (∃ t', t = .float t' ∧ a = .source (.floatLoad t' ao))) := by
  rcases head10_load (head10_of_caseE h) with ⟨t, p, ao, rfl⟩ | ⟨t, ao, rfl⟩
  · have hs := tup_of_caseE10 h (us := [valTypeV (.int t),
      .opt (p.map fun q => .case "%_%" (.tuple [szV q.1, Sim20.sxV q.2])), memargV ao]) rfl
    have hp0 : p = none := by
      have h' := evalExp_optE_none_iff.1 (snd_of3 hs)
      cases p <;> simp_all
    exact ⟨.int t, ao, evalExp_varE_iff.1 (fst_of3 hs), thd_of3 hs, .inl ⟨t, rfl, by rw [hp0]⟩⟩
  · have hs := tup_of_caseE10 h (us := [valTypeV (.float t), .opt none, memargV ao]) rfl
    exact ⟨.float t, ao, evalExp_varE_iff.1 (fst_of3 hs), thd_of3 hs, .inr ⟨t, rfl, rfl⟩⟩

/-- `LOAD Inn (n _ sx) ao`, read back. -/
theorem loadPack_decode {ρ : VarEnv} {a : Admin}
    (h : EvalExp (simEnv10 B) ρ (.caseE "LOAD" (.tupE [innE10, .optE (some (.caseE "%_%" (.tupE
      [.caseE "%" (.tupE [.varE "n"]), .varE "sx"]))), .varE "ao"])) (adminToV a)) :
    ∃ t sz sx ao, a = .source (.intLoad t (some (sz, sx)) ao) ∧
      ρ.findVal? "ao" = some (memargV ao) ∧ ρ.findVal? "n" = some (.num (.natN sz.width)) := by
  rcases head10_load (head10_of_caseE h) with ⟨t, p, ao, rfl⟩ | ⟨t, ao, rfl⟩
  · have hs := tup_of_caseE10 h (us := [valTypeV (.int t),
      .opt (p.map fun q => .case "%_%" (.tuple [szV q.1, Sim20.sxV q.2])), memargV ao]) rfl
    obtain ⟨u, hu, hpu⟩ := evalExp_optE_some_iff.1 (snd_of3 hs)
    obtain ⟨sz, sx, rfl, rfl⟩ : ∃ sz sx, p = some (sz, sx) ∧
        u = .case "%_%" (.tuple [szV sz, Sim20.sxV sx]) := by
      rcases p with _ | ⟨sz, sx⟩
      · simp at hpu
      · exact ⟨sz, sx, rfl, by simpa using hpu.symm⟩
    obtain ⟨w₁, us₁, hn₁, -, he₁⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 (tup_of_caseV hu)
    have ew₁ : w₁ = szV sz := (List.cons.inj he₁).1.symm
    exact ⟨t, sz, sx, ao, rfl, thd_of3 hs, width_of_pctN (ew₁ ▸ hn₁)⟩
  · have hs := tup_of_caseE10 h (us := [valTypeV (.float t), .opt none, memargV ao]) rfl
    obtain ⟨u, -, hpu⟩ := evalExp_optE_some_iff.1 (snd_of3 hs)
    simp at hpu

/-- `STORE t ε ao`, after a value of type `ty`, read back. -/
theorem storeNum_decode {ρ : VarEnv} {a : Admin} {ty : V1.ValType}
    (ft : ρ.findVal? "t" = some (valTypeV ty))
    (h : EvalExp (simEnv10 B) ρ (.caseE "STORE" (.tupE [.varE "t", .optE none, .varE "ao"]))
      (adminToV a)) :
    ∃ ao : V1.MemArg, ρ.findVal? "ao" = some (memargV ao) ∧
      ((∃ t', ty = .int t' ∧ a = .source (.intStore t' none ao)) ∨
        (∃ t', ty = .float t' ∧ a = .source (.floatStore t' ao))) := by
  rcases head10_store (head10_of_caseE h) with ⟨t, p, ao, rfl⟩ | ⟨t, ao, rfl⟩
  · have hs := tup_of_caseE10 h (us := [valTypeV (.int t), .opt (p.map szV), memargV ao]) rfl
    have et : ty = .int t :=
      numTypeV_inj (Option.some.inj (ft.symm.trans (evalExp_varE_iff.1 (fst_of3 hs))))
    have hp0 : p = none := by
      have h' := evalExp_optE_none_iff.1 (snd_of3 hs)
      cases p <;> simp_all
    exact ⟨ao, thd_of3 hs, .inl ⟨t, et, by rw [hp0]⟩⟩
  · have hs := tup_of_caseE10 h (us := [valTypeV (.float t), .opt none, memargV ao]) rfl
    have et : ty = .float t :=
      numTypeV_inj (Option.some.inj (ft.symm.trans (evalExp_varE_iff.1 (fst_of3 hs))))
    exact ⟨ao, thd_of3 hs, .inr ⟨t, et, rfl⟩⟩

/-- `STORE Inn (% n) ao`, after a value whose type `Inn` is bound to, read back. -/
theorem storePack_decode {ρ : VarEnv} {a : Admin} {ty : V1.ValType}
    (fInn : ρ.findVal? "Inn" = some (valTypeV ty))
    (h : EvalExp (simEnv10 B) ρ (.caseE "STORE" (.tupE [innE10,
      .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"])) (adminToV a)) :
    ∃ t sz ao, ty = .int t ∧ a = .source (.intStore t (some sz) ao) ∧
      ρ.findVal? "ao" = some (memargV ao) ∧ ρ.findVal? "n" = some (.num (.natN sz.width)) := by
  rcases head10_store (head10_of_caseE h) with ⟨t, p, ao, rfl⟩ | ⟨t, ao, rfl⟩
  · have hs := tup_of_caseE10 h (us := [valTypeV (.int t), .opt (p.map szV), memargV ao]) rfl
    have et : ty = .int t :=
      numTypeV_inj (Option.some.inj (fInn.symm.trans (inn_of_eval10 (fst_of3 hs))))
    obtain ⟨u, hu, hpu⟩ := evalExp_optE_some_iff.1 (snd_of3 hs)
    obtain ⟨sz, rfl, rfl⟩ : ∃ sz, p = some sz ∧ u = szV sz := by
      cases p with
      | none => simp at hpu
      | some sz => exact ⟨sz, rfl, by simpa using hpu.symm⟩
    exact ⟨t, sz, ao, et, rfl, thd_of3 hs, width_of_pctN hu⟩
  · have hs := tup_of_caseE10 h (us := [valTypeV (.float t), .opt none, memargV ao]) rfl
    obtain ⟨u, -, hpu⟩ := evalExp_optE_some_iff.1 (snd_of3 hs)
    simp at hpu

/-! ## The rules backwards -/

/-- **`Step_read/load-num-trap` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_loadNumTrap {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10 B) "Step_read" 8 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_loadNumTrap B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨t, ao, ft, fa, hd⟩ := loadNum_decode h₂
  have ew : w = adminsToV [.trap] := Value.list.inj (EvalExp.unique hrh evalExp_trapRhs)
  have hlt : ∀ a m, frameMemory s f = some (a, m) →
      m.data.size < effectiveAddress i ao + t.width / 8 := fun a m hm =>
    trap_of_prem10 fz (evalExp_varE_iff.1 fi) fa (evalExp_size10 t rfl (evalExp_var ft))
      (width_cases t) hm (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  rcases hd with ⟨t', rfl, rfl⟩ | ⟨t', rfl, rfl⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
    exact ⟨_, ew, step_intLoadTrap hm (hlt a m hm)⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
    exact ⟨_, ew, step_floatLoadTrap hm (hlt a m hm)⟩

/-- **`Step_read/load-pack-trap` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_loadPackTrap {host : HostSemantics H} {c : Config H} {w : List Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10 B) "Step_read" 10 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_loadPackTrap B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨t, sz, sx, ao, rfl, fa, fn⟩ := loadPack_decode h₂
  have ew : w = adminsToV [.trap] := Value.list.inj (EvalExp.unique hrh evalExp_trapRhs)
  obtain ⟨a, m, hm⟩ := mem_of_good2 hg (fun h => h)
  have hlt : m.data.size < effectiveAddress i ao + sz.width / 8 :=
    trap_of_prem10 fz (evalExp_varE_iff.1 fi) fa (evalExp_var fn) (packWidth10_cases sz) hm
      (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨_, ew, step_intLoadTrap hm hlt⟩

/-- **`Step/store-num-trap` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_storeNumTrap {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10 B) "Step" 7 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_storeNumTrap B) hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes10_three hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨⟨ty, x⟩, rfl, hty⟩ := const_tc10 h₂
  obtain ⟨ao, fa, hd⟩ := storeNum_decode (evalExp_varE_iff.1 hty) h₃
  have ew : w = configV hn ⟨s, f, [.trap]⟩ := EvalExp.unique hrh (evalExp_zTrap10 fz)
  have hlt : ∀ a m, frameMemory s f = some (a, m) →
      m.data.size < effectiveAddress i ao + ty.width / 8 := fun a m hm =>
    trap_of_prem10 fz (evalExp_varE_iff.1 fi) fa (evalExp_size10 ty rfl hty)
      (width_cases ty) hm (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  rcases hd with ⟨t', rfl, rfl⟩ | ⟨t', rfl, rfl⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good3 hg (fun h => h)
    exact ⟨_, ew, step_intStoreTrap hm (hlt a m hm)⟩
  · obtain ⟨a, m, hm⟩ := mem_of_good3 hg (fun h => h)
    exact ⟨_, ew, step_floatStoreTrap hm (hlt a m hm)⟩

/-- **`Step/store-pack-trap` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_storePackTrap {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10 B) "Step" 9 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ := firesCfg10_inv (hasRuleAt10_storePackTrap B) hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes10_three hes
  obtain ⟨i, rfl, fi⟩ := constI32_of_lhs10 h₁
  obtain ⟨⟨ty, x⟩, rfl, hty⟩ := const_tc10 h₂
  obtain ⟨t, sz, ao, rfl, rfl, fa, fn⟩ := storePack_decode (inn_of_eval10 hty) h₃
  have ew : w = configV hn ⟨s, f, [.trap]⟩ := EvalExp.unique hrh (evalExp_zTrap10 fz)
  obtain ⟨a, m, hm⟩ := mem_of_good3 hg (fun h => h)
  have hlt : m.data.size < effectiveAddress i ao + sz.width / 8 :=
    trap_of_prem10 fz (evalExp_varE_iff.1 fi) fa (evalExp_var fn) (packWidth10_cases sz) hm
      (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨_, ew, step_intStoreTrap hm hlt⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole

module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.ValTyping

/-!
# `memory.grow-succeed` forward, at `bytesB10`

1.0's `Step/memory.grow-succeed` (rule 11) is 2.0's rule 19 verbatim
(`Sim20.Whole.memGrowSucceedRule`, kernel `rfl` at the 1.0 index):

  `z; (CONST I32 n) MEMORY.GROW ~> $with_meminst(z, 0, mi); (CONST I32 $(|$mem(z, 0).BYTES| / (64 * $Ki)))`

under `$growmemory($mem(z, 0), n) = mi`. At `bytesB10` the builtins answer `$growmemory` with the
image of V1's `Memory.grow?` (`bytesB10_growmemory`), so V1's successful `memory.grow` is this
rule forward (`fwdAt10_memGrowSucceed_bytesB10`):

* `mi` is the grown instance, typed by pass 3's `typedV_memInst_grow10`;
* `$with_meminst` writes it at the frame's memory (`evalExp_withMeminst10`, 2.0's proof at the
  1.0 clause);
* the old page count is whole, because `Memory.grow?` requires a page-aligned memory, so the
  `rat` quotient converts back to `nat` (`evalExp_pages10`), and it is below `2^32`.

This discharges the `memoryGrowSucceed` field of `FwdRestR10` at `bytesB10 P`, for every `P`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst MemAddr)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV stateT evalExp_case evalExp_tup2 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathSet_idx pathSet_dot
  pathSet_root evalExp_idxPayload HasClause1 idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.Whole (memGrowSucceedRule sfxyPat withInstBody20 mem0E pagesE
  constNE growMemCallE evalExp_constN)
open Silmaril.Wasm.SpecTec.Sim20.Pure (fires_of_ruleAt prems_one)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

theorem hasRuleAt10_memGrowSucceed (B : Builtins) :
    HasRuleAt (simEnv10 B) "Step" "%~>%" 11 memGrowSucceedRule := ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## `$mem(z, 0)` and `$with_meminst(z, 0, mi)` -/

/-- **`$mem(z, 0)`** at the 1.0 encoding. -/
theorem evalExp_mem0_10 {ρ : VarEnv} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (hρ : ρ.findDef? "mem" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (hm : frameMemory s f = some (a, m)) : EvalExp (simEnv10 B) ρ mem0E (memInstV m) := by
  obtain ⟨ha, hs⟩ := frameMemory_some hm
  exact evalExp_call1 hasClause_mem10 hρ (evalArgs_cons (Sim.evalExp_var fz)
    (evalArgs_cons evalExp_pct0 evalArgs_nil)) Sim20.State.matchArgs_sfx
    (evalExp_idxE_iff.2 ⟨_, a.value, evalExp_dotE_iff.2 ⟨storeV hn s, Sim.evalExp_var rfl, rfl⟩,
      evalExp_idxE_iff.2 ⟨_, 0, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
        evalExp_dotE_iff.2 ⟨frameV f, Sim.evalExp_var rfl, rfl⟩, rfl⟩,
        evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
      by simp [Value.idx?, List.getElem?_map, hs]⟩)

theorem hasClause_withMeminst10 :
    HasClause1 (simEnv10 B) "with_meminst" (sfxyPat "mi") (withInstBody20 "MEMS" "mi") :=
  ⟨_, _, _, rfl⟩

/-- The store with one memory replaced. -/
theorem storeV_setMem10 (s : Store H) (a : MemAddr) (mi : MemInst) :
    (storeV hn s).setField "MEMS" (.list ((s.memories.map memInstV).set a.value (memInstV mi))) =
      some (storeV hn (setMemory s a mi)) := by
  simp [storeV, Value.setField, setMemory, List.map_set]

/-- **`$with_meminst(z, 0, mi')`** at the 1.0 encoding, at the frame's memory. -/
theorem evalExp_withMeminst10 {ρ : VarEnv} {ez ey : Exp} {s : Store H} {f : Frame} {a : MemAddr}
    {m mi' : MemInst} (hρ : ρ.findDef? "with_meminst" = none)
    (hz : EvalExp (simEnv10 B) ρ ez (stateV hn s f))
    (hy : EvalExp (simEnv10 B) ρ ey (memInstV mi')) (hm : frameMemory s f = some (a, m)) :
    EvalExp (simEnv10 B) ρ (.callE "with_meminst" [.expA ez,
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA ey])
      (stateV hn (setMemory s a mi') f) := by
  obtain ⟨ha, hs⟩ := frameMemory_some hm
  refine evalExp_call1 hasClause_withMeminst10 hρ
    (evalArgs_cons hz (evalArgs_cons evalExp_pct0 (evalArgs_cons hy evalArgs_nil)))
    (matchArgs_cons (matchArg_expA Sim20.State.matchExp_state) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        matchArgs_nil))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (Sim.evalExp_var rfl))
  have ha' : a.value < s.memories.length := (List.getElem?_eq_some_iff.1 hs).1
  refine evalExp_updE_iff.2 ⟨storeV hn s, memInstV mi', Sim.evalExp_var rfl,
    Sim.evalExp_var rfl, ?_⟩
  exact pathSet_idx (i := a.value) (pathGet_dot pathGet_root rfl)
    (evalExp_idxE_iff.2 ⟨_, 0, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, Sim.evalExp_var rfl, rfl⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩)
    (by simp [Value.setIdx, ha'])
    (pathSet_dot pathGet_root (storeV_setMem10 s a _) pathSet_root)

/-! ## The page count -/

/-- A whole number of pages converts back from `rat`. -/
theorem cvt_pages10 (p : Nat) :
    Num.cvt .natT (.ratN (((p * 65536 : Nat) : Rat) / ((64 * 1024 : Nat) : Rat))) =
      some (.natN p) := by
  have e : (((p * 65536 : Nat) : Rat) / ((64 * 1024 : Nat) : Rat)) = (p : Rat) := by
    push_cast
    field_simp
  rw [e]
  simp [Num.cvt]

/-- **`|$mem(z, 0).BYTES| / (64 * $Ki)`**, at a page-aligned memory. -/
theorem evalExp_pagesE10 {ρ : VarEnv} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (hρ₁ : ρ.findDef? "mem" = none) (hρ₂ : ρ.findDef? "Ki" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (hm : frameMemory s f = some (a, m))
    (hal : m.data.size % Execution.Memory.pageSize = 0) :
    EvalExp (simEnv10 B) ρ pagesE (.num (.natN (Execution.Memory.size m.data))) := by
  set p := Execution.Memory.size m.data with hp
  have hsz : m.data.size = p * 65536 := by
    have := Nat.div_add_mod m.data.size Execution.Memory.pageSize
    simp only [Execution.Memory.size, Execution.Memory.pageSize] at hp hal this ⊢
    omega
  have hlen : EvalExp (simEnv10 B) ρ (.cvtE (.lenE (.dotE mem0E "BYTES")) .natT .ratT)
      (.num (.ratN ((p * 65536 : Nat) : Rat))) :=
    evalExp_cvtNum (hsz ▸ evalExp_memLen10 hρ₁ fz hm) rfl
  have hden : EvalExp (simEnv10 B) ρ (.cvtE (.binE .mulOp (.numT .natT) (.numE (.natN 64))
      (.callE "Ki" [])) .natT .ratT) (.num (.ratN ((64 * 1024 : Nat) : Rat))) :=
    evalExp_cvtNum (evalExp_binNum evalExp_num (evalExp_ki10 hρ₂) rfl) rfl
  refine evalExp_cvtNum (evalExp_binNum hlen hden ?_) (cvt_pages10 p)
  simp [Num.bin]

/-! ## The rule, forward -/

/-- The pages of a memory that grows are below `2^32`, and its bytes are page-aligned. -/
theorem grow_bounds10 {m : MemInst} {n : Nat} {d : Execution.Memory.Bytes}
    (h : Execution.Memory.grow? m.data m.max n = some d) :
    m.data.size % Execution.Memory.pageSize = 0 ∧ Execution.Memory.size m.data < 2 ^ 32 := by
  unfold Execution.Memory.grow? at h
  split at h
  · rename_i hc
    simp only [Execution.Memory.maxPages] at hc
    exact ⟨hc.1, by omega⟩
  · cases h

/-- The left-hand side `z; (CONST I32 n) MEMORY.GROW`, evaluated. -/
theorem growLhs10 {ρ : VarEnv} {s : Store H} {f : Frame} {c : BitVec 32}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fn : ρ.findVal? "n" = some (.num (.natN c.toNat))) :
    EvalExp (simEnv10 B) ρ (.caseE "%;%" (.tupE [.varE "z",
      .listE [constNE, .caseE "MEMORY.GROW" (.tupE [])]]))
      (configV hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩) := by
  have hcode : adminsToV [value (.int .i32 c), .source .memoryGrow] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]), caseNilV "MEMORY.GROW"] := by
    rw [adminsToV_map10, List.map_cons, adminToV_value]
    rfl
  rw [configV_eq_cfgV10, hcode]
  exact evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (Sim20.Pure.evalExp_list2
    (evalExp_constN fn) Sim20.Pure.evalExp_caseNil))

/-- The right-hand side `$with_meminst(z, 0, mi); (CONST I32 pages)`, evaluated. -/
theorem growRhs10 {ρ : VarEnv} {s : Store H} {f : Frame} {a : MemAddr} {m mi : MemInst}
    (hρ₁ : ρ.findDef? "with_meminst" = none) (hρ₂ : ρ.findDef? "mem" = none)
    (hρ₃ : ρ.findDef? "Ki" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fmi : ρ.findVal? "mi" = some (memInstV mi))
    (hm : frameMemory s f = some (a, m)) (hal : m.data.size % Execution.Memory.pageSize = 0)
    (hlt : Execution.Memory.size m.data < 2 ^ 32) :
    EvalExp (simEnv10 B) ρ (.caseE "%;%" (.tupE [.callE "with_meminst" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.varE "mi")],
        .listE [Sim20.Whole.constI32E pagesE]]))
      (configV hn ⟨setMemory s a mi, f,
        [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩) := by
  have hb : (BitVec.ofNat 32 (Execution.Memory.size m.data)).toNat = Execution.Memory.size m.data := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hcode : adminsToV [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV (Execution.Memory.size m.data)])] := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    show [Value.case "CONST" (.tuple [caseNilV "I32",
      pctV (BitVec.ofNat 32 (Execution.Memory.size m.data)).toNat])] = _
    rw [hb]
  rw [configV_eq_cfgV10, hcode]
  exact evalExp_case (evalExp_tup2 (evalExp_withMeminst10 hρ₁ (Sim.evalExp_var fz)
    (Sim.evalExp_var fmi) hm) (evalExp_list1 (evalExp_case (evalExp_tup2
      Sim20.Pure.evalExp_caseNil (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
        (evalExp_pagesE10 hρ₂ hρ₃ fz hm hal) evalExps_nil, rfl⟩))))))

/-- The premise `$growmemory($mem(z, 0), n) = mi`, at `bytesB10` and V1's growth. -/
theorem growPrem10 {P : Profile} {ρ : VarEnv} {s : Store H} {f : Frame} {a : MemAddr}
    {m : MemInst} {c : BitVec 32} {d : Execution.Memory.Bytes}
    (hρ₁ : ρ.findDef? "growmemory" = none) (hρ₂ : ρ.findDef? "mem" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fn : ρ.findVal? "n" = some (.num (.natN c.toNat)))
    (fmi : ρ.findVal? "mi" = some (memInstV {m with data := d}))
    (hm : frameMemory s f = some (a, m))
    (hg : Execution.Memory.grow? m.data m.max c.toNat = some d) :
    EvalExp (simEnv10 (bytesB10 P)) ρ (.cmpE .eqOp .boolT growMemCallE (.varE "mi"))
      (.bool true) := by
  obtain ⟨ps, t, cs, hd, hu⟩ := Sim20.Whole.growmemory10_undef (B := bytesB10 P) (memInstV m)
    (.num (.natN c.toNat))
  have hb : (simEnv10 (bytesB10 P)).builtins.call "growmemory"
      [.val (memInstV m), .val (.num (.natN c.toNat))] = some (memInstV {m with data := d}) := by
    rw [simEnv10, Env.builtins_withBuiltins, bytesB10_growmemory, hg]
    rfl
  have hcall : CallDef (simEnv10 (bytesB10 P)) ρ "growmemory" [.expA mem0E, .expA (.varE "n")]
      (memInstV {m with data := d}) := by
    refine Equiv.ExecNumeric.callDef_iff.2 ⟨_, ps, t, cs, evalArgs_cons (evalExp_mem0_10 hρ₂ fz hm)
      (evalArgs_cons (Sim.evalExp_var fn) evalArgs_nil), ?_, .inr ⟨hu, ?_⟩⟩
    · rw [hρ₁, Option.getD_none]
      exact hd
    · rw [hρ₁, Option.getD_none]
      exact hb
  exact evalExp_cmpE_iff.2 ⟨_, _, evalExp_callE_iff.2 hcall, Sim.evalExp_var fmi,
    cmpValues_eq_true_iff.2 rfl⟩

/-- The scope of `memory.grow-succeed`. -/
abbrev growScope10 (z : Value) (c : BitVec 32) (mi : MemInst) : List (IL.Id × Value) :=
  [("z", z), ("n", .num (.natN c.toNat)), ("mi", memInstV mi)]

/-- **`memory.grow-succeed` fires forward** at `bytesB10`, at V1's successful growth. -/
theorem fires10_memGrowSucceed {P : Profile} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    {c : BitVec 32} {d : Execution.Memory.Bytes}
    (hz : TypedV (simEnv10 (bytesB10 P)) stateT (stateV hn s f))
    (hm : frameMemory s f = some (a, m))
    (hg : Execution.Memory.grow? m.data m.max c.toNat = some d) :
    Fires (simEnv10 (bytesB10 P)) "Step" 11 (.tuple [
      configV hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩,
      configV hn ⟨setMemory s a {m with data := d}, f,
        [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩]) := by
  let σ := growScope10 (stateV hn s f) c {m with data := d}
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN c.toNat)) := rfl
  have fmi : (VarEnv.empty.bindVals σ).findVal? "mi" = some (memInstV {m with data := d}) := rfl
  obtain ⟨hal, hlt⟩ := grow_bounds10 hg
  have hmi : TypedV (simEnv10 (bytesB10 P)) (.varT "meminst" []) (memInstV {m with data := d}) :=
    typedV_memInst_grow10 (Sim20.Whole.typedV_of_getElem? (storeTy10_of_state hz).mems
      (frameMemory_some hm).2) hg
  refine fires_of_ruleAt (hasRuleAt10_memGrowSucceed _) σ
    (QuantsOk.cons fz (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons fn (typedV_n10 _ _ ⟨rfl, rfl, rfl⟩)
      (QuantsOk.cons fmi (hmi _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)))
    (evalExp_tup2 (growLhs10 fz fn) (growRhs10 rfl rfl rfl fz fmi hm hal hlt))
    (prems_one (.ifPr (growPrem10 rfl rfl fz fn fmi hm hg)))

/-- **`memory.grow` that succeeds, forward, at `bytesB10`.** -/
theorem fwdAt10_memGrowSucceed_bytesB10 {P : Profile} (s : Store H) (f : Frame) (a : MemAddr)
    (m : MemInst) (c : BitVec 32) (d : Execution.Memory.Bytes) (hm : frameMemory s f = some (a, m))
    (hg : Execution.Memory.grow? m.data m.max c.toNat = some d) :
    FwdAt10 (bytesB10 P) hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
      ⟨setMemory s a {m with data := d}, f,
        [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩ :=
  fun hz _ _ _ => sstepB10_of_fires (fires10_memGrowSucceed hz hm hg)

/-! ## What is left at `bytesB10` -/

/-- **The forward obligations still open at given builtins**: the two successful loads. -/
structure FwdLoads10 (B : Builtins) (hn : H → String) : Prop where
  intLoad : ∀ (s : Store H) (f : Frame) (t : IntType) (packed : Option (V1.PackSize × Signedness))
    (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value),
      frameMemory s f = some (a, m) →
      V1.Execution.loadInt t packed m.data (V1.Execution.effectiveAddress c arg) = some v →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ ⟨s, f, [value v]⟩
  floatLoad : ∀ (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
    (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value), frameMemory s f = some (a, m) →
      V1.Execution.loadFloat t m.data (V1.Execution.effectiveAddress c arg) = some v →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [value v]⟩

/-- At `bytesB10`, `FwdRestR10` is the two loads. -/
theorem fwdRestR10_bytesB10 {P : Profile} (L : FwdLoads10 (bytesB10 P) hn) :
    FwdRestR10 (bytesB10 P) hn where
  intLoad := L.intLoad
  floatLoad := L.floatLoad
  memoryGrowSucceed s f a m c d hm hg := fwdAt10_memGrowSucceed_bytesB10 s f a m c d hm hg

/-- **The forward 1.0 half at `bytesB10`, from the two successful loads**, with no
successor-typing hypothesis. -/
theorem wholeStepFwd10_bytesB10' {host : HostSemantics H} {nd : Bool}
    {r : Silmaril.Wasm.Numerics.RelaxedChoice}
    (L : FwdLoads10 (bytesB10 (Profile.spec nd r)) hn) {c c' : Config H}
    (hc : Typed10 (simEnv10 (bytesB10 (Profile.spec nd r))) hn c)
    (hpl : Plain10 c.code) (hg : Silmaril.Wasm.SpecTec.Sim10.GSetOk c.store c.frame c.code)
    (hal : MemsAligned10 c.store) (h : Step host c c') :
    Silmaril.Wasm.SpecTec.Sim.Round6.Reading.SStepB (simEnv10 (bytesB10 (Profile.spec nd r)))
      (configV hn c) (configV hn c') :=
  wholeStepFwd10_of_restR'' (numAgree10_bytesB10 _) (fwdRestR10_bytesB10 L) hc hpl hg hal h

end Silmaril.Wasm.SpecTec.Sim10.Whole


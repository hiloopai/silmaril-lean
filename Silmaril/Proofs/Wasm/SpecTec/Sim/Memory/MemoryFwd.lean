module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Memory
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.TableFwd

/-!
# Track memory: `memory.fill`, `memory.copy`, `memory.init`, at the Core encoding

Each `fwd_memory*` has the type of the matching `MemoryStep` case of `Forward.memory` at
`simEnv B`, plus the no-wrap hypothesis `hw` where Core's bit-vector arithmetic could wrap
(gap G1). Unlike tables, a memory may hold exactly `2 ^ |at|` bytes (Core's `MemInst.grow?`
allows `2 ^ (|at| - 16)` pages), so `memory.fill` at `i = 2 ^ |at| - 1, n = 1` is a *reachable*
configuration where `hw` fails: see `docs/projects/spectec/README.md`, track memory.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)

variable {H : Type}

/-! ## Encoding facts -/

/-- `Store.mem?` unfolded. -/
theorem Store.mem?_eq_some {s : Store H} {f : Frame} {x : MemIdx} {a : Nat}
    {m : MemInst} (h : s.mem? f x = some (a, m)) :
    f.module.mems[x.toNat]? = some a ∧ s.mems[a]? = some m := by
  simp only [Store.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', ha, m', hm, rfl, rfl⟩ := h
  exact ⟨ha, hm⟩

/-- The encoded memory the module lists at `x`. -/
theorem memAt_of_mem? (hn : H → String) {s : Store H} {f : Frame} {x : MemIdx} {a : Nat}
    {m : MemInst} (h : s.mem? f x = some (a, m)) :
    MemAt (storeV hn s) (frameV f) x.toNat (memInstToValue m) := by
  obtain ⟨ha, hm⟩ := Store.mem?_eq_some h
  exact ⟨_, _, _, a, State.storeV_MEMS hn s, State.frameV_MODULE f, State.moduleV_MEMS _,
    State.getElem?_map_natN ha, by simp [hm]⟩

/-- The encoded data segment the module lists at `y`. -/
theorem dataAt_of_data? (hn : H → String) {s : Store H} {f : Frame} {y : DataIdx} {a : Nat}
    {d : DataInst} (h : s.data? f y = some (a, d)) :
    DataAt (storeV hn s) (frameV f) y.toNat (dataInstToValue d) := by
  obtain ⟨ha, hd⟩ := State.Store.data?_eq_some h
  exact ⟨_, _, _, a, State.storeV_DATAS hn s, State.frameV_MODULE f, State.moduleV_DATAS _,
    State.getElem?_map_natN ha, by simp [hd]⟩

/-- The encoded bytes. -/
abbrev bytesL (b : ByteArray) : List Value :=
  b.data.toList.map fun c => percentV (.num (.natN c.toNat))

@[simp] theorem bytesL_length (b : ByteArray) : (bytesL b).length = b.size := by
  rw [List.length_map, Array.length_toList]
  rfl

@[simp] theorem memInstV_BYTES (m : MemInst) :
    (memInstToValue m).field? "BYTES" = some (.list (bytesL m.bytes)) := rfl

@[simp] theorem dataInstV_BYTES (d : DataInst) :
    (dataInstToValue d).field? "BYTES" = some (.list (bytesL d.bytes)) := rfl

/-- `STORE I32 8 x $memarg0` encodes as `store8V`. -/
theorem adminToV_store8 (x : MemIdx) : adminToV (store8 x) = store8V x.toNat := rfl

/-- `LOAD I32 (8 _ U) x $memarg0` encodes as `load8uV`. -/
theorem adminToV_load8u (x : MemIdx) : adminToV (load8u x) = load8uV x.toNat := rfl

/-! ## `$memarg0` in `simEnv B` -/

/-- The body of `$memarg0`. -/
abbrev memarg0Body : Exp :=
  .strE [.mk "ALIGN" (.caseE "%" (.tupE [.numE (.natN 0)])),
    .mk "OFFSET" (.caseE "%" (.tupE [.numE (.natN 0)]))]

set_option maxRecDepth 100000 in
/-- `$memarg0` is the single premise-free clause `memarg0Body`. -/
theorem memarg0_baseEnv : State.HasClause1 baseEnv "memarg0" [] memarg0Body := ⟨_, _, _, rfl⟩

/-- `$memarg0()` evaluates to `{ALIGN 0, OFFSET 0}` in `simEnv B`. -/
theorem memarg0Ok_simEnv (B : Builtins) : Memarg0Ok (simEnv B) := by
  intro σ
  refine State.evalExp_call1 (memarg0_baseEnv.withBuiltins B) (findDef_bindVals_empty σ _)
    (ρ₀ := VarEnv.empty) Silmaril.SpecTec.Equiv.evalArgs_nil Silmaril.SpecTec.Sem.matchArgs_nil
    ⟨8, by simp [evalExp, evalExpFields, evalExps, memargV, memarg0,
      Silmaril.SpecTec.Equiv.Execution.pctV]⟩

set_option maxRecDepth 100000 in
/-- `$Ki` is the single premise-free clause `1024`. -/
theorem ki_baseEnv : State.HasClause1 baseEnv "Ki" [] (.numE (.natN 1024)) := ⟨_, _, _, rfl⟩

/-- `$Ki()` evaluates to `1024` in `simEnv B`. -/
theorem kiOk_simEnv (B : Builtins) : KiOk (simEnv B) := fun σ =>
  State.evalExp_call1 (ki_baseEnv.withBuiltins B) (findDef_bindVals_empty σ _)
    (ρ₀ := VarEnv.empty) Silmaril.SpecTec.Equiv.evalArgs_nil Silmaril.SpecTec.Sem.matchArgs_nil
    RefsGC.evalExp_num'

@[simp] theorem memInstV_TYPE (m : MemInst) :
    (memInstToValue m).field? "TYPE" = some (.case "%%PAGE" (.tuple [
      Encode.toValue m.type.address, Encode.toValue m.type.limits])) := rfl

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B))
include T St

/-! ## `memory.size` -/

/-- `MemoryStep.size`, forward, for a memory whose size is a whole number of pages, fewer than
`2 ^ |at|` of them. -/
theorem fwd_memorySize (M : MemTyping (simEnv B)) {s : Store H} {f : Frame} {x : MemIdx}
    {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
    (hpg : mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0)
    (hw : mi.pages < 2 ^ mi.type.address.intType.width) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.memorySize x)]⟩
      ⟨s, f, [aconst mi.type.address (BitVec.ofNat _ mi.pages)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  obtain ⟨-, hmi⟩ := Store.mem?_eq_some hm
  have hL := M.memType hn s f mi (List.mem_of_getElem? hmi) (State.typedV_state T hc)
  have hp : mi.pages * (64 * 1024) = (bytesL mi.bytes).length := by
    rw [bytesL_length, MemInst.pages]
    exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpg)
  have hs := sread_memorySize (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memorySize (kiOk_simEnv B) (State.typedV_state T hc)
    x.value.isLt hL (memAt_of_mem? hn hm) (memInstV_BYTES mi) (memInstV_TYPE mi) hp
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    toNat_ofNat_of_lt hw]
  exact hs

/-! ## `memory.fill` -/

/-- `MemoryStep.fillOob`, forward. -/
theorem fwd_memoryFillOob {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {i n : BitVec a.intType.width} {v : Val} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < i.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.memoryFill x)]⟩
      ⟨s, f, [.trap]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hv := State.typedV_val_of_mem T hc (v := v) (by simp)
  have hs := sread_memoryFillOob (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryFillOob (State.typedV_state T hc) x.value.isLt hv
    (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin]
  exact hs

/-- `MemoryStep.fillZero`, forward. -/
theorem fwd_memoryFillZero {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {v : Val} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : i.toNat ≤ mi.bytes.size) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a 0, .plain (.memoryFill x)]⟩
      ⟨s, f, []⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hv := State.typedV_val_of_mem T hc (v := v) (by simp)
  have hs := sread_memoryFillZero (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryFillZero (State.hasReadRules_simEnv B).memoryFillOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x.value.isLt hv
    (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin]
  exact hs

/-- `MemoryStep.fillSucc`, forward, when `i + 1` does not wrap. -/
theorem fwd_memoryFillSucc {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {i n : BitVec a.intType.width} {v : Val} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : i.toNat + n.toNat ≤ mi.bytes.size) (hnz : n ≠ 0)
    (hw : i.toNat + 1 < 2 ^ a.intType.width) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.memoryFill x)]⟩
      ⟨s, f, [aconst a i, v.toAdmin, store8 x,
        aconst a (i + 1), v.toAdmin, aconst a (n - 1), .plain (.memoryFill x)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hv := State.typedV_val_of_mem T hc (v := v) (by simp)
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_memoryFillSucc (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryFillSucc (State.hasReadRules_simEnv B).memoryFillOob
    (State.hasReadRules_simEnv B).memoryFillZero (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x.value.isLt hv (memAt_of_mem? hn hm)
    (memInstV_BYTES mi) (by simpa using h) hn0 (memarg0Ok_simEnv B)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin, adminToV_store8, toNat_add_one hw, toNat_sub_one hnz]
  exact hs

/-! ## `memory.copy` -/

/-- `MemoryStep.copyOob`, forward. -/
theorem fwd_memoryCopyOob {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (h : mi₁.bytes.size < i₁.toNat + n.toNat ∨ mi₂.bytes.size < i₂.toNat + n.toNat) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩
      ⟨s, f, [.trap]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_memoryCopyOob (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryCopyOob (State.typedV_state T hc) x₁.value.isLt
    x₂.value.isLt (memAt_of_mem? hn h₁) (memInstV_BYTES mi₁)
    (memAt_of_mem? hn h₂) (memInstV_BYTES mi₂) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `MemoryStep.copyZero`, forward. -/
theorem fwd_memoryCopyZero {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width}
    {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (h : i₁.toNat ≤ mi₁.bytes.size ∧ i₂.toNat ≤ mi₂.bytes.size) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' 0, .plain (.memoryCopy x₁ x₂)]⟩
      ⟨s, f, []⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_memoryCopyZero (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryCopyZero (State.hasReadRules_simEnv B).memoryCopyOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x₁.value.isLt
    x₂.value.isLt (memAt_of_mem? hn h₁) (memInstV_BYTES mi₁)
    (memAt_of_mem? hn h₂) (memInstV_BYTES mi₂) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `MemoryStep.copyLe`, forward, when neither `i₁ + 1` nor `i₂ + 1` wraps. -/
theorem fwd_memoryCopyLe {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (h : i₁.toNat + n.toNat ≤ mi₁.bytes.size ∧ i₂.toNat + n.toNat ≤ mi₂.bytes.size)
    (hnz : n ≠ 0) (hle : i₁.toNat ≤ i₂.toNat)
    (hw : i₁.toNat + 1 < 2 ^ a₁.intType.width ∧ i₂.toNat + 1 < 2 ^ a₂.intType.width) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩
      ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, load8u x₂, store8 x₁,
        aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1), .plain (.memoryCopy x₁ x₂)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_memoryCopyLe (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryCopyLe (State.hasReadRules_simEnv B).memoryCopyOob
    (State.hasReadRules_simEnv B).memoryCopyZero (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x₁.value.isLt x₂.value.isLt (memAt_of_mem? hn h₁)
    (memInstV_BYTES mi₁) (memAt_of_mem? hn h₂) (memInstV_BYTES mi₂)
    (by simpa using h) hn0 hle (memarg0Ok_simEnv B)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    adminToV_store8, adminToV_load8u, toNat_add_one hw.1, toNat_add_one hw.2,
    toNat_sub_one hnz]
  exact hs

/-- `MemoryStep.copyGt`, forward, when `i₁ + n - 1` and `i₂ + n - 1` do not wrap. -/
theorem fwd_memoryCopyGt {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (h : i₁.toNat + n.toNat ≤ mi₁.bytes.size ∧ i₂.toNat + n.toNat ≤ mi₂.bytes.size)
    (hnz : n ≠ 0) (hgt : i₂.toNat < i₁.toNat)
    (hw : i₁.toNat + n.toNat ≤ 2 ^ a₁.intType.width ∧
      i₂.toNat + n.toNat ≤ 2 ^ a₂.intType.width) :
    FwdP (simEnv B) hn
      ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩
      ⟨s, f, [aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1),
        aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1), load8u x₂, store8 x₁,
        aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1), .plain (.memoryCopy x₁ x₂)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_memoryCopyGt (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryCopyGt (State.hasReadRules_simEnv B).memoryCopyOob
    (State.hasReadRules_simEnv B).memoryCopyZero (State.hasReadRules_simEnv B).memoryCopyLe
    (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x₁.value.isLt x₂.value.isLt (memAt_of_mem? hn h₁)
    (memInstV_BYTES mi₁) (memAt_of_mem? hn h₂) (memInstV_BYTES mi₂)
    (by simpa using h) hn0 hgt (memarg0Ok_simEnv B)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    adminToV_store8, adminToV_load8u, toNat_add_ofNat_sub_one i₁ hn0 hw.1,
    toNat_add_ofNat_sub_one i₂ hn0 hw.2, toNat_sub_one hnz]
  exact hs

/-! ## `memory.init` -/

/-- `MemoryStep.initOob`, forward. -/
theorem fwd_memoryInitOob {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
    (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
    (h : mi.bytes.size < i.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩
      ⟨s, f, [.trap]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_memoryInitOob (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryInitOob (State.typedV_state T hc) x.value.isLt
    y.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi)
    (dataAt_of_data? hn hd) (dataInstV_BYTES di) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    adminToV_constI32]
  exact hs

/-- `MemoryStep.initZero`, forward. -/
theorem fwd_memoryInitZero {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
    (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
    (h : i.toNat ≤ mi.bytes.size ∧ j.toNat ≤ di.bytes.size) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 0, .plain (.memoryInit x y)]⟩
      ⟨s, f, []⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hs := sread_memoryInitZero (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryInitZero (State.hasReadRules_simEnv B).memoryInitOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x.value.isLt
    y.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi)
    (dataAt_of_data? hn hd) (dataInstV_BYTES di) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    adminToV_constI32]
  exact hs

/-- `MemoryStep.initSucc`, forward, when neither `i + 1` nor `j + 1` wraps. -/
theorem fwd_memoryInitSucc {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
    {byte : UInt8}
    (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
    (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size)
    (hnz : n ≠ 0) (hb : di.bytes.data[j.toNat]? = some byte)
    (hw : i.toNat + 1 < 2 ^ a.intType.width ∧ j.toNat + 1 < 2 ^ 32) :
    FwdP (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩
      ⟨s, f, [aconst a i, constI32 (BitVec.ofNat 32 byte.toNat), store8 x,
        aconst a (i + 1), constI32 (j + 1), constI32 (n - 1), .plain (.memoryInit x y)]⟩ := by
  refine fwd_of_sread' T (hasStepRules_simEnv B).read fun hc => ?_
  have hn0 : n.toNat ≠ 0 := fun h' => hnz (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hs := sread_memoryInitSucc (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryInitSucc (State.hasReadRules_simEnv B).memoryInitOob
    (State.hasReadRules_simEnv B).memoryInitZero (RefsGC.readTable_simEnv B)
    (State.typedV_state T hc) x.value.isLt y.value.isLt (memAt_of_mem? hn hm)
    (memInstV_BYTES mi) (dataAt_of_data? hn hd) (dataInstV_BYTES di) (by simpa using h)
    hn0 (byte := byte.toNat) (by simp [bytesL, hb]; rfl) (memarg0Ok_simEnv B)
  rw [State.configV_eq]
  have hb32 : byte.toNat < 2 ^ 32 := Nat.lt_of_lt_of_le byte.toNat_lt (by decide)
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    adminToV_constI32, adminToV_store8, toNat_add_one hw.1, toNat_add_one hw.2,
    toNat_sub_one hnz, toNat_ofNat_of_lt hb32]
  exact hs

end Silmaril.Wasm.SpecTec.Sim.Memory

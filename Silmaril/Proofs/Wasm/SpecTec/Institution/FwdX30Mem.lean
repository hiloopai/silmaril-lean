module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Thms
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.ConfigOk.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms

/-!
# The forward direction at wasm-3.0, extended: the memory rules of `Step_read`

At the concrete primitives `Round4Int.BI`, every `MemoryStep` whose instruction is a `Step_read`
instruction (`memReadInstr`: the loads, `memory.size`, `memory.fill`, `memory.copy`,
`memory.init`) is a `Step_read` fact of the declarative reading, from a typed configuration
bounded 's sense. Round 4's `Bounded` excludes the vector memory instructions, so the
vector loads hold vacuously there.

The `sreadL_*` lemmas are the bodies of the memory and the fwdmem forward leaves
(`Memory.fwd_load*Oob`, `Memory.fwd_memory*`, `FwdMem.fwd_loadNum`, `FwdMem.fwd_loadPack`,
`FwdMem.fwd_load*Val`), stopped before the leaf lifts the fact with `Step/read`.
`sread_of_memStep` is `Round5.Fwd.fwd_memory5` with the `Step` cases (stores, `memory.grow`,
`data.drop`) excluded by the instruction.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Memory
open State (aconstV idxV)

variable {H : Type}

section MemFwd

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B))
include T St

/-- `fwd_memorySize`, before the lift. -/
theorem sreadL_memorySize (M : MemTyping (simEnv B)) {s : Store H} {f : Frame} {x : MemIdx}
    {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
    (hpg : mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0)
    (hw : mi.pages < 2 ^ mi.type.address.intType.width)
    (hc : Typed (simEnv B) hn ⟨s, f, [.plain (.memorySize x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [.plain (.memorySize x)]⟩)
      (adminsToV ([aconst mi.type.address (BitVec.ofNat _ mi.pages)])) := by
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

/-- `fwd_memoryFillOob`, before the lift. -/
theorem sreadL_memoryFillOob {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {i n : BitVec a.intType.width} {v : Val} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < i.toNat + n.toNat)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.memoryFill x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.memoryFill x)]⟩)
      (adminsToV ([.trap])) := by
  have hv := State.typedV_val_of_mem T hc (v := v) (by simp)
  have hs := sread_memoryFillOob (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryFillOob (State.typedV_state T hc) x.value.isLt hv
    (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin]
  exact hs

/-- `fwd_memoryFillZero`, before the lift. -/
theorem sreadL_memoryFillZero {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {i : BitVec a.intType.width} {v : Val} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : i.toNat ≤ mi.bytes.size)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a 0, .plain (.memoryFill x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, v.toAdmin, aconst a 0, .plain (.memoryFill x)]⟩)
      (adminsToV ([])) := by
  have hv := State.typedV_val_of_mem T hc (v := v) (by simp)
  have hs := sread_memoryFillZero (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryFillZero (State.hasReadRules_simEnv B).memoryFillOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x.value.isLt hv
    (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    State.adminToV_toAdmin]
  exact hs

/-- `fwd_memoryFillSucc`, before the lift. -/
theorem sreadL_memoryFillSucc {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {i n : BitVec a.intType.width} {v : Val} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : i.toNat + n.toNat ≤ mi.bytes.size) (hnz : n ≠ 0)
    (hw : i.toNat + 1 < 2 ^ a.intType.width)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.memoryFill x)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, v.toAdmin, aconst a n, .plain (.memoryFill x)]⟩)
      (adminsToV ([aconst a i, v.toAdmin, store8 x,
        aconst a (i + 1), v.toAdmin, aconst a (n - 1), .plain (.memoryFill x)])) := by
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

/-- `fwd_memoryCopyOob`, before the lift. -/
theorem sreadL_memoryCopyOob {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (h : mi₁.bytes.size < i₁.toNat + n.toNat ∨ mi₂.bytes.size < i₂.toNat + n.toNat)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩)
      (adminsToV ([.trap])) := by
  have hs := sread_memoryCopyOob (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryCopyOob (State.typedV_state T hc) x₁.value.isLt
    x₂.value.isLt (memAt_of_mem? hn h₁) (memInstV_BYTES mi₁)
    (memAt_of_mem? hn h₂) (memInstV_BYTES mi₂) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `fwd_memoryCopyZero`, before the lift. -/
theorem sreadL_memoryCopyZero {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width}
    {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (h : i₁.toNat ≤ mi₁.bytes.size ∧ i₂.toNat ≤ mi₂.bytes.size)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' 0, .plain (.memoryCopy x₁ x₂)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' 0, .plain (.memoryCopy x₁ x₂)]⟩)
      (adminsToV ([])) := by
  have hs := sread_memoryCopyZero (a' := a') (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryCopyZero (State.hasReadRules_simEnv B).memoryCopyOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x₁.value.isLt
    x₂.value.isLt (memAt_of_mem? hn h₁) (memInstV_BYTES mi₁)
    (memAt_of_mem? hn h₂) (memInstV_BYTES mi₂) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `fwd_memoryCopyLe`, before the lift. -/
theorem sreadL_memoryCopyLe {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (h : i₁.toNat + n.toNat ≤ mi₁.bytes.size ∧ i₂.toNat + n.toNat ≤ mi₂.bytes.size)
    (hnz : n ≠ 0) (hle : i₁.toNat ≤ i₂.toNat)
    (hw : i₁.toNat + 1 < 2 ^ a₁.intType.width ∧ i₂.toNat + 1 < 2 ^ a₂.intType.width)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩)
      (adminsToV ([aconst a₁ i₁, aconst a₂ i₂, load8u x₂, store8 x₁,
        aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1), .plain (.memoryCopy x₁ x₂)])) := by
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

/-- `fwd_memoryCopyGt`, before the lift. -/
theorem sreadL_memoryCopyGt {s : Store H} {f : Frame} {x₁ x₂ : MemIdx} {a₁ a₂ a' : AddrType}
    {i₁ : BitVec a₁.intType.width} {i₂ : BitVec a₂.intType.width} {n : BitVec a'.intType.width}
    {ma₁ ma₂ : Nat} {mi₁ mi₂ : MemInst}
    (h₁ : s.mem? f x₁ = some (ma₁, mi₁)) (h₂ : s.mem? f x₂ = some (ma₂, mi₂))
    (h : i₁.toNat + n.toNat ≤ mi₁.bytes.size ∧ i₂.toNat + n.toNat ≤ mi₂.bytes.size)
    (hnz : n ≠ 0) (hgt : i₂.toNat < i₁.toNat)
    (hw : i₁.toNat + n.toNat ≤ 2 ^ a₁.intType.width ∧
      i₂.toNat + n.toNat ≤ 2 ^ a₂.intType.width)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a₁ i₁, aconst a₂ i₂, aconst a' n, .plain (.memoryCopy x₁ x₂)]⟩)
      (adminsToV ([aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1),
        aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1), load8u x₂, store8 x₁,
        aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1), .plain (.memoryCopy x₁ x₂)])) := by
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

/-- `fwd_memoryInitOob`, before the lift. -/
theorem sreadL_memoryInitOob {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
    (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
    (h : mi.bytes.size < i.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩)
      (adminsToV ([.trap])) := by
  have hs := sread_memoryInitOob (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryInitOob (State.typedV_state T hc) x.value.isLt
    y.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi)
    (dataAt_of_data? hn hd) (dataInstV_BYTES di) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    Memory.adminToV_constI32]
  exact hs

/-- `fwd_memoryInitZero`, before the lift. -/
theorem sreadL_memoryInitZero {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
    (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
    (h : i.toNat ≤ mi.bytes.size ∧ j.toNat ≤ di.bytes.size)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 0, .plain (.memoryInit x y)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, constI32 j, constI32 0, .plain (.memoryInit x y)]⟩)
      (adminsToV ([])) := by
  have hs := sread_memoryInitZero (State.stateDefs_simEnv B) St
    (State.hasReadRules_simEnv B).memoryInitZero (State.hasReadRules_simEnv B).memoryInitOob
    (RefsGC.readTable_simEnv B) (State.typedV_state T hc) x.value.isLt
    y.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi)
    (dataAt_of_data? hn hd) (dataInstV_BYTES di) (by simpa using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst,
    Memory.adminToV_constI32]
  exact hs

/-- `fwd_memoryInitSucc`, before the lift. -/
theorem sreadL_memoryInitSucc {s : Store H} {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
    {i : BitVec a.intType.width} {j n : BitVec 32} {ma da : Nat} {mi : MemInst} {di : DataInst}
    {byte : UInt8}
    (hm : s.mem? f x = some (ma, mi)) (hd : s.data? f y = some (da, di))
    (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size)
    (hnz : n ≠ 0) (hb : di.bytes.data[j.toNat]? = some byte)
    (hw : i.toNat + 1 < 2 ^ a.intType.width ∧ j.toNat + 1 < 2 ^ 32)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩)
      (adminsToV ([aconst a i, constI32 (BitVec.ofNat 32 byte.toNat), store8 x,
        aconst a (i + 1), constI32 (j + 1), constI32 (n - 1), .plain (.memoryInit x y)])) := by
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
    Memory.adminToV_constI32, adminToV_store8, toNat_add_one hw.1, toNat_add_one hw.2,
    toNat_sub_one hnz, toNat_ofNat_of_lt hb32]
  exact hs

end MemFwd

section Loads

open Silmaril.SpecTec.Equiv.ExecRead

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B)) (M : MemTyping (simEnv B))
include T St M

/-- `fwd_loadIntOob`, before the lift. -/
theorem sreadL_loadIntOob {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t none x arg)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.intLoad t none x arg)]⟩)
      (adminsToV ([.trap])) := by
  have hs := sread_loadIntOob (State.stateDefs_simEnv B) St M
    (State.hasReadRules_simEnv B).loadNumOob (State.growDefs_simEnv B) (State.typedV_state T hc)
    x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa [effAddr] using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `fwd_loadPackOob`, before the lift. -/
theorem sreadL_loadPackOob {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width}
    {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
    (h : mi.bytes.size < effAddr i.toNat arg + sz.width / 8)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩)
      (adminsToV ([.trap])) := by
  have hs := sread_loadPackOob (t := t) (sx := sx) (State.stateDefs_simEnv B) St M
    (State.hasReadRules_simEnv B).loadPackOob (State.typedV_state T hc)
    x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa [effAddr] using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `Memory.fwd_loadFloatOob`, before the lift. -/
theorem sreadL_loadFloatOob {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (h : mi.bytes.size < effAddr i.toNat arg + t.width / 8)
    (hc : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.floatLoad t x arg)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.floatLoad t x arg)]⟩)
      (adminsToV [.trap]) := by
  have hs := sread_loadFloatOob (State.stateDefs_simEnv B) (sizeDefs_simEnv B) St M
    (State.hasReadRules_simEnv B).loadNumOob (State.typedV_state T hc)
    x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES mi) (by simpa [effAddr] using h)
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

end Loads

section FwdMem

open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Sim.FwdMem

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : State.StateTyping (simEnv B)) (M : MemTyping (simEnv B)) (Bf : BytesFuns (simEnv B))
include T St M Bf

/-- `fwd_loadNum`, before the lift. -/
theorem sreadL_loadNum {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {v : NumVal} {p : Instr}
    (hp : instrToV p = .case "LOAD" (.tuple [Encode.toValue v.type, .opt none,
      idxV x.toNat, memargV arg]))
    (hm : s.mem? f x = some (ma, mi)) (hle : effAddr i.toNat arg + v.type.width / 8 ≤ mi.bytes.size)
    (hT : SliceTotal ∨ effAddr i.toNat arg + v.type.width / 8 < mi.bytes.size)
    (hc : leBytesV (v.type.width / 8) v.bits.toNat =
      ((bytesV mi.bytes).drop (effAddr i.toNat arg)).take (v.type.width / 8))
    {a' : Admin} (ha' : adminToV a' = .case "CONST" (.tuple [Encode.toValue v.type, numV v]))
    (hc' : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain p]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain p]⟩)
      (adminsToV ([a'])) := by
  have hs := sread_loadNumVal St M Bf (State.hasReadRules_simEnv B).loadNumVal
    (State.typedV_state T hc') x.value.isLt (memAt_of_mem? hn hm) (memInstV_BYTES' mi)
    (sliceAt_of_or hT hle) hc
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  show SRead _ (cfgV _ [_, instrToV p]) [adminToV a']
  rw [hp, ha']
  exact hs

/-- `fwd_loadPack`, before the lift. -/
theorem sreadL_loadPack {P : Silmaril.Wasm.Numerics.Profile} (hF : Floats.FloatB P B)
    {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width}
    {ma : Nat} {mi : MemInst} (y : BitVec sz.width) (r : BitVec t.width)
    (hr : r = match sx with | .signed => y.signExtend t.width | .unsigned => y.setWidth t.width)
    (hm : s.mem? f x = some (ma, mi)) (hle : effAddr i.toNat arg + sz.width / 8 ≤ mi.bytes.size)
    (hT : SliceTotal ∨ effAddr i.toNat arg + sz.width / 8 < mi.bytes.size)
    (hc : leBytesV (sz.width / 8) y.toNat =
      ((bytesV mi.bytes).drop (effAddr i.toNat arg)).take (sz.width / 8))
    (hc' : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩)
      (adminsToV ([.plain (.intConst t r)])) := by
  have hs := sread_loadPackVal (r := pctV r.toNat) St M Bf
    (State.hasReadRules_simEnv B).loadPackVal (State.typedV_state T hc') x.value.isLt
    (memAt_of_mem? hn hm) (memInstV_BYTES' mi) y.isLt (sliceAt_of_or hT hle) hc
    (fun σ hd hN hI hS hC => by
      subst hr
      exact evalExp_callE_iff.2 (Floats.callDef_floatPrim hF (noClauses_extend B) (hd _)
        (evalArgs_cons (Sim.evalExp_var hN) (evalArgs_cons (evalExp_sizeInn hd hI)
          (evalArgs_cons (Sim.evalExp_var hS) (evalArgs_cons (Sim.evalExp_var hC) evalArgs_nil))))
        (Floats.floatCall_extend P sz.width t.width sx y)))
  rw [State.configV_eq]
  simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
  exact hs

/-- `FwdMem.fwd_loadIntVal`, before the lift. -/
theorem sreadL_loadIntVal {s : Store H} {f : Frame} {t : IntType} {x : MemIdx} {arg : MemArg}
    {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    {c : BitVec (8 * (t.width / 8))}
    (hT : SliceTotal ∨ effAddr i.toNat arg + t.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) =
      some c)
    (hc' : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t none x arg)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.intLoad t none x arg)]⟩)
      (adminsToV [.plain (.intConst t (c.setWidth t.width))]) := by
  obtain ⟨hle, hb⟩ := load_bytesV hl
  refine sreadL_loadNum B T St M Bf (v := ⟨.int t, c.setWidth t.width⟩) rfl hm hle hT ?_ rfl hc'
  show leBytesV (t.width / 8) (c.setWidth t.width).toNat = _
  rw [toNat_setWidth_of_le c (by rw [width8_int]), hb]
  rfl

/-- `FwdMem.fwd_loadFloatVal`, before the lift. -/
theorem sreadL_loadFloatVal {s : Store H} {f : Frame} {t : FloatType} {x : MemIdx}
    {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    {c : BitVec (8 * (t.width / 8))}
    (hT : SliceTotal ∨ effAddr i.toNat arg + t.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (t.width / 8) =
      some c)
    (hc' : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.floatLoad t x arg)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.floatLoad t x arg)]⟩)
      (adminsToV [.plain (.floatConst t (c.setWidth t.width))]) := by
  obtain ⟨hle, hb⟩ := load_bytesV hl
  refine sreadL_loadNum B T St M Bf (v := ⟨.float t, c.setWidth t.width⟩) rfl hm hle hT ?_ rfl
    hc'
  show leBytesV (t.width / 8) (c.setWidth t.width).toNat = _
  rw [toNat_setWidth_of_le c (by rw [width8_float]), hb]
  rfl

/-- `FwdMem.fwd_loadPackVal`, before the lift. -/
theorem sreadL_loadPackVal {P : Silmaril.Wasm.Numerics.Profile} (hF : Floats.FloatB P B)
    {s : Store H} {f : Frame} {t : IntType} {sz : PackSize}
    {sx : Signedness} {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width}
    {ma : Nat} {mi : MemInst} {c : BitVec (8 * (sz.width / 8))}
    (hT : SliceTotal ∨ effAddr i.toNat arg + sz.width / 8 < mi.bytes.size)
    (hm : s.mem? f x = some (ma, mi))
    (hl : Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg) (sz.width / 8) =
      some c)
    (hc' : Typed (simEnv B) hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [aconst a i, .plain (.intLoad t (some (sz, sx)) x arg)]⟩)
      (adminsToV [.plain (.intConst t (match (generalizing := false) sx with
        | .signed => c.signExtend t.width
        | .unsigned => c.setWidth t.width))]) := by
  obtain ⟨hle, hb⟩ := load_bytesV hl
  cases sz
  · exact sreadL_loadPack (sz := .i8) B T St M Bf hF c _ rfl hm hle hT hb hc'
  · exact sreadL_loadPack (sz := .i16) B T St M Bf hF c _ rfl hm hle hT hb hc'
  · exact sreadL_loadPack (sz := .i32) B T St M Bf hF c _ rfl hm hle hT hb hc'
  · exact sreadL_loadPack (sz := .i64) B T St M Bf hF c _ rfl hm hle hT hb hc'

end FwdMem

/-! ## The memory rules of `Step_read` at `BI` -/

section Dispatch

open Round4Int (BI)

variable {P : Numerics.Profile} (hn : H → String) (host : HostSemantics H)

/-- A code whose last instruction fails `p` is not `LastIs p`. -/
theorem not_lastIsM {p : Instr → Bool} {is : List Admin} {j : Instr}
    (h : is.getLast? = some (.plain j)) (hj : p j = false) : ¬ LastIs p is := by
  rintro ⟨i, hi, hp⟩
  have hij : Admin.plain i = Admin.plain j := Option.some.inj (hi.symm.trans h)
  have hij' : i = j := Admin.plain.inj hij
  rw [hij', hj] at hp
  exact Bool.false_ne_true hp

/-- **The memory rules of `Step_read`** at `BI`: every `MemoryStep` whose instruction is a
`Step_read` instruction, from a typed configuration bounded 's sense, is a
`Step_read` fact (`Round5.Fwd.fwd_memory5` before the lift). -/
theorem sread_of_memStep {c c' : Config H} (h : MemoryStep P c c')
    (hl : LastIs memReadInstr c.code) (hb : Round4.Bounded c)
    (hc : Typed (simEnv (BI P hn host)) hn c) :
    SRead (simEnv (BI P hn host)) (configV hn c) (adminsToV c'.code) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have St : State.StateTyping (simEnv (BI P hn host)) := Typing.stateTyping_simEnv _
  have Mt : Memory.MemTyping (simEnv (BI P hn host)) := ConfigOk.memTyping_simEnv _
  have Bf : FwdMem.BytesFuns (simEnv (BI P hn host)) := FwdMem.bytesFuns_builtins P hn host
  have hF : Floats.FloatB P (BI P hn host) := Prims.floatB_builtins hn host
  have hT' : FwdMem.SliceTotal := FwdMem.sliceTotal
  have hs : Integrate.StoreOk c.store := hb.store
  have hx : (∃ i, Admin.plain i ∈ c.code ∧ R4Fwd.VecMemI i = true) → False :=
    fun ⟨_, hi, hv⟩ => Round5.Fwd.not_vecMem hb.code hi hv
  cases h with
  | loadIntOob hm h₁ => exact sreadL_loadIntOob _ T St Mt hm h₁ hc
  | loadIntVal hm hl' => exact sreadL_loadIntVal _ T St Mt Bf (.inl hT') hm hl' hc
  | loadPackOob hm h₁ => exact sreadL_loadPackOob _ T St Mt hm h₁ hc
  | loadPackVal hm hl' => exact sreadL_loadPackVal _ T St Mt Bf hF (.inl hT') hm hl' hc
  | loadFloatOob hm h₁ => exact sreadL_loadFloatOob _ T St Mt hm h₁ hc
  | loadFloatVal hm hl' => exact sreadL_loadFloatVal _ T St Mt Bf (.inl hT') hm hl' hc
  | storeIntOob _ _ => exact absurd hl (not_lastIsM rfl rfl)
  | storeIntVal _ _ => exact absurd hl (not_lastIsM rfl rfl)
  | storePackOob _ _ => exact absurd hl (not_lastIsM rfl rfl)
  | storePackVal _ _ => exact absurd hl (not_lastIsM rfl rfl)
  | storeFloatOob _ _ => exact absurd hl (not_lastIsM rfl rfl)
  | storeFloatVal _ _ => exact absurd hl (not_lastIsM rfl rfl)
  | size hm =>
    exact sreadL_memorySize _ T St Mt hm (hs.mem hm).1 (Integrate.pages_lt (hs.mem hm).2 _) hc
  | growSucceed _ _ _ => exact absurd hl (not_lastIsM rfl rfl)
  | growFail _ _ => exact absurd hl (not_lastIsM rfl rfl)
  | fillOob hm h₁ => exact sreadL_memoryFillOob _ T St hm h₁ hc
  | fillZero hm h₁ => exact sreadL_memoryFillZero _ T St hm h₁ hc
  | @fillSucc s f x a i n v ma mi hm h₁ hnz =>
    exact sreadL_memoryFillSucc _ T St hm h₁ hnz (Integrate.succ_lt a hnz h₁ (hs.mem hm).2) hc
  | copyOob h₁ h₂ h₃ => exact sreadL_memoryCopyOob _ T St h₁ h₂ h₃ hc
  | copyZero h₁ h₂ h₃ => exact sreadL_memoryCopyZero _ T St h₁ h₂ h₃ hc
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hle =>
    exact sreadL_memoryCopyLe _ T St h₁ h₂ h₃ hnz hle
      ⟨Integrate.succ_lt a₁ hnz h₃.1 (hs.mem h₁).2, Integrate.succ_lt a₂ hnz h₃.2 (hs.mem h₂).2⟩ hc
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hgt =>
    exact sreadL_memoryCopyGt _ T St h₁ h₂ h₃ hnz hgt
      ⟨Integrate.add_le_pow a₁ h₃.1 (hs.mem h₁).2, Integrate.add_le_pow a₂ h₃.2 (hs.mem h₂).2⟩ hc
  | initOob hm hd h₁ => exact sreadL_memoryInitOob _ T St hm hd h₁ hc
  | initZero hm hd h₁ => exact sreadL_memoryInitZero _ T St hm hd h₁ hc
  | @initSucc s f x y a i j n ma da mi di byte hm hd h₁ hnz hby =>
    exact sreadL_memoryInitSucc _ T St hm hd h₁ hnz hby
      ⟨Integrate.succ_lt a hnz h₁.1 (hs.mem hm).2, Integrate.succ_lt .i32 hnz h₁.2 (hs.data hd)⟩ hc
  | dataDrop _ => exact absurd hl (not_lastIsM rfl rfl)
  | _ => exact (hx (by simp [R4Fwd.VecMemI, aconst])).elim

end Dispatch

end Silmaril.Wasm.SpecTec.Institution.FwdX30

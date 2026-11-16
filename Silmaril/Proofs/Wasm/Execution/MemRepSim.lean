module

public import Silmaril.Wasm.Execution.MemRep.Sim.Defs
public import Silmaril.Wasm.Execution.MemRep.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.Memory

/-! Proofs for `Silmaril.Wasm.Execution.MemRep.Sim.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Execution.MemRepSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded.Exec
  Silmaril.Wasm.SingleThreaded.Exec.Mem Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

variable {H R : Type} [MemRep R] [LawfulMemRep R]

/-! ## Store access and update -/

omit [LawfulMemRep R] in
theorem mem?_toBytes (s : Store H R) (f : Frame) (x : MemIdx) :
    s.toBytes.mem? f x = (s.mem? f x).map (fun p => (p.1, p.2.toBytes)) := by
  simp only [Store.mem?, Store.toBytes, bind, Option.bind, List.getElem?_map]
  cases f.module.mems[x.toNat]? with
  | none => rfl
  | some a => dsimp only; cases s.mems[a]? <;> rfl

omit [LawfulMemRep R] in
theorem data?_toBytes (s : Store H R) (f : Frame) (y : DataIdx) :
    s.toBytes.data? f y = s.data? f y := rfl

omit [LawfulMemRep R] in
theorem setMem_toBytes (s : Store H R) (a : Nat) (mi : MemInst R) :
    (s.setMem a mi).toBytes = s.toBytes.setMem a mi.toBytes := by
  simp [Store.setMem, Store.toBytes, List.map_set]

omit [LawfulMemRep R] in
theorem setData_toBytes (s : Store H R) (a : Nat) (b : ByteArray) :
    (s.setData a b).toBytes = s.toBytes.setData a b := rfl

theorem pages_toBytes (mi : MemInst R) : mi.toBytes.pages = mi.pagesR := by
  simp [MemInst.pages, MemInst.pagesR, MemInst.toBytes, LawfulMemRep.size_eq]

theorem growR?_toBytes (mi : MemInst R) (n : Nat) :
    (mi.growR? n).map MemInst.toBytes = mi.toBytes.growR? n := by
  unfold MemInst.growR?
  rw [show MemRep.size (R := ByteArray) mi.toBytes.bytes = MemRep.size mi.bytes from
    (LawfulMemRep.size_eq _).symm]
  dsimp only [MemInst.toBytes]
  rw [apply_ite (Option.map MemInst.toBytes)]
  congr 1
  simp [MemInst.toBytes, LawfulMemRep.extend_eq]

theorem grow?_toBytes (mi : MemInst R) (n : Nat) :
    (mi.growR? n).map MemInst.toBytes = mi.toBytes.grow? n := by
  rw [growR?_toBytes, MemInst.growR?_byteArray]

/-! ## The memory-family instructions -/

section Instrs

variable (s : Store H R) (f : Frame) (args : List Val)

set_option hygiene false in
/-- Close a load: the representation's load is the specification's load of `toBytes`. -/
local macro "load_close" : tactic => `(tactic| (
  simp only [Option.map, MemInst.toBytes, MemRep.load_byteArray, ← LawfulMemRep.load_eq]
  cases MemRep.load mi.bytes _ _ <;> rfl))

set_option hygiene false in
/-- Close a store: the representation's store maps to the specification's store of `toBytes`. -/
local macro "store_close" : tactic => `(tactic| (
  simp only [MemInst.toBytes, MemRep.store_byteArray]
  split <;> rename_i hst <;>
  · have h2 := congrArg (Option.map MemRep.toBytes) hst
    rw [LawfulMemRep.store_eq] at h2
    simp only [h2, Option.map_some, Option.map_none]
    try simp [Config.toBytes, setMem_toBytes, MemInst.toBytes]))

theorem loadInt_toBytes (t x arg) :
    (loadInt s f t x arg args).map Config.toBytes = loadInt s.toBytes f t x arg args := by
  unfold loadInt
  rcases args with _ | ⟨v, _ | _⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  load_close

theorem loadPack_toBytes (t sz sx x arg) :
    (loadPack s f t sz sx x arg args).map Config.toBytes =
      loadPack s.toBytes f t sz sx x arg args := by
  unfold loadPack
  rcases args with _ | ⟨v, _ | _⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  load_close

theorem loadFloat_toBytes (t x arg) :
    (loadFloat s f t x arg args).map Config.toBytes = loadFloat s.toBytes f t x arg args := by
  unfold loadFloat
  rcases args with _ | ⟨v, _ | _⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  load_close

theorem vecLoad_toBytes (op x arg) :
    (vecLoad s f op x arg args).map Config.toBytes = vecLoad s.toBytes f op x arg args := by
  unfold vecLoad
  rcases args with _ | ⟨v, _ | _⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  load_close

theorem vecLoadLane_toBytes (sz x arg j) :
    (vecLoadLane s f sz x arg j args).map Config.toBytes =
      vecLoadLane s.toBytes f sz x arg j args := by
  unfold vecLoadLane
  rcases args with _ | ⟨v, _ | ⟨w, _ | _⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases vecOf? w with _ | c <;>
    rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  load_close

theorem storeInt_toBytes (t x arg) :
    (storeInt s f t x arg args).map Config.toBytes = storeInt s.toBytes f t x arg args := by
  unfold storeInt
  rcases args with _ | ⟨v, _ | ⟨w, _ | _⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases intOf? t w with _ | c <;>
    rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  store_close

theorem storePack_toBytes (t sz x arg) :
    (storePack s f t sz x arg args).map Config.toBytes = storePack s.toBytes f t sz x arg args := by
  unfold storePack
  rcases args with _ | ⟨v, _ | ⟨w, _ | _⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases intOf? t w with _ | c <;>
    rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  store_close

theorem storeFloat_toBytes (t x arg) :
    (storeFloat s f t x arg args).map Config.toBytes = storeFloat s.toBytes f t x arg args := by
  unfold storeFloat
  rcases args with _ | ⟨v, _ | ⟨w, _ | _⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases floatOf? t w with _ | c <;>
    rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  store_close

theorem vecStore_toBytes (x arg) :
    (vecStore s f x arg args).map Config.toBytes = vecStore s.toBytes f x arg args := by
  unfold vecStore
  rcases args with _ | ⟨v, _ | ⟨w, _ | _⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases vecOf? w with _ | c <;>
    rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  store_close

theorem vecStoreLane_toBytes (sz x arg j) :
    (vecStoreLane s f sz x arg j args).map Config.toBytes =
      vecStoreLane s.toBytes f sz x arg j args := by
  unfold vecStoreLane
  rcases args with _ | ⟨v, _ | ⟨w, _ | _⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases vecOf? w with _ | c <;>
    rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  store_close

theorem memSize_toBytes (x) :
    (memSize s f x args).map Config.toBytes = memSize s.toBytes f x args := by
  unfold memSize
  rcases args with _ | _ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  simp only [Option.map_some, Config.toBytes, ← pages_toBytes]
  rfl

omit [LawfulMemRep R] in
theorem dataDrop_toBytes (y) :
    (dataDrop s f y args).map Config.toBytes = dataDrop s.toBytes f y args := by
  unfold dataDrop
  rcases args with _ | _ <;> try rfl
  dsimp only; rw [data?_toBytes]
  rcases s.data? f y with _ | ⟨da, di⟩ <;> rfl

theorem memFill_toBytes (x) :
    (memFill s f x args).map Config.toBytes = memFill s.toBytes f x args := by
  unfold memFill
  rcases args with _ | ⟨v₁, _ | ⟨v, _ | ⟨v₃, _ | _⟩⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v₁ with _ | ⟨a, i⟩ <;> rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  simp only [Option.map_some]
  rcases intOf? a.intType v₃ with _ | n <;> try rfl
  simp only [MemInst.toBytes, MemRep.size_byteArray, ← LawfulMemRep.size_eq]
  split_ifs <;> rfl

theorem memCopy_toBytes (x₁ x₂) :
    (memCopy s f x₁ x₂ args).map Config.toBytes = memCopy s.toBytes f x₁ x₂ args := by
  unfold memCopy
  rcases args with _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, _ | _⟩⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes, mem?_toBytes]
  rcases addrOf? v₁ with _ | ⟨a₁, i₁⟩ <;> rcases addrOf? v₂ with _ | ⟨a₂, i₂⟩ <;>
    rcases addrOf? v₃ with _ | ⟨a', n⟩ <;> rcases s.mem? f x₁ with _ | ⟨ma₁, mi₁⟩ <;>
    rcases s.mem? f x₂ with _ | ⟨ma₂, mi₂⟩ <;> try rfl
  simp only [Option.map_some, MemInst.toBytes, MemRep.size_byteArray, ← LawfulMemRep.size_eq]
  split_ifs <;> rfl

theorem memInit_toBytes (x y) :
    (memInit s f x y args).map Config.toBytes = memInit s.toBytes f x y args := by
  unfold memInit
  rcases args with _ | ⟨v₁, _ | ⟨v₂, _ | ⟨v₃, _ | _⟩⟩⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes, data?_toBytes]
  rcases addrOf? v₁ with _ | ⟨a, i⟩ <;> rcases i32Of? v₂ with _ | j <;>
    rcases i32Of? v₃ with _ | n <;> rcases s.mem? f x with _ | ⟨ma, mi⟩ <;>
    rcases s.data? f y with _ | ⟨da, di⟩ <;> try rfl
  simp only [Option.map_some, MemInst.toBytes, MemRep.size_byteArray, ← LawfulMemRep.size_eq]
  split_ifs <;> try rfl
  cases di.bytes.data[j.toNat]? <;> rfl

theorem memGrow_toBytes (o x) :
    (memGrow s f o x args).map Config.toBytes = memGrow s.toBytes f o x args := by
  unfold memGrow
  rcases args with _ | ⟨v, _ | _⟩ <;> try rfl
  dsimp only; rw [mem?_toBytes]
  rcases addrOf? v with _ | ⟨_, i⟩ <;> rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> try rfl
  simp only [Option.map, pages_toBytes, MemInst.pagesR_byteArray,
    MemInst.growR?_byteArray, ← grow?_toBytes]
  by_cases hg : (profile o).growMayFail .memory ma mi.pagesR i.toNat
  · rw [ite_eq_left hg, ite_eq_left hg]; rfl
  · rw [ite_eq_right hg, ite_eq_right hg]
    cases mi.growR? i.toNat <;> simp [Config.toBytes, setMem_toBytes]

theorem stepArgs_toBytes (o e) :
    (stepArgs o s f args e).map Config.toBytes = stepArgs o s.toBytes f args e := by
  unfold stepArgs
  split
  · exact loadInt_toBytes ..
  · exact loadPack_toBytes ..
  · exact loadFloat_toBytes ..
  · exact vecLoad_toBytes ..
  · exact vecLoadLane_toBytes ..
  · exact storeInt_toBytes ..
  · exact storePack_toBytes ..
  · exact storeFloat_toBytes ..
  · exact vecStore_toBytes ..
  · exact vecStoreLane_toBytes ..
  · exact memSize_toBytes ..
  · exact memGrow_toBytes ..
  · exact memFill_toBytes ..
  · exact memCopy_toBytes ..
  · exact memInit_toBytes ..
  · exact dataDrop_toBytes ..
  · rfl

end Instrs

theorem memoryStep?_toBytes (o : GrowOracle) (s : Store H R) (f : Frame) (vs : List Val)
    (e : Admin) :
    (memoryStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      memoryStep? o s.toBytes f vs e := by
  unfold memoryStep?
  split
  · split
    · rw [← stepArgs_toBytes, Option.map_map, Option.map_map]; rfl
    · rfl
  · rfl

end Silmaril.Proofs.Wasm.Execution.MemRepSim

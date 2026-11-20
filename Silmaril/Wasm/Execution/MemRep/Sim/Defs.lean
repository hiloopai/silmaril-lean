module

public import Silmaril.Wasm.Execution.Core.MemRep

/-! # Reading a store over a memory representation as a specification store

`MemInst.toBytes`, `Store.toBytes` and `Config.toBytes` replace every memory held in a
representation `R` by the `ByteArray` it stands for (`MemRep.toBytes`); nothing else changes.
`Execution.MemRep.Sim.Thms` shows that the memory-family interpreter step commutes with this
map at a lawful `R`.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core

variable {H R : Type} [MemRep R]

/-- The specification memory instance a represented one stands for. -/
def MemInst.toBytes (mi : MemInst R) : MemInst := ⟨mi.type, MemRep.toBytes mi.bytes⟩

/-- The specification store: every memory read through `MemRep.toBytes`. -/
def Store.toBytes (s : Store H R) : Store H :=
  ⟨s.tags, s.globals, s.mems.map MemInst.toBytes, s.tables, s.funcs, s.datas, s.elems,
    s.structs, s.arrays, s.exns⟩

/-- The specification configuration: the store read through `Store.toBytes`. -/
def Config.toBytes (c : Config H R) : Config H := ⟨c.store.toBytes, c.frame, c.code⟩

end Silmaril.Wasm.Execution.Core

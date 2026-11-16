module

public import Silmaril.Wasm.Component.Reference.Machine.Transfer.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
import Silmaril.Proofs.Wasm.Component.Reference.TransferCanon

/-!
# Memory access of the canonical ABI across engines (pilot)

The first per-definition obligations of `Machine.Transfer`: the `Canon.Context` programs that
read or write the core store are related to themselves by `ProgRel S` for every store
simulation `S : E.StoreSim I`. The proofs use only the memory laws of `S`.

* `rel_ptrType`, `rel_memLen`, `rel_readMem`, `rel_writeMem`;
* `writeMemSt_mapStore`: the store update of `writeMem` commutes with `mapStore S`.

The other core-store accesses of REF programs are `threadNewIndirect`
(`Canon.Builtins.Thread`) and the instantiation helpers `setCoreSt`, `allocHostSt`,
`addrTypesOf`, `allocCoreHost` and `instantiateCore` (`Instantiate`). Every other REF program
reads and writes only fields other than `core`, which `mapStore S` keeps.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine.Transfer

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I) {σ : Type}

theorem rel_ptrType (cx : LiftLowerContext E) :
    ProgRel S (ptrType cx : P (E.withStore I) σ Silmaril.Wasm.AddrType) (ptrType cx) :=
  Silmaril.Proofs.Wasm.Component.Reference.TransferCanon.rel_ptrType S cx

theorem rel_memLen (cx : LiftLowerContext E) :
    ProgRel S (memLen cx : P (E.withStore I) σ Nat) (memLen cx) :=
  Silmaril.Proofs.Wasm.Component.Reference.TransferCanon.rel_memLen S cx

theorem rel_readMem (cx : LiftLowerContext E) (ptr len : Nat) :
    ProgRel S (readMem cx ptr len : P (E.withStore I) σ ByteArray) (readMem cx ptr len) :=
  Silmaril.Proofs.Wasm.Component.Reference.TransferCanon.rel_readMem S cx ptr len

theorem writeMemSt_mapStore (m : E.MemAddr) (ptr : Nat) (bytes : ByteArray)
    (s : CStore (E.withStore I)) :
    mapStore S (writeMemSt m ptr bytes s) = writeMemSt m ptr bytes (mapStore S s) :=
  Silmaril.Proofs.Wasm.Component.Reference.TransferCanon.writeMemSt_mapStore S m ptr bytes s

theorem rel_writeMem (cx : LiftLowerContext E) (ptr : Nat) (bytes : ByteArray) :
    ProgRel S (writeMem cx ptr bytes : P (E.withStore I) σ Unit) (writeMem cx ptr bytes) :=
  Silmaril.Proofs.Wasm.Component.Reference.TransferCanon.rel_writeMem S cx ptr bytes

end Silmaril.Wasm.Component.Machine.Transfer

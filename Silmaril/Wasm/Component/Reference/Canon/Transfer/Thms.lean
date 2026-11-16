module

public import Silmaril.Wasm.Component.Reference.Machine.Transfer.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs

/-!
# Memory access of the canonical ABI across engines

The `Canon.Context` programs that read or write core memory (`ptrType`, `memLen`, `readMem`,
`writeMem`) are related to themselves by `ProgRel S` for every store simulation
`S : E.StoreSim I`. They reach the core store only through `Op.readCore` and `Op.memWrite`, so
the program over `E.withStore I` is the program over `E` (`ProgRel.refl`); the machine's answers
to those operations are related by the memory laws of `S` (`Machine.Transfer.step_sim`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine.Transfer

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I) {σ : Type}

theorem rel_ptrType (cx : LiftLowerContext E) :
    ProgRel S (ptrType cx : P (E.withStore I) σ Silmaril.Wasm.AddrType) (ptrType cx) :=
  by prog_rel_refl

theorem rel_memLen (cx : LiftLowerContext E) :
    ProgRel S (memLen cx : P (E.withStore I) σ Nat) (memLen cx) :=
  by prog_rel_refl

theorem rel_readMem (cx : LiftLowerContext E) (ptr len : Nat) :
    ProgRel S (readMem cx ptr len : P (E.withStore I) σ ByteArray) (readMem cx ptr len) :=
  by prog_rel_refl

theorem rel_writeMem (cx : LiftLowerContext E) (ptr : Nat) (bytes : ByteArray) :
    ProgRel S (writeMem cx ptr bytes : P (E.withStore I) σ Unit) (writeMem cx ptr bytes) :=
  by prog_rel_refl

end Silmaril.Wasm.Component.Machine.Transfer

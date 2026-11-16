module

public import Silmaril.Wasm.Component.Reference.Machine.Transfer.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.Transfer

/-!
# Proofs: memory access of the canonical ABI is related across engines

The pilot of the per-definition obligations of `Machine.Transfer`: the programs of
`Canon.Context` that read or write the core store (`ptrType`, `memLen`, `readMem`, `writeMem`)
are related to themselves by `ProgRel S`, from the memory laws of the store simulation
(`StoreSim.memAddrType?`, `memSize?`, `memRead?`, `memWrite?`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.TransferCanon

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine.Transfer

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I) {σ α : Type}

theorem mapStore_core (s : CStore (E.withStore I)) : (mapStore S s).core = S.φ s.core := rfl

theorem rel_trap (r : TrapReason) :
    ProgRel S (trap r : P (E.withStore I) σ α) (trap r) := .trap r _ _

theorem rel_orTrap (r : TrapReason) (o : Option α) :
    ProgRel S (orTrap r o : P (E.withStore I) σ α) (orTrap r o) := by
  cases o
  · exact rel_trap S r
  · exact .pure _

theorem rel_gets {f' : CStore (E.withStore I) → α} {f : CStore E → α}
    (h : ∀ s, f' s = f (mapStore S s)) : ProgRel S (gets f' : P (E.withStore I) σ α) (gets f) :=
  .get fun s => by
    show ProgRel S (Pure.pure (f' s)) (Pure.pure (f (mapStore S s)))
    rw [h]
    exact .pure _

theorem ptrTypeIn_mapStore (s : CStore (E.withStore I)) (cx : LiftLowerContext E) :
    ptrTypeIn (mapStore S s) cx = ptrTypeIn s cx := by
  have e : (fun m => (E.memAddrType? (S.φ s.core) m).getD Silmaril.Wasm.AddrType.i32) =
      fun m => (I.memAddrType? s.core m).getD Silmaril.Wasm.AddrType.i32 :=
    funext fun m => by rw [S.memAddrType?]
  show cx.opts.ptrType (fun m => (E.memAddrType? (S.φ s.core) m).getD Silmaril.Wasm.AddrType.i32) = _
  rw [e]
  kernel_rfl

theorem rel_ptrType (cx : LiftLowerContext E) :
    ProgRel S (ptrType cx : P (E.withStore I) σ Silmaril.Wasm.AddrType) (ptrType cx) :=
  rel_gets S (f' := (ptrTypeIn · cx)) (f := (ptrTypeIn · cx)) fun s =>
    (ptrTypeIn_mapStore S s cx).symm

theorem rel_memAddr (cx : LiftLowerContext E) :
    ProgRel S (memAddr cx : P (E.withStore I) σ E.MemAddr) (memAddr cx) :=
  rel_orTrap S _ _

theorem rel_memLen (cx : LiftLowerContext E) :
    ProgRel S (memLen cx : P (E.withStore I) σ Nat) (memLen cx) := by
  refine ProgRel.bind S (rel_memAddr S cx) fun m => rel_getStore_bind S fun s => ?_
  dsimp only [CoreEngine.withStore]
  rw [mapStore_core, S.memSize?]
  exact rel_orTrap S _ _

theorem rel_readMem (cx : LiftLowerContext E) (ptr len : Nat) :
    ProgRel S (readMem cx ptr len : P (E.withStore I) σ ByteArray) (readMem cx ptr len) := by
  refine ProgRel.bind S (rel_memAddr S cx) fun m => rel_getStore_bind S fun s => ?_
  dsimp only [CoreEngine.withStore]
  rw [mapStore_core, S.memRead?]
  exact rel_orTrap S _ _

theorem writeMemSt_mapStore (m : E.MemAddr) (ptr : Nat) (bytes : ByteArray)
    (s : CStore (E.withStore I)) :
    mapStore S (writeMemSt m ptr bytes s) = writeMemSt m ptr bytes (mapStore S s) := by
  unfold writeMemSt
  dsimp only [CoreEngine.withStore]
  rw [mapStore_core, S.memWrite?]
  cases I.memWrite? s.core m ptr bytes <;> rfl

theorem rel_writeMem (cx : LiftLowerContext E) (ptr : Nat) (bytes : ByteArray) :
    ProgRel S (writeMem cx ptr bytes : P (E.withStore I) σ Unit) (writeMem cx ptr bytes) := by
  refine ProgRel.bind S (rel_memAddr S cx) fun m => rel_getStore_bind S fun s => ?_
  dsimp only [CoreEngine.withStore]
  rw [mapStore_core, S.memWrite?]
  cases I.memWrite? s.core m ptr bytes
  · exact rel_trap S _
  · exact .modify (fun s => writeMemSt_mapStore S m ptr bytes s) (.pure ())

end Silmaril.Proofs.Wasm.Component.Reference.TransferCanon

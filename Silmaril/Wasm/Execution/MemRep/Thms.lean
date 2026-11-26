module

public import Silmaril.Wasm.Execution.MemRep.Defs
import Silmaril.Proofs.Wasm.Execution.MemRep

/-! # Memory representations behind laws: the lawful instances

* `ByteArray` is lawful: it is the specification (`toBytes = id`).
* `KMem` (well-formed `KBytes`) is lawful: `KMem.load_eq`, `KMem.store_eq`,
  `KMem.readBytes_eq`, `KMem.writeBytes_eq`, `KMem.grow_eq`, `KMem.zeros_eq`. The two digit
  lemmas are `decodeLE_eq` (`Memory.decodeLE b = KBytes.leVal b.data.toList`) and
  `encodeLE_toList` (`(Memory.encodeLE n v).data.toList = KBytes.unpack n v`).
-/

@[expose] public section

namespace Silmaril.Wasm.Execution

open Silmaril.Proofs.Wasm.Execution.MemRep

theorem decodeLE_eq (b : ByteArray) : Memory.decodeLE b = Silmaril.KBytes.leVal b.data.toList :=
  Silmaril.Proofs.Wasm.Execution.MemRep.decodeLE_eq b

theorem encodeLE_toList (n v : Nat) :
    (Memory.encodeLE n v).data.toList = Silmaril.KBytes.unpack n v :=
  Silmaril.Proofs.Wasm.Execution.MemRep.encodeLE_toList n v

instance : LawfulMemRep ByteArray where
  size_eq _ := rfl
  load_eq _ _ _ := rfl
  store_eq _ _ _ _ := Option.map_id'
  readBytes_eq _ _ _ := rfl
  writeBytes_eq _ _ _ := Option.map_id'
  grow_eq _ _ _ := Option.map_id'
  zeros_eq n := by simp [MemRep.toBytes, MemRep.zeros]

namespace KMem

theorem load_eq (m : KMem) (a count : Nat) : m.load a count = Memory.load m.toBytes a count :=
  Silmaril.Proofs.Wasm.Execution.MemRep.load_eq m a count
theorem store_eq (m : KMem) (a : Nat) {count : Nat} (w : BitVec (8 * count)) :
    (m.store a w).map toBytes = Memory.store m.toBytes a w :=
  Silmaril.Proofs.Wasm.Execution.MemRep.store_eq m a w
theorem readBytes_eq (m : KMem) (a count : Nat) :
    m.readBytes a count = Memory.readBytes m.toBytes a count :=
  Silmaril.Proofs.Wasm.Execution.MemRep.readBytes_eq m a count
theorem writeBytes_eq (m : KMem) (a : Nat) (bs : ByteArray) :
    (m.writeBytes a bs).map toBytes = Memory.writeBytes m.toBytes a bs :=
  Silmaril.Proofs.Wasm.Execution.MemRep.writeBytes_eq m a bs
theorem grow_eq (m : KMem) (maximum : Option Nat) (delta : Nat) :
    (m.grow? maximum delta).map toBytes = Memory.grow? m.toBytes maximum delta :=
  Silmaril.Proofs.Wasm.Execution.MemRep.grow_eq m maximum delta
theorem zeros_eq (n : Nat) : (zeros n).toBytes.data.toList = List.replicate n 0 :=
  Silmaril.Proofs.Wasm.Execution.MemRep.zeros_eq n

end KMem

instance : LawfulMemRep KMem where
  size_eq m := (Silmaril.Proofs.Wasm.Execution.MemRep.size_toBytes m).symm
  load_eq := KMem.load_eq
  store_eq m a _ w := KMem.store_eq m a w
  readBytes_eq := KMem.readBytes_eq
  writeBytes_eq := KMem.writeBytes_eq
  grow_eq := KMem.grow_eq
  zeros_eq := KMem.zeros_eq

end Silmaril.Wasm.Execution

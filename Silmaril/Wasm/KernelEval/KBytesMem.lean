module

public import Silmaril.Wasm.KernelEval.Memories
public import Silmaril.Prelude.Bytes.Defs

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: `Silmaril.KBytes` as Wasm memory

`Silmaril.KBytes` (`Silmaril.Prelude.Bytes`) is the shared kernel byte string: a length-cached
binary tree of leaves, each packing up to 4 KiB into one natural number. It is read-only: its
interface reads (`readLE`), slices (`slice`) and concatenates (`++`). As Wasm memory:

* `KRope`: loads are `readLE`; a store is the rope
  `slice 0 a ++ leaf k v ++ slice (a + k) rest`, the store expressible with the published
  interface only. Slices share untouched subtrees, but every store adds nodes.
* `KPath`: loads are `readLE`; a store rewrites the leaves the window falls in and copies the
  path to them (`KBytes.writeLE` below, not part of the `KBytes` interface); the tree keeps its
  shape. A leaf is rewritten digit-wise (`%`, `/`, `*`, `+` on its number), so no condition on
  leaves is needed.

Both simulate the list reference under `toListMem` with the validity condition `wf`
(`Silmaril.Wasm.KernelEval.KBytesMemThms`). The zero memory is the canonical tree of
`4096`-byte zero leaves (`kzeros`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.KernelEval

open Silmaril

/-- Replace the `w` bytes at `off` by the `w` low bytes of `v`, copying the path to the
affected leaves (meaningful when `off + w ≤ len`). -/
def kwrite : KBytes → Nat → Nat → Nat → KBytes
  | .leaf n x, off, w, v =>
    .leaf n (x % 256 ^ off + 256 ^ off * (v % 256 ^ w + 256 ^ w * (x / 256 ^ (off + w))))
  | .node n l r, off, w, v =>
    if off + w ≤ l.len then .node n (kwrite l off w v) r
    else if l.len ≤ off then .node n l (kwrite r (off - l.len) w v)
    else .node n (kwrite l off (l.len - off) v)
      (kwrite r 0 (w - (l.len - off)) (v / 256 ^ (l.len - off)))

/-- `KBytes` with stores as ropes of slices. -/
structure KRope where
  t : KBytes

/-- `KBytes` with path-copying stores. -/
structure KPath where
  t : KBytes

instance : MemOps KRope where
  load m a k := m.t.readLE a k
  store m a k v :=
    if a + k ≤ m.t.len then
      some ⟨m.t.slice 0 a ++ .leaf k (v % 256 ^ k) ++ m.t.slice (a + k) (m.t.len - (a + k))⟩
    else none

instance : MemOps KPath where
  load m a k := m.t.readLE a k
  store m a k v := if a + k ≤ m.t.len then some ⟨kwrite m.t a k v⟩ else none

/-- `n` zero bytes, as the canonical tree of `4096`-byte leaves. -/
def kzeros (n : Nat) : KBytes := KBytes.ofChunks 4096 n (List.replicate ((n + 4095) / 4096) 0)

/-- The list memory of kernel bytes. -/
def kToListMem (t : KBytes) : ListMem := ⟨t.toList.map UInt8.toBitVec⟩

end Silmaril.Wasm.KernelEval

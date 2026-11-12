module

public import Silmaril.Wasm.Execution.Memory

/-!
# A linear-memory model for program proofs: definitions

Wasm linear memory is a `ByteArray`; `Memory.load`/`Memory.store` read and write
little-endian words at byte addresses, failing out of bounds. Program proofs talk
about **regions** (`Region`, a base and a length), their disjointness and bounds,
the bytes of a region (`bytesAt`), and the little-endian encodings of words
(`leNat`, `u32le`, `u64le`, `storeLE`). The access and separation lemmas are in
`Silmaril.Wasm.Logic.Memory.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm.Execution

/-! ## Regions -/

/-- The byte range `[base, base + len)`. -/
structure Region where
  base : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- The end of a region (exclusive). -/
def Region.stop (r : Region) : Nat := r.base + r.len

/-- Two regions share no byte. -/
def Region.Disjoint (r q : Region) : Prop := r.stop ≤ q.base ∨ q.stop ≤ r.base

/-- A region lies inside a memory of `B.size` bytes. -/
def Region.InBounds (r : Region) (B : ByteArray) : Prop := r.stop ≤ B.size

/-- `r` contains `q`. -/
def Region.Contains (r q : Region) : Prop := r.base ≤ q.base ∧ q.stop ≤ r.stop

/-- The bytes of `B` in the region `r` (truncated at the end of `B`). -/
def bytesAt (B : ByteArray) (r : Region) : List UInt8 := (B.data.toList.drop r.base).take r.len

/-- The little-endian value of a list of bytes. -/
def leNat (l : List UInt8) : Nat := l.foldr (fun b rest => b.toNat + 256 * rest) 0

/-- The four little-endian bytes of a `u32`. -/
def u32le (x : UInt32) : List UInt8 :=
  [UInt8.ofNat x.toNat, UInt8.ofNat (x.toNat / 2 ^ 8), UInt8.ofNat (x.toNat / 2 ^ 16),
    UInt8.ofNat (x.toNat / 2 ^ 24)]

/-- The eight little-endian bytes of a `u64`. -/
def u64le (x : UInt64) : List UInt8 :=
  (List.range 8).map fun k => UInt8.ofNat (x.toNat / 2 ^ (8 * k))

/-- The result of an in-bounds store. -/
def storeLE (B : ByteArray) (a n v : Nat) : ByteArray :=
  (Memory.encodeLE n v).copySlice 0 B a n

end Silmaril.Wasm.Logic.Core

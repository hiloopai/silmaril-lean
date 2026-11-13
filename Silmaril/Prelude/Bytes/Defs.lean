module

public import Init.Data.List.Basic
public import Init.Data.ByteArray.Basic
public import Silmaril.Prelude.Bytes.Digits.Thms

/-! # Kernel bytes (`Silmaril.KBytes`)

A byte string the Lean kernel can read quickly. `KBytes` is a binary tree. A leaf
`leaf n v` holds `n` bytes packed little-endian into one natural number `v` (byte `i` of the
leaf is `v / 256 ^ i % 256`). A node `node n l r` caches its length `n`, which must be
`l.len + r.len` (`wf`).

The kernel accelerates `Nat` arithmetic on literals with GMP (`+`, `-`, `*`, `/`, `%`, `^`,
`>>>`, `<<<`, `==`, `≤`). Every operation here is written so that the kernel does a few big-number
operations per leaf and one comparison per node:

* `read t off w` is the little-endian value of the `w` bytes at `off`. It descends the tree
  (one `≤` per level) and shifts the leaf. A read that straddles leaves combines the pieces with
  `<<<` and `+`. `readLE` is the `Option` form for the ELF and Wasm readers
  (`Nat → Nat → Option Nat`).
* `append` is one node (a rope); `slice` builds a rope that shares the untouched subtrees.
* `canon c t` rebuilds `t` as the canonical tree with `c`-byte leaves. Two canonical trees
  hold the same bytes iff they are the same term, so the kernel decides equality by
  `rfl` (`Eq.refl`), not by evaluation.

The **canonical form** with chunk size `c` (`ofChunks c n cs`) is left-balanced. A tree with
`k > 1` leaves puts the largest power of two strictly below `k` on the left. Each leaf holds
`min c remaining` bytes. Files are elaborated into this form with `c = 4096`
(`Silmaril.Prelude.Bytes.Elab`), the chunk size `include_bytes` uses.

`toList` is the specification. The theorems in `Silmaril.Prelude.Bytes.Thms` relate each
operation to it. Nothing here needs `Decidable` instances, native evaluation or a compiled
evaluator: a fact about kernel bytes is a `Bool` computation checked by `decide +kernel` (or a
registered native procedure, `Silmaril.Prelude.Trust`).
-/

@[expose] public section

namespace Silmaril

/-- Bytes as a length-cached binary tree of packed little-endian `Nat` leaves. -/
inductive KBytes where
  /-- `len` bytes; byte `i` is `val / 256 ^ i % 256`. -/
  | leaf (len val : Nat)
  /-- The bytes of `left` then `right`; `len` caches their total length (`wf`). -/
  | node (len : Nat) (left right : KBytes)
  deriving Inhabited

namespace KBytes

/-- The cached length. -/
def len : KBytes → Nat
  | leaf n _ => n
  | node n _ _ => n

/-- The bytes, in order. This is the specification of every operation. -/
def toList : KBytes → List UInt8
  | leaf n v => unpack n v
  | node _ l r => l.toList ++ r.toList

/-- The bytes as a `ByteArray`. -/
def toByteArray (t : KBytes) : ByteArray := ⟨⟨t.toList⟩⟩

/-- Cached lengths are correct (leaves are unconstrained: high digits are ignored). -/
def wf : KBytes → Bool
  | leaf _ _ => true
  | node n l r => n == l.len + r.len && l.wf && r.wf

/-- The empty byte string. -/
def empty : KBytes := leaf 0 0

/-- The little-endian value of the `w` bytes at `off` (meaningful when `off + w ≤ len`). -/
def read : KBytes → Nat → Nat → Nat
  | leaf _ v, off, w => (v >>> (8 * off)) % 2 ^ (8 * w)
  | node _ l r, off, w =>
    if off + w ≤ l.len then read l off w
    else if l.len ≤ off then read r (off - l.len) w
    else read l off (l.len - off) + (read r 0 (w - (l.len - off)) <<< (8 * (l.len - off)))

/-- The `w` bytes at `off` as a little-endian number, if they are in range. -/
def readLE (t : KBytes) (off w : Nat) : Option Nat :=
  if off + w ≤ t.len then some (t.read off w) else none

/-- Byte `i` as a number (meaningful when `i < len`). -/
def byte (t : KBytes) (i : Nat) : Nat := t.read i 1

/-- Byte `i`, if it is in range. -/
def get? (t : KBytes) (i : Nat) : Option UInt8 :=
  if i < t.len then some (UInt8.ofNat (t.byte i)) else none

/-- Concatenation: one node. The result is a rope, not canonical. -/
def append (a b : KBytes) : KBytes := node (a.len + b.len) a b

instance : Append KBytes := ⟨append⟩

/-- The `w` bytes at `off` (meaningful when `off + w ≤ len`), sharing untouched subtrees. -/
def slice : KBytes → Nat → Nat → KBytes
  | leaf _ v, off, w => leaf w ((v >>> (8 * off)) % 2 ^ (8 * w))
  | node _ l r, off, w =>
    if off + w ≤ l.len then slice l off w
    else if l.len ≤ off then slice r (off - l.len) w
    else node w (slice l off (l.len - off)) (slice r 0 (w - (l.len - off)))

/-- The largest power of two strictly below `k` (for `k ≥ 2`): the leaf count of the left
subtree of a left-balanced tree with `k` leaves. -/
def leftLeaves (k : Nat) : Nat := 2 ^ Nat.log2 (k - 1)

/-- The canonical tree, chunk size `c`, of the `n` bytes of `t` at `off`, with `fuel` levels.
Out of fuel, it returns one leaf (still the right bytes, merely not canonical). -/
def canonAux (t : KBytes) (c : Nat) : Nat → Nat → Nat → KBytes
  | 0, off, n => leaf n (t.read off n)
  | fuel + 1, off, n =>
    if n ≤ c then leaf n (t.read off n)
    else
      let p := leftLeaves ((n + c - 1) / c) * c
      node n (canonAux t c fuel off p) (canonAux t c fuel (off + p) (n - p))

/-- `t` rebuilt in canonical form with `c`-byte leaves. -/
def canon (c : Nat) (t : KBytes) : KBytes := canonAux t c 64 0 t.len

/-- Structural equality. On canonical trees it decides equality of the bytes. On ropes it is
only sound (`toList_eq_of_beq`); compare `canon c a` with `canon c b` instead. -/
def beq : KBytes → KBytes → Bool
  | leaf n v, leaf m u => n == m && v == u
  | node n a b, node m c d => n == m && beq a c && beq b d
  | _, _ => false

/-- Same bytes, whatever the shapes: equal lengths and equal `w`-byte windows
(`w = 65536` measured fastest; see benchmarks/kernel-bytes). -/
def sameBytes (w : Nat) (a b : KBytes) : Bool :=
  a.len == b.len && go a.len 0 (a.len / w + 1)
where
  /-- Compare the windows from `off`, with `fuel` windows left. -/
  go (n off : Nat) : Nat → Bool
    | 0 => n ≤ off
    | fuel + 1 => if n ≤ off then true else
        a.read off (min w (n - off)) == b.read off (min w (n - off)) && go n (off + w) fuel

/-- The bytes are `b`'s (for compiled code; the kernel compares canonical trees instead). -/
def eqByteArray (t : KBytes) (b : ByteArray) : Bool := t.toList == b.data.toList

/-! ## The canonical form of chunk literals -/

/-- The bytes of chunk literals (as `Silmaril.IncludeBytes.bytesChunks`): `n` bytes, `c` per
literal, the last literal holding what remains. -/
def chunksBytes (c : Nat) : Nat → List Nat → List UInt8
  | _, [] => []
  | n, x :: xs => unpack (min c n) x ++ chunksBytes c (n - c) xs

/-- The bytes of chunk literals as a `ByteArray` (as `Silmaril.IncludeBytes.decode`). -/
def decodeChunks (c n : Nat) (cs : List Nat) : ByteArray := ⟨⟨chunksBytes c n cs⟩⟩

/-- One node per chunk, nested to the right (the fallback when `ofChunksAux` runs out of fuel). -/
def chain (c : Nat) : Nat → List Nat → KBytes
  | _, [] => empty
  | n, [x] => leaf (min c n) x
  | n, x :: y :: ys =>
    let r := chain c (n - c) (y :: ys)
    node (min c n + r.len) (leaf (min c n) x) r

/-- The left-balanced tree of the chunk literals `cs` (`k = cs.length`, `n` bytes in all). -/
def ofChunksAux (c : Nat) : Nat → Nat → List Nat → Nat → KBytes
  | 0, n, cs, _ => chain c n cs
  | fuel + 1, n, cs, k =>
    if k ≤ 1 then chain c n cs
    else
      let p := leftLeaves k
      let l := ofChunksAux c fuel (min n (p * c)) (cs.take p) p
      let r := ofChunksAux c fuel (n - p * c) (cs.drop p) (k - p)
      node (l.len + r.len) l r

/-- The canonical tree of `n` bytes given as `c`-byte little-endian chunk literals. The
elaborator writes this tree out as a literal and proves it equal to `ofChunks` by `rfl`. -/
def ofChunks (c n : Nat) (cs : List Nat) : KBytes := ofChunksAux c 64 n cs cs.length

end KBytes

end Silmaril

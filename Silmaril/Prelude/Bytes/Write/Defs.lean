module

public import Silmaril.Prelude.Bytes.Defs

/-! # Writes on kernel bytes

`Silmaril.KBytes` (`Silmaril.Prelude.Bytes`) is read, sliced and concatenated. This module adds
**writes**, as two alternatives with the same specification and different costs, plus
the zero byte strings that writable memories start from. None of them depends on a particular
client (Wasm memory, a process image, a patched ELF file).

* `write t off w v` (**path copying**): replace the `w` bytes at `off` by the `w` low bytes
  of `v`. It rewrites the leaves the window falls in, digit-wise (`%`, `/`, `*`, `+` on the leaf
  number), and copies the path to them. The tree keeps its shape: every node and leaf keeps its
  length, so a tree with leaves of at most `c` bytes keeps that bound (`leafBound`). Untouched
  subtrees are shared with `t`, so many writes on one base share it. This is `kwrite` of
  hiloopai/silmaril-lean#133.
* `ropeWrite t off w v` (**rope**): `slice 0 off ++ leaf w (v % 256 ^ w) ++ slice (off + w) …`,
  the write expressible with the read-only interface alone. Slices share untouched subtrees,
  but every write adds nodes and a leaf of `w` bytes, so neither the depth nor the leaf size
  stays bounded. This is the `KRope` store of #133.
* `writeLE?` and `ropeWriteLE?` check bounds (`off + w ≤ len`) and return `none` out of range.
  `write` and `ropeWrite` themselves do not check bounds.

**Truncation**: a `w`-byte write stores `v % 256 ^ w`; higher digits of `v` are ignored.

**Zeros** (zero compression): `zeros n` is one leaf `leaf n 0` (no tree at all; a first write
splits nothing, it rewrites that one number), and `zerosCanon c n` is the canonical tree of
`c`-byte zero leaves (`ofChunks`, which shares no subterms but keeps leaves at most `c` bytes).

Three conditions appear in the theorems (`Silmaril.Prelude.Bytes.Write.Thms`), and they differ:

* `wf` (cached lengths are correct) is the **validity** condition of every specification
  theorem, and every write preserves it.
* `leafBound c` (every leaf holds at most `c` bytes) is a **performance** invariant. It costs
  the kernel big-number operations on at most `c`-byte numbers per leaf. `write` preserves it,
  and `ropeWrite` does not.
* `normal` (every leaf number is below `256 ^ len`) is what makes the literal leaves of
  canonical trees (`ofChunks`, `kbytes_def`) unique. `write` preserves it, so a written
  canonical tree can still be compared leaf by leaf (`beq`). **Canonicity** itself (being
  `canon c` of something) is not claimed for written trees beyond that.

The specification is the byte list: `toList (write t off w v) = splice t.toList off w v`.
-/

@[expose] public section

namespace Silmaril.KBytes

/-- The specification of a write: the `w` bytes at `off` of `bs` replaced by `unpack w v`. -/
def splice (bs : List UInt8) (off w v : Nat) : List UInt8 :=
  bs.take off ++ unpack w v ++ bs.drop (off + w)

/-- Replace the `w` bytes at `off` by the `w` low bytes of `v`, copying the path to the
affected leaves (meaningful when `off + w ≤ len`; no bounds check). -/
def write : KBytes → Nat → Nat → Nat → KBytes
  | .leaf n x, off, w, v =>
    .leaf n (x % 256 ^ off + 256 ^ off * (v % 256 ^ w + 256 ^ w * (x / 256 ^ (off + w))))
  | .node n l r, off, w, v =>
    if off + w ≤ l.len then .node n (write l off w v) r
    else if l.len ≤ off then .node n l (write r (off - l.len) w v)
    else .node n (write l off (l.len - off) v)
      (write r 0 (w - (l.len - off)) (v / 256 ^ (l.len - off)))

/-- `write`, if the window is in range. -/
def writeLE? (t : KBytes) (off w v : Nat) : Option KBytes :=
  if off + w ≤ t.len then some (t.write off w v) else none

/-- The write as a rope of two slices around a new leaf (no bounds check). -/
def ropeWrite (t : KBytes) (off w v : Nat) : KBytes :=
  t.slice 0 off ++ leaf w (v % 256 ^ w) ++ t.slice (off + w) (t.len - (off + w))

/-- `ropeWrite`, if the window is in range. -/
def ropeWriteLE? (t : KBytes) (off w v : Nat) : Option KBytes :=
  if off + w ≤ t.len then some (t.ropeWrite off w v) else none

/-- `n` zero bytes as one leaf. -/
def zeros (n : Nat) : KBytes := leaf n 0

/-- `n` zero bytes as the canonical tree of `c`-byte leaves. -/
def zerosCanon (c n : Nat) : KBytes := ofChunks c n (List.replicate ((n + c - 1) / c) 0)

/-- Every leaf holds at most `c` bytes (a performance invariant, not a validity condition). -/
def leafBound (c : Nat) : KBytes → Bool
  | leaf n _ => n ≤ c
  | node _ l r => leafBound c l && leafBound c r

/-- Every leaf number is below `256 ^ len`: no digits beyond the leaf's bytes. -/
def normal : KBytes → Bool
  | leaf n v => v < 256 ^ n
  | node _ l r => normal l && normal r

end Silmaril.KBytes

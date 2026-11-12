module

public import Silmaril.Data.Cells.Defs

/-!
# Bitmaps as fragments

A bitmap of `nwords` words of `wbytes` bytes at `base`, bit `i` in word `i / (8 * wbytes)` at
position `i % (8 * wbytes)` (glibc's `binmap`: 4 words of 4 bytes, `idx2block`/`idx2bit`).
-/

@[expose] public section

namespace Silmaril.Data.Bitmap

open Silmaril.Data

/-- The value of word `k` of the bitmap `f`. -/
def word (wbytes : Nat) (f : Nat → Bool) (k : Nat) : Nat :=
  ((List.range (8 * wbytes)).filter fun b => f (8 * wbytes * k + b)).foldl (fun acc b => acc + 2 ^ b) 0

/-- **The bitmap `f`** as a fragment. -/
def frag (base wbytes nwords : Nat) (f : Nat → Bool) : Frag :=
  (List.range nwords).map fun k => ⟨base + wbytes * k, wbytes, word wbytes f k⟩

/-- Set bit `i`. -/
def set (f : Nat → Bool) (i : Nat) : Nat → Bool := fun j => if j = i then true else f j

/-- Clear bit `i`. -/
def clear (f : Nat → Bool) (i : Nat) : Nat → Bool := fun j => if j = i then false else f j

/-- The first set bit at or after `i`, below `n` (glibc's binmap scan). -/
def nextSet (f : Nat → Bool) (i n : Nat) : Option Nat :=
  ((List.range (n - i)).map (· + i)).find? f

/-- **`Task.seplist.bitmapSet`**: setting (clearing) bit `i` is one store of word
`i / (8 * wbytes)` (`binmap[block] |= bit`), the other words unchanged. -/
def Task.seplist.bitmapSet : Prop :=
  ∀ (base wbytes nwords : Nat) (f : Nat → Bool) (v : MemView) (i : Nat) (b : Bool),
    0 < wbytes → i < 8 * wbytes * nwords → (frag base wbytes nwords f).Holds v →
    let g := if b then set f i else clear f i
    let k := i / (8 * wbytes)
    (frag base wbytes nwords g).Holds (v.store ⟨base + wbytes * k, wbytes, word wbytes g k⟩)

end Silmaril.Data.Bitmap

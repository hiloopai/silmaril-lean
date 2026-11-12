module

public import Silmaril.Wasm.Tools.Meta.Fast.Defs
public import Silmaril.Wasm.Tools.Meta.Names.Defs

/-!
# wasmparser's error offsets inside `name`, `component-name` and `producers` sections

The list readers of `Names.Defs` and `Producers.Defs` decide whether a section reads and what it
holds; their error messages carry no offset. The checkers here read the same sections over the
input array in the order wasmparser's iterators do (and wasm-metadata or wasm-encoder's
re-encoder consume them), and report the first error with its offset. They are used only to
render the message of an error the list readers found (and, as hooks of the payload walk, to
find the first error in stream order); they decide nothing.

Order details kept from upstream: a name map checks index order after reading the name
("names out of order" at the start of the entry); an indirect map and a producers field first
skip their inner entries (`skip_string`: length limit and bounds only) and then read them
(UTF-8); a lazy read (`ModuleNames::from_bytes`, `ComponentNames::from_bytes`) reads only the
subsection framing, the name subsection and the first count of each map.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Chk

open Silmaril.Wasm.Tools.Meta

abbrev R := Except FErr

/-- `read_u7` at `pos` below `lim`. -/
def rdU7 (ba : ByteArray) (lim pos : Nat) : R Nat :=
  if pos < lim then
    let b := byteAt ba pos
    if 128 ≤ b.toNat then .error ("invalid u7", pos) else .ok b.toNat
  else .error (errEof, pos)

/-- `read_u8` at `pos` below `lim`. -/
def rdU8 (ba : ByteArray) (lim pos : Nat) : R Nat :=
  if pos < lim then .ok (byteAt ba pos).toNat else .error (errEof, pos)

/-- `skip_string` at `pos`: the end of the string. -/
def skipStr (ba : ByteArray) (lim pos : Nat) : R Nat := do
  let (n, p) ← rdU32 ba lim pos
  if 100000 < n then throw ("string size out of bounds", p - 1)
  rdBytes lim p n

/-- `k` entries of a `NameMap` from `pos` (index, unlimited string; order checked after the
entry reads). The position after them. -/
def mapEntries (ba : ByteArray) (lim : Nat) : Nat → Option Nat → Nat → R Nat
  | 0, _, pos => .ok pos
  | k + 1, last, pos => do
    let (i, p) ← rdU32 ba lim pos
    let (_, q) ← rdStr ba lim p false
    if !idxOk last i then throw ("names out of order", pos)
    mapEntries ba lim k (some i) q

/-- A `NameMap` filling `[a, b)`, iterated to the end. -/
def nameMap (ba : ByteArray) (a b : Nat) : R Unit := do
  let (k, p) ← rdU32 ba b a
  let q ← mapEntries ba b k none p
  if q != b then throw ("section size mismatch: unexpected data at the end of the section", q)

/-- Skip `k` (index, string) pairs. -/
def skipPairs (ba : ByteArray) (lim : Nat) : Nat → Nat → R Nat
  | 0, pos => .ok pos
  | k + 1, pos => do
    let (_, p) ← rdU32 ba lim pos
    let q ← skipStr ba lim p
    skipPairs ba lim k q

/-- `k` entries of an `IndirectNameMap`, each inner map iterated right after its entry. -/
def indEntries (ba : ByteArray) (lim : Nat) : Nat → Option Nat → Nat → R Nat
  | 0, _, pos => .ok pos
  | k + 1, last, pos => do
    let (i, p) ← rdU32 ba lim pos
    let (c, q) ← rdU32 ba lim p
    let e ← skipPairs ba lim c q
    if !idxOk last i then throw ("indirect names out of order", pos)
    nameMap ba p e
    indEntries ba lim k (some i) e

/-- An `IndirectNameMap` filling `[a, b)`. -/
def indMap (ba : ByteArray) (a b : Nat) : R Unit := do
  let (k, p) ← rdU32 ba b a
  let q ← indEntries ba b k none p
  if q != b then throw ("section size mismatch: unexpected data at the end of the section", q)

/-- A name subsection `[a, b)`: a string and nothing after it. -/
def nameSub (ba : ByteArray) (limited : Bool) (a b : Nat) : R Unit := do
  let (_, q) ← rdStr ba b a limited
  if q != b then throw ("trailing data at the end of a name", q)

/-- The subsections of a name section `[pos, lim)`, each checked by `dec id a b`. -/
def subs (ba : ByteArray) (lim : Nat) (dec : Nat → Nat → Nat → R Unit) : Nat → Nat → R Unit
  | 0, _ => .ok ()
  | f + 1, pos =>
    if lim ≤ pos then .ok () else do
    let id ← rdU7 ba lim pos
    let (n, p) ← rdU32 ba lim (pos + 1)
    let e ← rdBytes lim p n
    dec id p e
    subs ba lim dec f e

/-- The sort of a `component-name` subsection 1 at `a`: the start of its name map, if the sort
is known. -/
def compSortB (ba : ByteArray) (a b : Nat) : R (Option Nat) := do
  let k ← rdU8 ba b a
  if k == 0 then
    let k2 ← rdU8 ba b (a + 1)
    pure (if k2 ∈ [0, 1, 2, 3, 4, 0x10, 0x11, 0x12] then some (a + 2) else none)
  else pure (if k ∈ [1, 2, 3, 4, 5] then some (a + 1) else none)

/-- `ModuleNames::from_bytes` on `[a, b)`. -/
def scanNames (ba : ByteArray) (a b : Nat) : R Unit :=
  subs ba b (fun id p e =>
    if id == 0 then nameSub ba true p e
    else if id ∈ mapIds ∨ id ∈ indIds then (rdU32 ba e p).map fun _ => ()
    else .ok ()) (b - a + 1) a

/-- `ComponentNames::from_bytes` on `[a, b)`. -/
def scanCompNames (ba : ByteArray) (a b : Nat) : R Unit :=
  subs ba b (fun id p e =>
    if id == 0 then nameSub ba false p e
    else if id == 1 then do
      match ← compSortB ba p e with
      | some q => let _ ← rdU32 ba e q; pure ()
      | none => pure ()
    else .ok ()) (b - a + 1) a

/-- The full read of a module `name` section (wasm-encoder's re-encoder). -/
def decodeNames (ba : ByteArray) (a b : Nat) : R Unit :=
  subs ba b (fun id p e =>
    if id == 0 then nameSub ba true p e
    else if id ∈ mapIds then nameMap ba p e
    else if id ∈ indIds then indMap ba p e
    else .ok ()) (b - a + 1) a

/-- The full read of a `component-name` section. -/
def decodeCompNames (ba : ByteArray) (a b : Nat) : R Unit :=
  subs ba b (fun id p e =>
    if id == 0 then nameSub ba false p e
    else if id == 1 then do
      match ← compSortB ba p e with
      | some q => nameMap ba q e
      | none => pure ()
    else .ok ()) (b - a + 1) a

/-- Read `k` values (two unlimited strings each). -/
def values (ba : ByteArray) (lim : Nat) : Nat → Nat → R Nat
  | 0, pos => .ok pos
  | k + 1, pos => do
    let (_, p) ← rdStr ba lim pos false
    let (_, q) ← rdStr ba lim p false
    values ba lim k q

/-- Skip `k` values (two `skip_string`s each). -/
def skipValues (ba : ByteArray) (lim : Nat) : Nat → Nat → R Nat
  | 0, pos => .ok pos
  | k + 1, pos => do
    let p ← skipStr ba lim pos
    let q ← skipStr ba lim p
    skipValues ba lim k q

/-- `k` producers fields: name, the values skipped, then read. -/
def fields (ba : ByteArray) (lim : Nat) : Nat → Nat → R Nat
  | 0, pos => .ok pos
  | k + 1, pos => do
    let (ns, ne) ← rdStr ba lim pos false
    let name := String.fromUTF8! (ba.extract ns ne)
    if !(name == "language" || name == "sdk" || name == "processed-by") then
      throw ("invalid producers field name: `" ++ name ++ "`", pos)
    let (c, p) ← rdU32 ba lim ne
    let e ← skipValues ba lim c p
    let _ ← values ba e c p
    fields ba lim k e

/-- `Producers::from_bytes` on `[a, b)`. -/
def producers (ba : ByteArray) (a b : Nat) : R Unit := do
  let (k, p) ← rdU32 ba b a
  let q ← fields ba b k p
  if q != b then throw ("section size mismatch: unexpected data at the end of the section", q)

end Silmaril.Wasm.Tools.Meta.Chk

end

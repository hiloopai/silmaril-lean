module

public import Silmaril.Wasm.Jco.Styles.XAdaptor.Defs

/-!
# The canonical ABI with the string encodings `utf16` and `latin1+utf16`

`Silmaril.Wasm.Jco.Canon` is `canon lift` with `string-encoding=utf8`. This module adds the
`string-encoding` option. It follows `definitions.py` (`a25fc0b`): `store_string_into_range` for
a host string, `load_string_from_range` for a result. The host's strings are taken to be UTF-8
(the source encoding of `store_string`, with `src_code_units` the UTF-8 byte length), as in the
first fragment. The algorithms are restated here, not imported, over `M`'s memory and an
arbitrary `realloc`:

* `utf8` (`store_string_copy`): `lowerBytes`, as in `Canon`.
* `utf16` (`store_utf8_to_utf16`): with `n` UTF-8 bytes, allocate the worst case
  `realloc(0, 0, 2, 2n)`, check alignment 2 and bounds, write the UTF-16LE bytes, and if they are
  shorter **shrink with `realloc(ptr, 2n, 2, len)`**: a call with a nonzero old pointer. The
  result is `(ptr, code units)`.
* `latin1+utf16` (`store_string_to_latin1_or_utf16`): allocate `realloc(0, 0, 2, n)` and write
  the Latin-1 prefix. If the whole string is Latin-1, shrink to its length when shorter, and the
  result is `(ptr, length)`. Otherwise **grow with `realloc(ptr, n, 2, 2n)`**, inflate the
  prefix in place (read back from memory, so a `realloc` that does not move the old bytes is
  observed), write the rest as UTF-16LE, and shrink when shorter. The result is
  `(ptr, code units | 2^31)`.
* lifting a string from `(ptr, tagged)`: `utf16` checks alignment 2, reads `2 * tagged` bytes
  and decodes UTF-16LE strictly (unpaired surrogates trap). `latin1+utf16` checks alignment 2 and
  then reads UTF-16 when the tag bit `2^31` is set, Latin-1 otherwise.

`canonCallE enc realloc callee sig vs` is `canonCall` with the encoding `enc`.

Deviation: the length bound is `maxStringBytes = 2^31 - 1` of the first fragment. The reference
at `a25fc0b` has `MAX_STRING_BYTE_LENGTH = 2^28 - 1`, according to the transcription in
`Silmaril/Raw/Wasm/Component/ABI/String.lean`, so the first fragment and this module accept longer
strings than the reference. The Python `assert`s are not traps; they are kept as checks only
where they bound a length.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

/-! ## Codecs -/

/-- UTF-16 code units of a character. -/
def utf16Char (c : Char) : List Nat :=
  if c.toNat < 0x10000 then [c.toNat]
  else [0xD800 + (c.toNat - 0x10000) / 1024, 0xDC00 + (c.toNat - 0x10000) % 1024]

/-- UTF-16LE bytes of a string. -/
def utf16Bytes (s : String) : List UInt8 :=
  (s.toList.flatMap utf16Char).flatMap fun u => [(u % 256).toUInt8, (u / 256).toUInt8]

/-- Decode UTF-16 code units strictly. -/
def decodeUnits : List Nat → Option (List Char)
  | [] => some []
  | u :: us =>
    if u < 0xD800 ∨ 0xE000 ≤ u then (Char.ofNat u :: ·) <$> decodeUnits us
    else if u < 0xDC00 then
      match us with
      | v :: us' =>
        if 0xDC00 ≤ v ∧ v < 0xE000 then
          (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (v - 0xDC00)) :: ·) <$> decodeUnits us'
        else none
      | [] => none
    else none

/-- Little-endian 16-bit units of an even number of bytes. -/
def unitsOf : List UInt8 → Option (List Nat)
  | [] => some []
  | a :: b :: bs => ((a.toNat + 256 * b.toNat) :: ·) <$> unitsOf bs
  | [_] => none

/-- Decode UTF-16LE bytes (trap if invalid). -/
def decodeUtf16 (bs : List UInt8) : Option String := do
  let us ← unitsOf bs
  let cs ← decodeUnits us
  pure (String.ofList cs)

/-- Number of leading characters below `2^8`. -/
def latin1Prefix (s : String) : Nat := (s.toList.takeWhile (·.toNat < 256)).length

/-- Latin-1 bytes of the first `i` characters. -/
def latin1Bytes (s : String) (i : Nat) : List UInt8 := (s.toList.take i).map (·.toNat.toUInt8)

/-- Decode Latin-1 bytes. -/
def decodeLatin1 (bs : List UInt8) : String := String.ofList (bs.map fun b => Char.ofNat b.toNat)

/-- The in-place inflation of Latin-1 bytes to UTF-16LE. -/
def inflate (bs : List UInt8) : List UInt8 := bs.flatMap fun b => [b, 0]

/-- `UTF16_TAG` for 32-bit memories. -/
def utf16Tag : Nat := 2 ^ 31

/-! ## Storing a string -/

variable (M : CoreInst)

/-- Call `realloc(old, old_size, align, new_size)`; one `i32` result. -/
def reallocCall (R : List Flat → RM M.St (List Flat)) (old os al ns : Nat) :
    RM M.St (BitVec 32) := do
  let r ← R [i32n old, i32n os, i32n al, i32n ns]
  RM.ofOption (single32? r)

/-- Trap unless `p` is `al`-aligned and `[p, p + size)` is in bounds. -/
def checkAt (al size : Nat) (p : BitVec 32) : RM M.St Unit := do
  RM.check (p.toNat % al == 0)
  let s ← RM.get
  RM.check (decide (p.toNat + size ≤ (M.mem s).length))

/-- Shrink (or keep) a block to `len` bytes at the end of a store. -/
def shrinkTo (R : List Flat → RM M.St (List Flat)) (p : BitVec 32) (w len : Nat) :
    RM M.St (BitVec 32) :=
  if len < w then do
    let p' ← reallocCall M R p.toNat w 2 len
    checkAt M 2 len p'
    pure p'
  else pure p

/-- `store_utf8_to_utf16`. -/
def storeUtf16 (R : List Flat → RM M.St (List Flat)) (s : String) : RM M.St (List Flat) := do
  let w := 2 * (utf8 s).length
  RM.check (decide (w ≤ maxStringBytes))
  let p ← reallocCall M R 0 0 2 w
  checkAt M 2 w p
  let e := utf16Bytes s
  M.store p.toNat e
  let p' ← shrinkTo M R p w e.length
  pure [Flat.i32 p', i32n (e.length / 2)]

/-- `store_string_to_latin1_or_utf16`. -/
def storeLatin1Utf16 (R : List Flat → RM M.St (List Flat)) (s : String) :
    RM M.St (List Flat) := do
  let n := (utf8 s).length
  RM.check (decide (n ≤ maxStringBytes))
  let p ← reallocCall M R 0 0 2 n
  checkAt M 2 n p
  let i := latin1Prefix s
  M.store p.toNat (latin1Bytes s i)
  if i = s.length then do
    let p' ← shrinkTo M R p n i
    pure [Flat.i32 p', i32n i]
  else do
    let w := 2 * n
    RM.check (decide (w ≤ maxStringBytes))
    let p' ← reallocCall M R p.toNat n 2 w
    checkAt M 2 w p'
    let bs ← M.load p'.toNat i
    M.store p'.toNat (inflate bs)
    let e := utf16Bytes s
    M.store (p'.toNat + 2 * i) (e.drop (2 * i))
    let p'' ← shrinkTo M R p' w e.length
    pure [Flat.i32 p'', i32n (e.length / 2 ||| utf16Tag)]

/-- Store a host string with the destination encoding `enc`; the flat `(ptr, tagged)`. -/
def lowerStr (R : List Flat → RM M.St (List Flat)) : StrEnc → String → RM M.St (List Flat)
  | .utf8, s => lowerBytes M R maxStringBytes (utf8 s)
  | .utf16, s => storeUtf16 M R s
  | .latin1Utf16, s => storeLatin1Utf16 M R s

/-! ## Loading a string -/

/-- `load_string_from_range` for `(ptr, tagged)`. -/
def liftStr : StrEnc → BitVec 32 → BitVec 32 → RM M.St String
  | .utf8, p, l => do
    let bs ← M.load p.toNat l.toNat
    RM.ofOption (decodeUtf8 bs)
  | .utf16, p, l => do
    RM.check (p.toNat % 2 == 0)
    let bs ← M.load p.toNat (2 * l.toNat)
    RM.ofOption (decodeUtf16 bs)
  | .latin1Utf16, p, l => do
    RM.check (p.toNat % 2 == 0)
    if l.toNat &&& utf16Tag != 0 then do
      let bs ← M.load p.toNat (2 * (l.toNat ^^^ utf16Tag))
      RM.ofOption (decodeUtf16 bs)
    else do
      let bs ← M.load p.toNat l.toNat
      pure (decodeLatin1 bs)

/-- The `(ptr, len)` pair at a 4-aligned address. -/
def pairAt (rp : BitVec 32) : RM M.St (BitVec 32 × BitVec 32) := do
  RM.check (rp.toNat % 4 == 0)
  let w ← M.load rp.toNat 8
  let p ← RM.ofOption (ofLe32 (w.take 4))
  let l ← RM.ofOption (ofLe32 (w.drop 4))
  pure (p, l)

/-! ## The canonical call with an encoding -/

/-- Lowering one parameter. -/
def lowerParamE (enc : StrEnc) (R : List Flat → RM M.St (List Flat)) :
    PTy → PVal → RM M.St (List Flat)
  | .string, .string s => lowerStr M R enc s
  | t, v => lowerParam M R t v

/-- Lowering the parameters. -/
def lowerParamsE (enc : StrEnc) (R : List Flat → RM M.St (List Flat)) :
    List PTy → List PVal → RM M.St (List Flat)
  | [], [] => pure []
  | t :: ts, v :: vs => do
    let a ← lowerParamE M enc R t v
    let b ← lowerParamsE enc R ts vs
    pure (a ++ b)
  | _, _ => RM.fail

/-- Lifting the result. -/
def liftResultE (enc : StrEnc) : Option PTy → List Flat → RM M.St (Option PVal)
  | some .string, [x] => do
    let rp ← RM.ofOption (asI32? x)
    let (p, l) ← pairAt M rp
    let s ← liftStr M enc p l
    pure (some (.string s))
  | r, xs => liftResult M r xs

/-- **`canon lift` with the string encoding `enc`.** -/
def canonCallE : LiftSem M := fun enc R callee sig vs => do
  let xs ← lowerParamsE M enc R sig.params vs
  let rs ← callee xs
  liftResultE M enc sig.result rs

end Silmaril.Wasm.Jco

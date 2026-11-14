module

public import Silmaril.Net.Qpack.Instruction.Defs

@[expose] public section

/-!
# QPACK encoded field sections (RFC 9204 §4.5, §2.2)

"An encoded field section consists of a prefix and a possibly empty sequence of
representations ... These representations reference the static table or the dynamic table in a
particular state, but they do not modify that state" (§4.5).

**Prefix (§4.5.1).** `Required Insert Count (8+) | S | Delta Base (7+)`.

* *Required Insert Count* (§4.5.1.1), "one larger than the largest absolute index of all
  referenced dynamic table entries", or zero without dynamic references (§2.1.2), is sent
  modulo `2 * MaxEntries`: `encodeRic`, with `MaxEntries = floor(MaxTableCapacity / 32)`.
  `decodeRic` is the decoder's reconstruction algorithm of §4.5.1.1, returning `none` for a
  value "that could not have been produced by a conformant encoder". (Its final check "Value
  of 0 must be encoded as 0" can only fail in the non-wrapping branch: after unwrapping, the
  value exceeds zero.)
* *Base* (§4.5.1.2): "if Sign == 0: Base = ReqInsertCount + DeltaBase, else: Base =
  ReqInsertCount - DeltaBase - 1"; "An endpoint MUST treat a field block with a Sign bit of 1
  as invalid if the value of Required Insert Count is less than or equal to the value of Delta
  Base" (`decodeBase`). `encodeBase` picks the sign.

**Field line representations (§4.5.2–§4.5.6).**

| Representation | First octet | Index / name | RFC 9204 |
| --- | --- | --- | --- |
| Indexed Field Line | `1Txxxxxx` | index (6+) | §4.5.2 |
| Indexed Field Line with Post-Base Index | `0001xxxx` | index (4+) | §4.5.3 |
| Literal Field Line with Name Reference | `01NTxxxx` | index (4+), value | §4.5.4 |
| Literal Field Line with Post-Base Name Reference | `0000Nxxx` | index (3+), value | §4.5.5 |
| Literal Field Line with Literal Name | `001NHxxx` | name (4-bit string), value | §4.5.6 |

A reference (`Ref`) is a static index (`T = 1`), a dynamic index relative to the Base
(`T = 0`, §3.2.5), or a post-Base index (§3.2.6). `N` is the never-indexed bit, kept so that an
intermediary can forward the line as a literal (§4.5.4, §7.1.3). Values are 8-bit prefix
string literals; Huffman coding is rejected (planned).

**Decoding against the table (§2.2.1, §2.2.3).** `decodeFieldSection t s` reconstructs the
Required Insert Count from `t`'s insert count. If it exceeds the insert count the stream is
**blocked** ("the stream cannot be processed immediately", §2.1.2, §2.2.1) and nothing else is
read. Otherwise each line is resolved; "a reference ... to a dynamic table entry that has
already been evicted or that has an absolute index greater than or equal to the declared
Required Insert Count" is `QPACK_DECOMPRESSION_FAILED` (§2.2.3), as are an invalid static index
(§3.1), an undecodable Required Insert Count (§4.5.1.1) and a negative Base (§4.5.1.2). A
Required Insert Count larger than needed is accepted (§2.2.1 makes rejecting it optional).
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry encodeInt decodeInt)

/-! ## Required Insert Count and Base (§4.5.1.1, §4.5.1.2) -/

/-- The encoded Required Insert Count (§4.5.1.1), for `MaxEntries = maxEntries`. -/
def encodeRic (maxEntries ric : Nat) : Nat :=
  if ric = 0 then 0 else ric % (2 * maxEntries) + 1

/-- The decoder's reconstruction of the Required Insert Count (§4.5.1.1) from the encoded value
`enc`, `MaxEntries` and `TotalNumberOfInserts`; `none` is an error. -/
def decodeRic (maxEntries totalInserts enc : Nat) : Option Nat :=
  if enc = 0 then some 0
  else if 2 * maxEntries < enc then none
  else
    let maxValue := totalInserts + maxEntries
    let ric := maxValue / (2 * maxEntries) * (2 * maxEntries) + enc - 1
    if maxValue < ric then (if ric ≤ 2 * maxEntries then none else some (ric - 2 * maxEntries))
    else if ric = 0 then none else some ric

/-- The Sign bit and Delta Base for a Base (§4.5.1.2). -/
def encodeBase (ric base : Nat) : Bool × Nat :=
  if ric ≤ base then (false, base - ric) else (true, ric - base - 1)

/-- The Base from the Sign bit and Delta Base (§4.5.1.2); `none` for a negative Base. -/
def decodeBase (ric : Nat) (sign : Bool) (delta : Nat) : Option Nat :=
  if sign then (if delta < ric then some (ric - delta - 1) else none) else some (ric + delta)

/-- The encoded field section prefix (§4.5.1). -/
structure SectionPrefix where
  encRic : Nat
  sign : Bool
  deltaBase : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Serialize the prefix: Required Insert Count (8+), then `S` and Delta Base (7+). -/
def SectionPrefix.encode (p : SectionPrefix) : List UInt8 :=
  encodeInt 8 0 p.encRic ++ encodeInt 7 (if p.sign then 0x80 else 0) p.deltaBase

/-- Read the prefix (§4.5.1). -/
def decodePrefix (xs : List UInt8) : Option (SectionPrefix × List UInt8) :=
  match decodeInt 8 xs with
  | none => none
  | some (e, r) =>
    match r with
    | [] => none
    | b :: bs =>
      match decodeInt 7 (b :: bs) with
      | none => none
      | some (d, r') => some (⟨e, decide (128 ≤ b.toNat), d⟩, r')

/-! ## Field line representations (§4.5.2–§4.5.6) -/

/-- A table reference in a field line. -/
inductive Ref where
  /-- A static table index (`T = 1`, §3.1). -/
  | static (index : Nat)
  /-- A dynamic table index relative to the Base (`T = 0`, §3.2.5). -/
  | dynamic (index : Nat)
  /-- A post-Base index (§3.2.6). -/
  | postBase (index : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A field line representation (§4.5.2–§4.5.6). -/
inductive FieldLine where
  /-- Indexed Field Line (§4.5.2), or with Post-Base Index (§4.5.3). -/
  | indexed (ref : Ref)
  /-- Literal Field Line with Name Reference (§4.5.4) or Post-Base Name Reference (§4.5.5);
  `never` is the `N` bit. -/
  | literalRef (never : Bool) (ref : Ref) (value : List UInt8)
  /-- Literal Field Line with Literal Name (§4.5.6). -/
  | literal (never : Bool) (name value : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- `1` as a flag bit of weight `w` when `b` holds. -/
def flagIf (b : Bool) (w : Nat) : Nat := if b then w else 0

/-- Serialize a field line (raw string literals). -/
def FieldLine.encode : FieldLine → List UInt8
  | .indexed (.static i) => encodeInt 6 0xc0 i
  | .indexed (.dynamic i) => encodeInt 6 0x80 i
  | .indexed (.postBase i) => encodeInt 4 0x10 i
  | .literalRef n (.static i) v => encodeInt 4 (0x50 + flagIf n 0x20) i ++ encodeStringN 8 0 v
  | .literalRef n (.dynamic i) v => encodeInt 4 (0x40 + flagIf n 0x20) i ++ encodeStringN 8 0 v
  | .literalRef n (.postBase i) v => encodeInt 3 (flagIf n 0x08) i ++ encodeStringN 8 0 v
  | .literal n name v => encodeStringN 4 (0x20 + flagIf n 0x10) name ++ encodeStringN 8 0 v

/-- Read a value string after a name index. -/
def decodeValueAfter (mk : List UInt8 → FieldLine) (r : List UInt8) :
    Option (FieldLine × List UInt8) :=
  match decodeStringN 8 r with
  | none => none
  | some (v, r') => some (mk v, r')

/-- Read one field line, dispatching on the first octet (§4.5.2–§4.5.6). -/
def decodeFieldLine : List UInt8 → Option (FieldLine × List UInt8)
  | [] => none
  | b :: bs =>
    let x := b.toNat
    if 128 ≤ x then
      (decodeInt 6 (b :: bs)).map fun (i, r) =>
        (.indexed (if 192 ≤ x then .static i else .dynamic i), r)
    else if 64 ≤ x then
      match decodeInt 4 (b :: bs) with
      | none => none
      | some (i, r) =>
        decodeValueAfter
          (.literalRef (decide (96 ≤ x)) (if 16 ≤ x % 32 then .static i else .dynamic i)) r
    else if 32 ≤ x then
      match decodeStringN 4 (b :: bs) with
      | none => none
      | some (n, r) => decodeValueAfter (.literal (decide (48 ≤ x)) n) r
    else if 16 ≤ x then (decodeInt 4 (b :: bs)).map fun (i, r) => (.indexed (.postBase i), r)
    else
      match decodeInt 3 (b :: bs) with
      | none => none
      | some (i, r) => decodeValueAfter (.literalRef (decide (8 ≤ x)) (.postBase i)) r

/-- An encoded field section (§4.5): the prefix and the field lines. -/
structure EncodedSection where
  pre : SectionPrefix
  lines : List FieldLine
  deriving DecidableEq, Repr, Inhabited

/-- Serialize an encoded field section. -/
def EncodedSection.encode (s : EncodedSection) : List UInt8 :=
  s.pre.encode ++ s.lines.flatMap FieldLine.encode

/-- Read an encoded field section occupying the whole input. -/
def decodeEncodedSection (xs : List UInt8) : Option EncodedSection :=
  match decodePrefix xs with
  | none => none
  | some (p, r) => (decodeMany decodeFieldLine r).map fun ls => ⟨p, ls⟩

/-! ## Decoding against the dynamic table (§2.2.1, §2.2.3) -/

/-- The absolute index a reference names, given the Base (`none` for static references and
for relative indices not below the Base). -/
def Ref.abs (base : Nat) : Ref → Option Nat
  | .static _ => none
  | .dynamic r => relToAbs base r
  | .postBase p => some (postBaseToAbs base p)

/-- Whether a reference is to the static table. -/
def Ref.isStatic : Ref → Bool
  | .static _ => true
  | _ => false

/-- The reference of a field line, if any. -/
def FieldLine.ref? : FieldLine → Option Ref
  | .indexed r => some r
  | .literalRef _ r _ => some r
  | .literal _ _ _ => none

/-- A field line that needs no dynamic state (§2.1: "References to the static table and literal
representations do not require any dynamic state"). -/
def FieldLine.staticOnly (l : FieldLine) : Bool :=
  match l.ref? with
  | some r => r.isStatic
  | none => true

/-- The absolute index a field line references, given the Base. -/
def FieldLine.absRef (base : Nat) (l : FieldLine) : Option Nat := l.ref?.bind (Ref.abs base)

/-- A dynamic table entry referenced by a field section with Required Insert Count `ric`:
`QPACK_DECOMPRESSION_FAILED` if `a ≥ ric` or the entry was evicted (§2.2.3). -/
def lookupDyn (t : DynTable) (ric a : Nat) : Except QpackError Entry :=
  if a < ric then
    match t.lookupAbs a with
    | some e => .ok e
    | none => .error .decompressionFailed
  else .error .decompressionFailed

/-- Resolve a reference (§3.1, §3.2.5, §3.2.6, §2.2.3). -/
def resolveRef (t : DynTable) (ric base : Nat) : Ref → Except QpackError Entry
  | .static i =>
    match staticLookup i with
    | some e => .ok e
    | none => .error .decompressionFailed
  | .dynamic r =>
    match relToAbs base r with
    | some a => lookupDyn t ric a
    | none => .error .decompressionFailed
  | .postBase p => lookupDyn t ric (postBaseToAbs base p)

/-- The field line a representation denotes (§4.5.2–§4.5.6). -/
def FieldLine.resolve (t : DynTable) (ric base : Nat) : FieldLine → Except QpackError Entry
  | .indexed r => resolveRef t ric base r
  | .literalRef _ r v =>
    match resolveRef t ric base r with
    | .ok e => .ok ⟨e.name, v⟩
    | .error err => .error err
  | .literal _ n v => .ok ⟨n, v⟩

/-- Resolve field lines in order (§2.2: "The decoder MUST emit field lines in the order their
representations appear"). -/
def resolveLines (t : DynTable) (ric base : Nat) : List FieldLine → Except QpackError (List Entry)
  | [] => .ok []
  | l :: ls =>
    match l.resolve t ric base with
    | .error err => .error err
    | .ok e =>
      match resolveLines t ric base ls with
      | .error err => .error err
      | .ok es => .ok (e :: es)

/-- The outcome of decoding a field section: blocked on its Required Insert Count (§2.2.1), or
decoded into field lines. -/
inductive SectionResult where
  | blocked (ric : Nat)
  | decoded (ric : Nat) (fields : List Entry)
  deriving DecidableEq, Repr

/-- Decode an encoded field section against the decoder's table (§2.2.1, §2.2.3, §4.5). -/
def decodeFieldSection (t : DynTable) (s : EncodedSection) : Except QpackError SectionResult :=
  match decodeRic t.maxEntries t.insertCount s.pre.encRic with
  | none => .error .decompressionFailed
  | some ric =>
    if t.insertCount < ric then .ok (.blocked ric)
    else
      match decodeBase ric s.pre.sign s.pre.deltaBase with
      | none => .error .decompressionFailed
      | some base =>
        match resolveLines t ric base s.lines with
        | .ok fs => .ok (.decoded ric fs)
        | .error err => .error err

/-- Decode a field section from octets; malformed octets are `QPACK_DECOMPRESSION_FAILED`. -/
def decodeFieldSectionBytes (t : DynTable) (xs : List UInt8) : Except QpackError SectionResult :=
  match decodeEncodedSection xs with
  | none => .error .decompressionFailed
  | some s => decodeFieldSection t s

end Silmaril.Net.Qpack

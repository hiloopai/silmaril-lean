module

public import Silmaril.Net.Qpack.Error.Defs
public import Silmaril.Net.Qpack.Static.Defs
public import Silmaril.Net.Qpack.String.Defs
public import Silmaril.Net.Qpack.Table.Defs

@[expose] public section

/-!
# QPACK encoder and decoder instructions (RFC 9204 §4.2–§4.4)

QPACK carries table updates on two unidirectional streams (§4.2): the **encoder stream** (type
`0x02`) carries "an unframed sequence of encoder instructions from encoder to decoder", the
**decoder stream** (type `0x03`) "an unframed sequence of decoder instructions from decoder to
encoder".

**Encoder instructions (§4.3).**

| Instruction | First octet | Fields | RFC 9204 |
| --- | --- | --- | --- |
| Set Dynamic Table Capacity | `001xxxxx` | capacity (5+) | §4.3.1 |
| Insert with Name Reference | `1Txxxxxx` | name index (6+), value (8-bit string) | §4.3.2 |
| Insert with Literal Name | `01Hxxxxx` | name (6-bit string), value (8-bit string) | §4.3.3 |
| Duplicate | `000xxxxx` | relative index (5+) | §4.3.4 |

In Insert with Name Reference, `T = 1` names a static entry and `T = 0` an entry by its
encoder-stream relative index (§3.2.5).

**Decoder instructions (§4.4).**

| Instruction | First octet | Field | RFC 9204 |
| --- | --- | --- | --- |
| Section Acknowledgment | `1xxxxxxx` | stream ID (7+) | §4.4.1 |
| Stream Cancellation | `01xxxxxx` | stream ID (6+) | §4.4.2 |
| Insert Count Increment | `00xxxxxx` | increment (6+) | §4.4.3 |

`EncoderInstr.encode`/`decodeEncoderInstr` and `DecoderInstr.encode`/`decodeDecoderInstr` are
the wire formats (raw string literals only; Huffman coding is rejected, see
`Silmaril.Net.Qpack.String`). `decodeMany` reads a whole buffer of instructions; a streaming
reader holding back an incomplete trailing instruction is not modelled.

**Decoder semantics (§3.2, §4.3).** `DynTable.applyInstr` applies an encoder instruction to the
decoder's table. Every failure is `QPACK_ENCODER_STREAM_ERROR`: a capacity above the maximum
(§4.3.1), an invalid static index (§3.1), a relative index naming an evicted or never-inserted
entry (§2.2.3), or an entry larger than the capacity (§3.2.2). The name or entry referenced by
an insertion is read *before* the insertion evicts anything, as §3.2.2 cautions.
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry encodeInt decodeInt)

/-! ## Sequences -/

/-- Read items with `dec` until the input is exhausted (at most `fuel` of them). -/
def decodeManyFuel {α : Type} (dec : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, xs@(_ :: _) =>
    match dec xs with
    | none => none
    | some (x, rest) =>
      match decodeManyFuel dec k rest with
      | none => none
      | some ys => some (x :: ys)

/-- Read a whole buffer of items. Each item takes at least one octet, so the buffer length
bounds their number. -/
def decodeMany {α : Type} (dec : List UInt8 → Option (α × List UInt8)) (xs : List UInt8) :
    Option (List α) :=
  decodeManyFuel dec xs.length xs

/-! ## Encoder instructions (§4.3) -/

/-- An encoder instruction (§4.3). -/
inductive EncoderInstr where
  /-- Set Dynamic Table Capacity (§4.3.1). -/
  | setCapacity (capacity : Nat)
  /-- Insert with Name Reference (§4.3.2): `isStatic` is the `T` bit; `index` is a static
  index (`T = 1`) or an encoder-stream relative index (`T = 0`). -/
  | insertNameRef (isStatic : Bool) (index : Nat) (value : List UInt8)
  /-- Insert with Literal Name (§4.3.3). -/
  | insertLiteral (name value : List UInt8)
  /-- Duplicate (§4.3.4), by encoder-stream relative index. -/
  | duplicate (index : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Serialize an encoder instruction (raw string literals). -/
def EncoderInstr.encode : EncoderInstr → List UInt8
  | .setCapacity c => encodeInt 5 0x20 c
  | .insertNameRef s i v => encodeInt 6 (if s then 0xc0 else 0x80) i ++ encodeStringN 8 0 v
  | .insertLiteral n v => encodeStringN 6 0x40 n ++ encodeStringN 8 0 v
  | .duplicate i => encodeInt 5 0x00 i

/-- Read one encoder instruction, dispatching on the first octet (§4.3). -/
def decodeEncoderInstr : List UInt8 → Option (EncoderInstr × List UInt8)
  | [] => none
  | b :: bs =>
    if 128 ≤ b.toNat then
      match decodeInt 6 (b :: bs) with
      | none => none
      | some (i, r) =>
        match decodeStringN 8 r with
        | none => none
        | some (v, r') => some (.insertNameRef (decide (192 ≤ b.toNat)) i v, r')
    else if 64 ≤ b.toNat then
      match decodeStringN 6 (b :: bs) with
      | none => none
      | some (n, r) =>
        match decodeStringN 8 r with
        | none => none
        | some (v, r') => some (.insertLiteral n v, r')
    else if 32 ≤ b.toNat then (decodeInt 5 (b :: bs)).map fun (c, r) => (.setCapacity c, r)
    else (decodeInt 5 (b :: bs)).map fun (i, r) => (.duplicate i, r)

/-- Serialize a sequence of encoder instructions (an encoder stream's payload). -/
def encodeEncoderInstrs (is : List EncoderInstr) : List UInt8 := is.flatMap EncoderInstr.encode

/-- Read an encoder stream's payload. -/
def decodeEncoderInstrs (xs : List UInt8) : Option (List EncoderInstr) :=
  decodeMany decodeEncoderInstr xs

/-! ## Decoder instructions (§4.4) -/

/-- A decoder instruction (§4.4). -/
inductive DecoderInstr where
  /-- Section Acknowledgment (§4.4.1). -/
  | sectionAck (streamId : Nat)
  /-- Stream Cancellation (§4.4.2). -/
  | streamCancel (streamId : Nat)
  /-- Insert Count Increment (§4.4.3). -/
  | insertCountIncrement (increment : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Serialize a decoder instruction. -/
def DecoderInstr.encode : DecoderInstr → List UInt8
  | .sectionAck s => encodeInt 7 0x80 s
  | .streamCancel s => encodeInt 6 0x40 s
  | .insertCountIncrement k => encodeInt 6 0x00 k

/-- Read one decoder instruction, dispatching on the first octet (§4.4). -/
def decodeDecoderInstr : List UInt8 → Option (DecoderInstr × List UInt8)
  | [] => none
  | b :: bs =>
    if 128 ≤ b.toNat then (decodeInt 7 (b :: bs)).map fun (s, r) => (.sectionAck s, r)
    else if 64 ≤ b.toNat then (decodeInt 6 (b :: bs)).map fun (s, r) => (.streamCancel s, r)
    else (decodeInt 6 (b :: bs)).map fun (k, r) => (.insertCountIncrement k, r)

/-- Serialize a sequence of decoder instructions (a decoder stream's payload). -/
def encodeDecoderInstrs (is : List DecoderInstr) : List UInt8 := is.flatMap DecoderInstr.encode

/-- Read a decoder stream's payload. -/
def decodeDecoderInstrs (xs : List UInt8) : Option (List DecoderInstr) :=
  decodeMany decodeDecoderInstr xs

/-! ## Applying encoder instructions to the decoder's table (§3.2, §4.3) -/

namespace DynTable

/-- Insert, reporting an oversize entry as `QPACK_ENCODER_STREAM_ERROR` (§3.2.2). -/
def insertOrErr (t : DynTable) (e : Entry) : Except QpackError DynTable :=
  match t.insert e with
  | some t' => .ok t'
  | none => .error .encoderStreamError

/-- Apply one encoder instruction (§4.3); every failure is `QPACK_ENCODER_STREAM_ERROR`. -/
def applyInstr (t : DynTable) : EncoderInstr → Except QpackError DynTable
  | .setCapacity c =>
    match t.setCapacity c with
    | some t' => .ok t'
    | none => .error .encoderStreamError
  | .insertNameRef true i v =>
    match staticLookup i with
    | some e => t.insertOrErr ⟨e.name, v⟩
    | none => .error .encoderStreamError
  | .insertNameRef false r v =>
    match t.lookupRel r with
    | some e => t.insertOrErr ⟨e.name, v⟩
    | none => .error .encoderStreamError
  | .insertLiteral n v => t.insertOrErr ⟨n, v⟩
  | .duplicate r =>
    match t.lookupRel r with
    | some e => t.insertOrErr e
    | none => .error .encoderStreamError

/-- Apply encoder instructions in order, stopping at the first error. -/
def applyInstrs (t : DynTable) : List EncoderInstr → Except QpackError DynTable
  | [] => .ok t
  | i :: is =>
    match t.applyInstr i with
    | .ok t' => t'.applyInstrs is
    | .error e => .error e

end DynTable

end Silmaril.Net.Qpack

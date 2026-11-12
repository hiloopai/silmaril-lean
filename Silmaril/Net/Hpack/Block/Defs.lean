module

public import Silmaril.Net.Hpack.Integer.Defs
public import Silmaril.Net.Hpack.Table.Defs

@[expose] public section

/-!
# HPACK field representations and field block decoding (RFC 7541 §3, §6)

A field block is a sequence of *representations* (§6), each of which a decoder processes in
order (§3.2), emitting header fields and updating its dynamic table:

| Representation | First octet | Prefix | RFC 7541 |
| --- | --- | --- | --- |
| Indexed field | `1xxxxxxx` | 7 | §6.1 |
| Literal with incremental indexing | `01xxxxxx` | 6 | §6.2.1 |
| Dynamic table size update | `001xxxxx` | 5 | §6.3 |
| Literal never indexed | `0001xxxx` | 4 | §6.2.3 |
| Literal without indexing | `0000xxxx` | 4 | §6.2.2 |

A literal names its field by an index (non-zero) or by a literal string (index `0`), then
gives the value as a string literal (§6.2).

`encodeRep`/`decodeRep` are the wire format (raw string literals only: `decodeString` rejects
Huffman coding, see `Silmaril.Net.Hpack.Integer`). `processRep`/`processReps` are the decoder's
semantics (§3.2, §4): indexed fields are looked up, literals with incremental indexing are
inserted, size updates change the maximum. `decodeBlock` composes the two.

**Ordering of size updates (§4.2).** "This dynamic table size update MUST occur at the
beginning of the first field block following the change"; a size update after a field
representation is a decoding error here (`processReps` tracks whether a field was seen).

**Never-indexed literals (§6.2.3, §7.1.3).** They protect sensitive values (such as short
cookies) from compression-based attacks: an intermediary MUST forward them with the same
representation. Here they never touch the dynamic table (`processRep_never` in `Thms`).
-/

namespace Silmaril.Net.Hpack

/-- How a literal interacts with the dynamic table (§6.2). -/
inductive Indexing where
  | incremental | without | never
  deriving DecidableEq, Repr, Inhabited

/-- The name of a literal: an index (§2.3.3) or a literal string. -/
inductive NameRef where
  | indexed (i : Nat)
  | literal (name : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- A field representation (§6). -/
inductive Rep where
  | indexed (i : Nat)
  | literal (ix : Indexing) (name : NameRef) (value : List UInt8)
  | sizeUpdate (m : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Well-formed: an indexed name is not index `0` (which denotes a literal name, §6.2). -/
def Rep.WellFormed : Rep → Prop
  | .literal _ (.indexed i) _ => i ≠ 0
  | _ => True

/-- The prefix width and flag bits of each literal kind (§6.2). -/
def Indexing.prefixBits : Indexing → Nat
  | .incremental => 6 | .without => 4 | .never => 4

def Indexing.flagBits : Indexing → Nat
  | .incremental => 0x40 | .without => 0x00 | .never => 0x10

/-- Serialize a representation (raw string literals). -/
def encodeRep : Rep → List UInt8
  | .indexed i => encodeInt 7 0x80 i
  | .sizeUpdate m => encodeInt 5 0x20 m
  | .literal ix (.indexed i) v => encodeInt ix.prefixBits ix.flagBits i ++ encodeString v
  | .literal ix (.literal n) v =>
    encodeInt ix.prefixBits ix.flagBits 0 ++ encodeString n ++ encodeString v

/-- Read the rest of a literal of kind `ix` (§6.2): name index or literal name, then value. -/
def decodeLiteral (ix : Indexing) (xs : List UInt8) : Option (Rep × List UInt8) :=
  match decodeInt ix.prefixBits xs with
  | none => none
  | some (i, r) =>
    let name? : Option (NameRef × List UInt8) :=
      if i = 0 then (decodeString r).map fun (s, r') => (.literal s, r')
      else some (.indexed i, r)
    match name? with
    | none => none
    | some (nr, r') =>
      match decodeString r' with
      | none => none
      | some (v, r'') => some (.literal ix nr v, r'')

/-- Read one representation, dispatching on the first octet (§6). -/
def decodeRep : List UInt8 → Option (Rep × List UInt8)
  | [] => none
  | b :: bs =>
    if 128 ≤ b.toNat then (decodeInt 7 (b :: bs)).map fun (i, r) => (.indexed i, r)
    else if 64 ≤ b.toNat then decodeLiteral .incremental (b :: bs)
    else if 32 ≤ b.toNat then (decodeInt 5 (b :: bs)).map fun (m, r) => (.sizeUpdate m, r)
    else if 16 ≤ b.toNat then decodeLiteral .never (b :: bs)
    else decodeLiteral .without (b :: bs)

/-- Read representations until the input is exhausted (at most `fuel` of them). -/
def decodeRepsFuel : Nat → List UInt8 → Option (List Rep)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, xs@(_ :: _) =>
    match decodeRep xs with
    | none => none
    | some (r, rest) =>
      match decodeRepsFuel k rest with
      | none => none
      | some rs => some (r :: rs)

/-- Read a whole field block into representations. Each representation takes at least one
octet, so the block length bounds their number. -/
def decodeReps (xs : List UInt8) : Option (List Rep) := decodeRepsFuel xs.length xs

/-- Serialize representations. -/
def encodeReps (rs : List Rep) : List UInt8 := rs.flatMap encodeRep

/-! ## Decoder semantics (§3.2, §4) -/

/-- Resolve a name reference against the tables. -/
def DynTable.resolveName (t : DynTable) : NameRef → Option (List UInt8)
  | .indexed i => (t.lookup i).map Entry.name
  | .literal n => some n

/-- Process one representation: the emitted field (if any) and the next table. `none` is a
decoding error (`COMPRESSION_ERROR` in HTTP/2, RFC 9113 §4.3). -/
def processRep (t : DynTable) : Rep → Option (Option Entry × DynTable)
  | .indexed i => (t.lookup i).map fun e => (some e, t)
  | .sizeUpdate m => (t.setMaxSize m).map fun t' => (none, t')
  | .literal ix nr v =>
    match t.resolveName nr with
    | none => none
    | some n =>
      let e : Entry := ⟨n, v⟩
      some (some e, if ix = .incremental then t.insert e else t)

/-- Process a field block's representations (§3.2), rejecting a size update that follows a
field representation (§4.2). `seen` records whether a field was already emitted. -/
def processRepsFrom (seen : Bool) (t : DynTable) : List Rep → Option (List Entry × DynTable)
  | [] => some ([], t)
  | r :: rs =>
    match r with
    | .sizeUpdate _ => if seen then none else
      match processRep t r with
      | none => none
      | some (_, t') => processRepsFrom seen t' rs
    | _ =>
      match processRep t r with
      | none => none
      | some (e?, t') =>
        match processRepsFrom true t' rs with
        | none => none
        | some (es, t'') => some (e?.toList ++ es, t'')

/-- Process a field block's representations from its start. -/
def processReps (t : DynTable) (rs : List Rep) : Option (List Entry × DynTable) :=
  processRepsFrom false t rs

/-- Decode a field block (§3.2): its header fields, in order, and the next dynamic table. -/
def decodeBlock (t : DynTable) (xs : List UInt8) : Option (List Entry × DynTable) :=
  match decodeReps xs with
  | none => none
  | some rs => processReps t rs

end Silmaril.Net.Hpack

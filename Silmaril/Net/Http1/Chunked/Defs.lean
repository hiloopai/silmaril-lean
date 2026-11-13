module

public import Silmaril.Net.Http1.Message.Defs

/-!
# The chunked transfer coding (RFC 9112 §7.1)

```
chunked-body   = *chunk
                 last-chunk
                 trailer-section
                 CRLF
chunk          = chunk-size [ chunk-ext ] CRLF
                 chunk-data CRLF
chunk-size     = 1*HEXDIG
last-chunk     = 1*("0") [ chunk-ext ] CRLF
chunk-data     = 1*OCTET ; a sequence of chunk-size octets
chunk-ext      = *( BWS ";" BWS chunk-ext-name
                    [ BWS "=" BWS chunk-ext-val ] )        ; §7.1.1
chunk-ext-name = token
chunk-ext-val  = token / quoted-string
trailer-section = *( field-line CRLF )                     ; §7.1.2
```

`Chunked` is a decoded chunked body: its chunks (extensions and data), the extensions of the
last chunk, and the trailer fields. Its `content` is the concatenation of the chunk data:
the chunked coding is a *rechunking* of the content byte stream, and every chunking of the
same content carries the same content (`Silmaril.Net.Http1.Chunked.Thms`). In the terms of
`docs/projects/wasm-wasi.md`, `chunks.map data` is a byte-chunk stream and two chunked bodies with
the same trailers are equivalent exactly when their chunk streams are `ChunkEq`
(`cs.flatten = ds.flatten`).

Choices:

* `chunk-size` is read as a natural number of any size (RFC 9112 §7.1: recipients "MUST
  anticipate potentially large hexadecimal numerals"; a resource limit belongs to the caller).
  Leading zeros are accepted; the serializer writes minimal lowercase hex.
* `chunk-ext` is kept as its raw octets (`Chunk.ext`, everything between the size and the
  `CRLF`), accepted when `isChunkExt` holds: a finite automaton transcribing the §7.1.1 ABNF
  (`chunkExtStep`), proved to accept exactly the ABNF as an inductive relation
  (`isChunkExt_iff_abnf`, `ChunkExtAbnf`). Extensions are not interpreted (§7.1.1: a recipient "MUST ignore
  unrecognized chunk extensions").
* The trailer section uses the field-line grammar of the head (`Grammar.fields`).
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

/-! ## Chunk extensions -/

/-- `";"`. -/
abbrev SEMI : UInt8 := 0x3B
/-- `"="`. -/
abbrev EQ : UInt8 := 0x3D
/-- `DQUOTE`. -/
abbrev DQUOTE : UInt8 := 0x22
/-- `"\"`. -/
abbrev BSLASH : UInt8 := 0x5C

/-- `qdtext = HTAB / SP / %x21 / %x23-5B / %x5D-7E / obs-text` (RFC 9110 §5.6.4). -/
def isQdtext (c : UInt8) : Bool :=
  c == HTAB || c == SP || c == 0x21 || (0x23 ≤ c && c ≤ 0x5B) || (0x5D ≤ c && c ≤ 0x7E) ||
    isObsText c

/-- States of the chunk-ext automaton. -/
inductive ExtState where
  /-- Nothing read yet (accepting: no extensions). -/
  | start
  /-- Whitespace before a `";"`. -/
  | ws
  /-- After `";"` and optional whitespace, before the name. -/
  | semi
  /-- In the name (accepting). -/
  | name
  /-- Whitespace after the name. -/
  | nameWs
  /-- After `"="` and optional whitespace, before the value. -/
  | eq
  /-- In a token value (accepting). -/
  | token
  /-- Inside a quoted string. -/
  | quoted
  /-- After a backslash inside a quoted string. -/
  | escape
  /-- After the closing quote (accepting). -/
  | closed
  deriving DecidableEq, Repr

/-- One step of the automaton for `chunk-ext` (RFC 9112 §7.1.1, with `BWS` = `OWS`,
`token` from RFC 9110 §5.6.2 and `quoted-string` from §5.6.4); `none` rejects. -/
def chunkExtStep : ExtState → UInt8 → Option ExtState
  | .start, c | .ws, c | .closed, c =>
    if c == SEMI then some .semi else if isWS c then some .ws else none
  | .token, c =>
    if isTchar c then some .token else if c == SEMI then some .semi
    else if isWS c then some .ws else none
  | .semi, c => if isWS c then some .semi else if isTchar c then some .name else none
  | .name, c =>
    if isTchar c then some .name else if isWS c then some .nameWs
    else if c == EQ then some .eq else if c == SEMI then some .semi else none
  | .nameWs, c => if isWS c then some .nameWs else if c == EQ then some .eq
    else if c == SEMI then some .semi else none
  | .eq, c => if isWS c then some .eq else if isTchar c then some .token
    else if c == DQUOTE then some .quoted else none
  | .quoted, c => if c == DQUOTE then some .closed else if c == BSLASH then some .escape
    else if isQdtext c then some .quoted else none
  | .escape, c => if isFieldByte c then some .quoted else none

/-- The accepting states: the end of a (possibly empty) list of extensions. -/
def ExtState.accepting : ExtState → Bool
  | .start | .name | .token | .closed => true
  | _ => false

/-- Run the automaton. -/
def chunkExtRun : ExtState → Bytes → Option ExtState
  | s, [] => some s
  | s, c :: cs => (chunkExtStep s c).bind fun s' => chunkExtRun s' cs

/-- `l` is a `chunk-ext` (the octets between `chunk-size` and `CRLF`). The first two
conjuncts are implied by the automaton; they are stated so that the parser's laws do not
depend on it. -/
def isChunkExt (l : Bytes) : Bool :=
  l.all isFieldByte && (l.head?.all fun c => c == SEMI || isWS c) &&
    ((chunkExtRun .start l).map ExtState.accepting == some true)

/-- `*( qdtext / quoted-pair )` (RFC 9110 §5.6.4). -/
inductive QuotedBody : Bytes → Prop where
  | nil : QuotedBody []
  | qdtext {c : UInt8} {q : Bytes} : isQdtext c = true → QuotedBody q → QuotedBody (c :: q)
  | pair {c : UInt8} {q : Bytes} : isFieldByte c = true → QuotedBody q →
      QuotedBody (BSLASH :: c :: q)

/-- The `chunk-ext` ABNF of RFC 9112 §7.1.1 as a relation:
items `BWS ";" BWS name [ BWS "=" BWS value ]`. -/
inductive ChunkExtItem : Bytes → Prop where
  | name {w₁ w₂ n : Bytes} : (∀ b ∈ w₁, isWS b = true) → (∀ b ∈ w₂, isWS b = true) →
      IsToken n → ChunkExtItem (w₁ ++ [SEMI] ++ w₂ ++ n)
  | token {w₁ w₂ n w₃ w₄ v : Bytes} : (∀ b ∈ w₁ ++ w₂ ++ w₃ ++ w₄, isWS b = true) →
      IsToken n → IsToken v → ChunkExtItem (w₁ ++ [SEMI] ++ w₂ ++ n ++ w₃ ++ [EQ] ++ w₄ ++ v)
  | quoted {w₁ w₂ n w₃ w₄ q : Bytes} : (∀ b ∈ w₁ ++ w₂ ++ w₃ ++ w₄, isWS b = true) →
      IsToken n → QuotedBody q →
      ChunkExtItem (w₁ ++ [SEMI] ++ w₂ ++ n ++ w₃ ++ [EQ] ++ w₄ ++ [DQUOTE] ++ q ++ [DQUOTE])

/-- `chunk-ext = *( item )`. -/
inductive ChunkExtAbnf : Bytes → Prop where
  | nil : ChunkExtAbnf []
  | cons {i r : Bytes} : ChunkExtItem i → ChunkExtAbnf r → ChunkExtAbnf (i ++ r)


/-! ## Decoded bodies -/

/-- A chunk: its raw extensions and its data (nonempty). -/
structure Chunk where
  ext : Bytes
  data : Bytes
  deriving DecidableEq, Repr, Inhabited

/-- A chunked body (RFC 9112 §7.1). -/
structure Chunked where
  chunks : List Chunk
  lastExt : Bytes
  trailers : List FieldLine
  deriving DecidableEq, Repr, Inhabited

/-- The content: the chunk data, concatenated (RFC 9112 §7.1.3, "decoding chunked"). -/
def Chunked.content (c : Chunked) : Bytes := (c.chunks.map Chunk.data).flatten

def Chunk.Valid (c : Chunk) : Prop := c.data ≠ [] ∧ isChunkExt c.ext = true

def Chunked.Valid (c : Chunked) : Prop :=
  (∀ k ∈ c.chunks, k.Valid) ∧ isChunkExt c.lastExt = true ∧ ∀ f ∈ c.trailers, f.Valid

instance (c : Chunk) : Decidable c.Valid := inferInstanceAs (Decidable (_ ∧ _))
instance (c : Chunked) : Decidable c.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The chunks of `cs` with no extensions (one per nonempty piece). -/
def Chunked.ofPieces (cs : List Bytes) (trailers : List FieldLine := []) : Chunked :=
  ⟨(cs.filter (· ≠ [])).map fun d => ⟨[], d⟩, [], trailers⟩

/-! ## Serializer -/

/-- `chunk-size [ chunk-ext ] CRLF`. -/
def encChunkLine (n : Nat) (ext : Bytes) : Bytes := hexDigits n ++ ext ++ CRLF

/-- `chunk = chunk-size [ chunk-ext ] CRLF chunk-data CRLF`. -/
def encChunk (c : Chunk) : Bytes := encChunkLine c.data.length c.ext ++ c.data ++ CRLF

/-- `chunked-body`, the last chunk written `0`. -/
def encChunked (c : Chunked) : Bytes :=
  (c.chunks.map encChunk).flatten ++ encChunkLine 0 c.lastExt ++ encFields c.trailers

/-! ## Grammar and parser -/

namespace Grammar

open Silmaril.Parse.ByteParse.Grammar (lit then_)

/-- The extension octets: `[]` if the size ends at `CR`; otherwise the octet `c` that ended
the size (`";"` or whitespace) and the rest of the line, checked by `isChunkExt`. -/
@[inline] def chunkExtTail (c : UInt8) : Grammar Bytes :=
  if c = CR then (PG.expect "LF" LF).map fun _ => []
  else
    ((delim "chunk-ext" isFieldByte CR false).bind fun r =>
      (PG.expect "LF" LF).map fun _ => c :: r).filterMap "chunk-ext" fun e =>
        if isChunkExt e then some e else none

/-- `chunk-size [ chunk-ext ] CRLF`: the size and the raw extensions. -/
@[inline] def chunkLine : Grammar (Nat × Bytes) :=
  (Grammar.runThen isHexDig).bind fun r =>
    if r.1 = [] then Silmaril.Parse.ByteParse.Grammar.fail
    else (chunkExtTail r.2).map fun e => (hexValue r.1, e)

/-- `n` octets of chunk data, then `CRLF`. -/
@[inline] def chunkData (n : Nat) : Grammar Bytes :=
  (Silmaril.Parse.ByteParse.Grammar.bytes n).bind fun d =>
    (lit CRLF).map fun _ => d.data.toList

/-- A chunked body with at most `k - 1` chunks and `k - 1` trailer fields. -/
def chunked : Nat → Grammar Chunked
  | 0 => Silmaril.Parse.ByteParse.Grammar.fail
  | k + 1 => chunkLine.bind fun r =>
    if r.1 = 0 then (fields (k + 1)).map fun tr => ⟨[], r.2, tr⟩
    else (chunkData r.1).bind fun d =>
      (chunked k).map fun c => { c with chunks := ⟨r.2, d⟩ :: c.chunks }

end Grammar

/-- Decode a chunked body starting at position `i` of `bs`: the body and the position after
it. -/
def parseChunked (bs : ByteArray) (i : Nat) : Res Chunked :=
  (Grammar.chunked (bs.size + 1)).parse bs bs.size i

end Silmaril.Net.Http1

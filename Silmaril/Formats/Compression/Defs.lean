module

public import Init

/-!
# Lossless compression: the framework

A small vocabulary shared by every compressed format in this library. It fixes
what a decoder is, which laws a codec states, and how containers, checksums,
multi-member files and streaming decoders are put together. Formats instantiate
it; they do not need to share anything else.

* `Decoder`: the **specification** of a compressed format is a partial function
  that decodes *one* self-delimiting member at the front of the input and returns
  its output with the unread rest. A whole-buffer decoder (`Decoder.whole`) and a
  multi-member decoder (`Decoder.members`) are derived from it.
* `Encoder`, `RoundTrip`, `Codec`: an encoder is any function whose output the
  decoder reads back exactly, whatever follows it. Encoders are optional; the
  decoder alone defines the format (`Decoder.Decodes`).
* `Decoder.Consumes`, `Decoder.Local`: the member boundary laws. `Consumes` says
  the rest is a suffix of the input; `Local` says bytes appended after a member
  do not change how it decodes.
* `Framing`, `Framing.wrap`: a container (header, body, trailer) around a body
  decoder, e.g. zlib (RFC 1950) and gzip (RFC 1952) around DEFLATE (RFC 1951).
* `Checksum`: an incremental 32-bit checksum (`init`, `update`, `finish`), such
  as Adler-32 and CRC-32.
* `Incremental`: a streaming decoder that is offered input in calls, with the
  soundness and completeness laws that relate it to a `Decoder`.

Byte strings are `List UInt8` here, the normal form for proofs. Formats that
expose `ByteArray` interfaces relate them to these list-level decoders.

## Where future formats go

Each format is a topic `Silmaril/Formats/Compression/<Format>/{Defs,Thms}.lean`
that defines its member `Decoder` (and optionally an `Encoder`), and states the
laws above. None of these is implemented yet:

* **zstd** (RFC 8878): a frame is a `Framing` (magic, frame header, optional
  XXH64 content checksum) around a block decoder whose literals use Huffman and
  whose sequences use FSE; skippable frames and frame concatenation are
  `Decoder.members`.
* **bzip2**: a stream header and per-block CRC-32 framing around the inverse
  BWT, MTF/RLE and Huffman stages; concatenated streams are `Decoder.members`.
* **xz** (LZMA2): the xz container (stream header/footer, block headers, index,
  CRC-32/CRC-64/SHA-256 checks) is a `Framing` around the LZMA2 chunk decoder.
* **brotli** (RFC 7932): a raw self-delimiting `Decoder` with a built-in
  dictionary, like raw DEFLATE.
* **LZ4**: the LZ4 frame format (magic, frame descriptor, optional xxHash-32
  block and content checksums) is a `Framing` around LZ4 block decoding.

A new 32-bit checksum is a `Checksum` (`XxHash` gives XXH32 and the low half of
XXH64, the LZ4 and zstd content checksums); a streaming decoder for a new
format is an `Incremental` proved `Sound` against the format's `Decoder`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

/-! ## Decoders -/

/-- A **member decoder**: decode one compressed member at the front of the
input, returning the decoded bytes and the unread input after the member.
`none` means the input does not start with a valid member. -/
abbrev Decoder := List UInt8 → Option (List UInt8 × List UInt8)

namespace Decoder

/-- A decoder reporting errors in `Except`, read as a member decoder. -/
def ofExcept {ε : Type} (d : List UInt8 → Except ε (List UInt8 × List UInt8)) : Decoder :=
  fun bytes => (d bytes).toOption

/-- A successful decode consumes a prefix: the rest is a suffix of the input. -/
def Consumes (d : Decoder) : Prop :=
  ∀ ⦃bytes out rest : List UInt8⦄, d bytes = some (out, rest) → rest <:+ bytes

/-- Bytes after a member never change how it decodes: they are passed through as
part of the rest. This is the law that makes members self-delimiting. -/
def Local (d : Decoder) : Prop :=
  ∀ ⦃bytes out rest : List UInt8⦄ (tail : List UInt8),
    d bytes = some (out, rest) → d (bytes ++ tail) = some (out, rest ++ tail)

/-- Decode a whole buffer holding exactly one member and nothing after it. -/
def whole (d : Decoder) (bytes : List UInt8) : Option (List UInt8) :=
  match d bytes with
  | some (out, []) => some out
  | _ => none

/-- `compressed` is an encoding of `data`: the format's meaning, as a relation. -/
def Decodes (d : Decoder) (compressed data : List UInt8) : Prop :=
  d.whole compressed = some data

/-- Decode members one after another until the input is used up, concatenating
their outputs. `fuel` bounds the number of members. The input must hold at least
one member, and every byte must belong to one. -/
def membersFuel (d : Decoder) : Nat → List UInt8 → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | fuel + 1, bytes, acc =>
    match d bytes with
    | none => none
    | some (out, []) => some (acc ++ out)
    | some (out, rest) => d.membersFuel fuel rest (acc ++ out)

/-- **Multi-member decoding**: one or more concatenated members (gzip's
RFC 1952 §2.2 rule, also used by bzip2, xz and zstd files). A decoder that makes
progress needs at most one member per input byte, so the fuel is the length. -/
def members (d : Decoder) (bytes : List UInt8) : Option (List UInt8) :=
  d.membersFuel (bytes.length + 1) bytes []

end Decoder

/-! ## Encoders and codecs -/

/-- An encoder: any function from data to a compressed member. -/
abbrev Encoder := List UInt8 → List UInt8

/-- **Round trip**: the decoder reads back exactly the encoded data, and leaves
whatever follows the member untouched. -/
def RoundTrip (d : Decoder) (e : Encoder) : Prop :=
  ∀ data rest : List UInt8, d (e data ++ rest) = some (data, rest)

/-- A lossless codec: a decoder with an encoder that round-trips through it. -/
structure Codec where
  decode : Decoder
  encode : Encoder
  roundTrip : RoundTrip decode encode

/-! ## Containers -/

/-- A **container** around a body stream: a header parser that yields metadata
of type `H`, and a trailer check that sees the metadata and the decoded output
(for a length or checksum) and returns the input after the trailer. -/
structure Framing (H : Type) where
  header : List UInt8 → Option (H × List UInt8)
  trailer : H → List UInt8 → List UInt8 → Option (List UInt8)

namespace Framing

variable {H : Type}

/-- The member decoder of a container: header, body, then trailer. -/
def wrap (f : Framing H) (body : Decoder) : Decoder := fun bytes =>
  match f.header bytes with
  | none => none
  | some (h, afterHeader) =>
    match body afterHeader with
    | none => none
    | some (out, afterBody) =>
      match f.trailer h out afterBody with
      | none => none
      | some rest => some (out, rest)

/-- Header and trailer consume prefixes. -/
def Consumes (f : Framing H) : Prop :=
  (∀ ⦃bytes h rest⦄, f.header bytes = some (h, rest) → rest <:+ bytes) ∧
  (∀ ⦃h out bytes rest⦄, f.trailer h out bytes = some rest → rest <:+ bytes)

/-- Header and trailer ignore bytes appended after them. -/
def Local (f : Framing H) : Prop :=
  (∀ ⦃bytes h rest⦄ (tail : List UInt8),
    f.header bytes = some (h, rest) → f.header (bytes ++ tail) = some (h, rest ++ tail)) ∧
  (∀ ⦃h out bytes rest⦄ (tail : List UInt8),
    f.trailer h out bytes = some rest → f.trailer h out (bytes ++ tail) = some (rest ++ tail))

/-- The trailer the container accepts after output `out` is exactly `spec out`
(for instance a checksum of `out`, serialised). -/
def TrailerIs (f : Framing H) (spec : List UInt8 → List UInt8) : Prop :=
  ∀ ⦃h out bytes rest⦄, f.trailer h out bytes = some rest → bytes = spec out ++ rest

/-- `hdr` is a header the container accepts, and `trl out` a trailer it accepts
after output `out`: what an encoder writes. -/
def Writes (f : Framing H) (hdr : List UInt8) (trl : List UInt8 → List UInt8) : Prop :=
  ∀ rest : List UInt8, ∃ h, f.header (hdr ++ rest) = some (h, rest) ∧
    ∀ out tail : List UInt8, f.trailer h out (trl out ++ tail) = some tail

/-- The container's encoder around a body encoder. -/
def encode (hdr : List UInt8) (body : Encoder) (trl : List UInt8 → List UInt8) : Encoder :=
  fun data => hdr ++ body data ++ trl data

end Framing

/-! ## Checksums -/

/-- An **incremental 32-bit checksum**: a running state updated byte by byte,
finished into the 32-bit check value. Streaming decoders keep the running
state; specifications use `digest`. -/
structure Checksum where
  State : Type
  init : State
  update : State → UInt8 → State
  finish : State → UInt32

/-- The check value of a byte string. -/
def Checksum.digest (c : Checksum) (bytes : List UInt8) : UInt32 :=
  c.finish (bytes.foldl c.update c.init)

/-! ## Streaming decoders -/

/-- What a streaming decoder reports after a sequence of calls. -/
inductive Status where
  | running
  | done (output : List UInt8)
  | failed

/-- A **streaming decoder**: a machine that is offered input in calls of type
`Call` (each call may also carry scheduling or output-capacity limits). `start`
is the machine that has already been offered its argument. -/
structure Incremental where
  Machine : Type
  Call : Type
  start : List UInt8 → Machine
  step : Machine → Call → Machine
  offered : Call → List UInt8
  status : Machine → Status

namespace Incremental

/-- Apply a call schedule in order. -/
def run (i : Incremental) (m : i.Machine) (calls : List i.Call) : i.Machine :=
  calls.foldl i.step m

/-- The input offered by a call schedule. -/
def delivered (i : Incremental) (calls : List i.Call) : List UInt8 :=
  calls.flatMap i.offered

/-- **Soundness**: whenever a schedule finishes, its output is the member
decoder's output on everything offered so far, and the member boundary is fixed:
any further input is passed through untouched. -/
def Sound (i : Incremental) (d : Decoder) : Prop :=
  ∀ (initial : List UInt8) (calls : List i.Call) (out : List UInt8),
    i.status (i.run (i.start initial) calls) = .done out →
      ∃ rest, ∀ future, d (initial ++ i.delivered calls ++ future) = some (out, rest ++ future)

/-- **Rejection soundness**: a failed schedule means the member decoder rejects
the offered input, however it continues. -/
def RejectSound (i : Incremental) (d : Decoder) : Prop :=
  ∀ (initial : List UInt8) (calls : List i.Call),
    i.status (i.run (i.start initial) calls) = .failed →
      ∀ future, d (initial ++ i.delivered calls ++ future) = none

/-- **Completeness**: every member the decoder accepts is finished by some
schedule that offers no further input. -/
def Complete (i : Incremental) (d : Decoder) : Prop :=
  ∀ ⦃bytes out rest : List UInt8⦄, d bytes = some (out, rest) →
    ∃ calls : List i.Call, i.delivered calls = [] ∧ i.status (i.run (i.start bytes) calls) = .done out

end Incremental

end Silmaril.Formats.Compression

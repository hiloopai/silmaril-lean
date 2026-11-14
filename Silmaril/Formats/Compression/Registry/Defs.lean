module

public import Silmaril.Formats.Compression.Defs
public import Silmaril.Formats.Compression.Gzip.Defs
public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Zstd.Defs

/-!
# Named content codings: the HTTP Content Coding registry as data

The IANA "HTTP Content Coding Registry" (RFC 9110 §16.6.1, §18.6, and the later
registrations of RFC 7932, RFC 8188, RFC 8878/RFC 9659 and RFC 9842) and the
coding names of the "HTTP Transfer Coding Registry" (RFC 9112 §7.3), together
with what this library knows about each coding.

* `Coding`: the registered content codings, `Coding.name` their lowercase token,
  `aliases` the deprecated `x-gzip` and `x-compress` (RFC 9110 §8.4.1.1, §8.4.1.3);
* `Entry`, `registry`: one row per registered name (content or transfer layer,
  reference, `Status`); `transferOnlyNames`: `chunked` and the reserved
  `trailers`, which are transfer codings only (RFC 9112 §7) and never content
  codings; `identity` is content-only and reserved (RFC 9110 §12.5.3);
* `ofName?`: case-insensitive lookup (RFC 9110 §8.4.1: "All content codings are
  case-insensitive"), resolving aliases;
* `Externals`, `decoder?`, `encoder?`: the whole-buffer decoder of a coding.
  `identity` is the identity, `gzip` is a gzip **file** (one or more members,
  `Gzip.decoder.members`), and `deflate` is the **zlib** format
  (`Zlib.decoder.whole`; RFC 9110 §8.4.1.2), not raw DEFLATE. `zstd` is the
  *partial* `Zstd.decode` (frames of raw and RLE blocks only; compressed blocks
  are rejected) with the window limit `Externals.zstdWindowMax`. `aes128gcm`
  (RFC 8188) needs keying material and belongs to the crypto track: its decoder is
  an abstract parameter (`Externals.aes128gcm`). Every other coding is planned;
* `DecodeError`, `stage`, `guarded`: one decoding step with explicit
  `unsupported`, `malformed` and `tooLarge` errors;
* `decodeChain`, `encodeChain`, `guardedChain`: Content-Encoding lists the
  codings in the order they were applied (RFC 9110 §8.4), so decoding applies
  them in reverse; `guardedChain` checks every stage's output against a bound;
* `Profile`: a deployment's settings: the allowed codings, the maximum decoded
  size, the maximum expansion ratio, the chain length and whether a compression
  dictionary is available (`dcb`, `dcz`, RFC 9842); `Profile.supports` and
  `Profile.limit`;
* `Decoder.bounded`: a member decoder with a `tooLarge` error.

**What the bound means.** `guarded` and `Decoder.bounded` are *semantic*
bounds: they are defined from the list-level specification, which computes the
full output before its length is compared with the limit. They say which inputs
a resource-safe decoder must reject and that it agrees with the specification on
all others; they do not by themselves bound the memory of an evaluation. The
operational side is the streaming inflater (`Inflate`), whose calls carry an
output capacity: `Registry.sound_bounded` (in `Registry.Thms`) connects a
finished streaming run whose output fits the limit to `Decoder.bounded`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Registry

/-! ## Names -/

/-- A coding name, as the octets of its token. -/
abbrev Name := List UInt8

/-- The ASCII octets of a string literal (all names here are ASCII). -/
def ascii (s : String) : Name := s.toList.map (fun c => c.toNat.toUInt8)

/-- ASCII lowercase of one octet (`A`–`Z` to `a`–`z`). -/
def lowerOctet (b : UInt8) : UInt8 := if 0x41 ≤ b ∧ b ≤ 0x5A then b + 0x20 else b

/-- ASCII lowercase of a name: the case-insensitive normal form. -/
def lower (n : Name) : Name := n.map lowerOctet

/-! ## The registered content codings -/

/-- The content codings of the IANA HTTP Content Coding Registry. Aliases
(`x-gzip`, `x-compress`) are not separate codings. -/
inductive Coding where
  /-- `identity`: no encoding; reserved for Accept-Encoding (RFC 9110 §12.5.3). -/
  | identity
  /-- `gzip`: the gzip file format (RFC 9110 §8.4.1.3, RFC 1952). -/
  | gzip
  /-- `deflate`: the zlib format around DEFLATE (RFC 9110 §8.4.1.2, RFC 1950/1951). -/
  | deflate
  /-- `compress`: UNIX `compress`, adaptive LZW (RFC 9110 §8.4.1.1). -/
  | compress
  /-- `br`: Brotli (RFC 7932). -/
  | br
  /-- `zstd`: Zstandard (RFC 8878 §7.2, window limit RFC 9659). -/
  | zstd
  /-- `dcb`: dictionary-compressed Brotli (RFC 9842 §4). -/
  | dcb
  /-- `dcz`: dictionary-compressed Zstandard (RFC 9842 §5). -/
  | dcz
  /-- `aes128gcm`: encrypted content encoding (RFC 8188). -/
  | aes128gcm
  /-- `exi`: W3C Efficient XML Interchange. -/
  | exi
  /-- `pack200-gzip`: Java archive network transfer format (JSR 200). -/
  | pack200gzip
  deriving DecidableEq, Repr, Inhabited

/-- Every registered coding, in registry order. -/
def Coding.all : List Coding :=
  [.aes128gcm, .br, .compress, .dcb, .dcz, .deflate, .exi, .gzip, .identity, .pack200gzip, .zstd]

/-- The registered (lowercase) token of a coding. -/
def Coding.name : Coding → Name
  | .identity => ascii "identity"
  | .gzip => ascii "gzip"
  | .deflate => ascii "deflate"
  | .compress => ascii "compress"
  | .br => ascii "br"
  | .zstd => ascii "zstd"
  | .dcb => ascii "dcb"
  | .dcz => ascii "dcz"
  | .aes128gcm => ascii "aes128gcm"
  | .exi => ascii "exi"
  | .pack200gzip => ascii "pack200-gzip"

/-- Deprecated aliases a recipient SHOULD treat as the coding (RFC 9110 §8.4.1.1,
§8.4.1.3). -/
def Coding.aliases : Coding → List Name
  | .gzip => [ascii "x-gzip"]
  | .compress => [ascii "x-compress"]
  | _ => []

/-- Whether the coding needs an out-of-band compression dictionary (RFC 9842). -/
def Coding.needsDictionary : Coding → Bool
  | .dcb | .dcz => true
  | _ => false

/-- The layers a registered name lives in: the content coding registry (RFC 9110
§16.6.1) and/or the transfer coding registry (RFC 9112 §7.3). -/
structure Layer where
  content : Bool
  transfer : Bool
  deriving DecidableEq, Repr

/-- What this library provides for a coding. -/
inductive Status where
  /-- A decoder is defined here and its round trip and container laws are proved. -/
  | proved
  /-- A decoder is defined here but only checked on known-answer vectors. -/
  | checked
  /-- A strict subset of the format is decoded (the rest is rejected), checked on
  vectors; the full format is planned. -/
  | partialSubset
  /-- Modelled as an abstract parameter (`Externals`); implemented by another track. -/
  | abstract
  /-- Not implemented; a formalization plan exists (docs/projects/content-coding.md). -/
  | planned
  /-- Deprecated by its registrant; not planned. -/
  | deprecated
  /-- A reserved name with a special role, not a data transformation to implement. -/
  | reserved
  deriving DecidableEq, Repr

/-- A row of the registry. `coding` is `none` for transfer-only names. -/
structure Entry where
  name : Name
  coding : Option Coding
  aliases : List Name
  layer : Layer
  reference : String
  status : Status
  deriving Repr

/-- The registry, one row per registered name (aliases are listed on their
coding's row). The transfer-coding rows `chunked` and `trailers` are recorded so
that the boundary is explicit: they are not content codings. -/
def registry : List Entry :=
  [ ⟨ascii "aes128gcm", some .aes128gcm, [], ⟨true, false⟩, "RFC 8188", .abstract⟩,
    ⟨ascii "br", some .br, [], ⟨true, false⟩, "RFC 7932", .planned⟩,
    ⟨ascii "compress", some .compress, [ascii "x-compress"], ⟨true, true⟩,
      "RFC 9110 §8.4.1.1; RFC 9112 §7.2", .planned⟩,
    ⟨ascii "dcb", some .dcb, [], ⟨true, false⟩, "RFC 9842 §4", .planned⟩,
    ⟨ascii "dcz", some .dcz, [], ⟨true, false⟩, "RFC 9842 §5", .planned⟩,
    ⟨ascii "deflate", some .deflate, [], ⟨true, true⟩,
      "RFC 9110 §8.4.1.2 (zlib, RFC 1950, around RFC 1951); RFC 9112 §7.2", .proved⟩,
    ⟨ascii "exi", some .exi, [], ⟨true, false⟩, "W3C EXI 1.0", .planned⟩,
    ⟨ascii "gzip", some .gzip, [ascii "x-gzip"], ⟨true, true⟩,
      "RFC 9110 §8.4.1.3 (RFC 1952 file); RFC 9112 §7.2", .proved⟩,
    ⟨ascii "identity", some .identity, [], ⟨true, false⟩, "RFC 9110 §12.5.3 (reserved)",
      .reserved⟩,
    ⟨ascii "pack200-gzip", some .pack200gzip, [], ⟨true, false⟩, "JSR 200 (removed, JEP 367)",
      .deprecated⟩,
    ⟨ascii "zstd", some .zstd, [], ⟨true, false⟩, "RFC 8878 §7.2; RFC 9659", .partialSubset⟩,
    ⟨ascii "chunked", none, [], ⟨false, true⟩, "RFC 9112 §7.1", .reserved⟩,
    ⟨ascii "trailers", none, [], ⟨false, true⟩, "RFC 9112 §7.3 (reserved)", .reserved⟩ ]

/-- Names that are transfer codings only (RFC 9112 §7): never content codings. -/
def transferOnlyNames : List Name := [ascii "chunked", ascii "trailers"]

/-- Whether an entry answers to a (lowercased) name, by its name or an alias. -/
def Entry.answers (e : Entry) (n : Name) : Bool := e.name == n || e.aliases.contains n

/-- The registry row of a name, case-insensitively. -/
def lookup (n : Name) : Option Entry := registry.find? (fun e => e.answers (lower n))

/-- The **content coding** a name denotes, case-insensitively and through
aliases; `none` for unregistered names and transfer-only names. -/
def ofName? (n : Name) : Option Coding := (lookup n).bind Entry.coding

/-- The status of a coding, from its registry row. -/
def Coding.status (c : Coding) : Status :=
  match registry.find? (fun e => e.coding == some c) with
  | some e => e.status
  | none => .planned

/-! ## Decoders of the codings -/

/-- A whole-buffer transformation: decoding a representation's coded form. -/
abbrev Whole := List UInt8 → Option (List UInt8)

/-- Decoder parameters fixed outside a coding's own format. `aes128gcm`
(RFC 8188) needs a key and a record size from the crypto track; it is modelled as
an abstract decoder, `none` when no such implementation is linked. `zstdWindowMax`
is the largest zstd `Window_Size` accepted (RFC 9659 §3: 8 MiB for HTTP). -/
structure Externals where
  aes128gcm : Option Whole := none
  zstdWindowMax : Nat := 8 * 1048576

/-- The whole-buffer decoder of a coding, when one is defined. -/
def Coding.decoder? (ext : Externals) : Coding → Option Whole
  | .identity => some some
  | .gzip => some Gzip.decoder.members
  | .deflate => some Zlib.decoder.whole
  | .zstd => some (Zstd.decode ext.zstdWindowMax)
  | .aes128gcm => ext.aes128gcm
  | _ => none

/-- The encoder of a coding, when one is defined: `identity`, and the stored-block
encoders of gzip (one member) and zlib. Encoders are optional; the decoder is the
specification. -/
def Coding.encoder? : Coding → Option Encoder
  | .identity => some id
  | .gzip => some Gzip.encoder
  | .deflate => some Zlib.encoder
  | _ => none

/-! ## Decoding steps and errors -/

/-- Why decoding a coded representation failed. -/
inductive DecodeError (α : Type) where
  /-- No decoder for this coding (planned, abstract and not linked, unregistered,
  or not allowed by the profile). -/
  | unsupported (c : α)
  /-- The input is not a valid encoding. -/
  | malformed (c : α)
  /-- The decoded output exceeds the profile's limit. -/
  | tooLarge (c : α)
  deriving DecidableEq, Repr

/-- One unbounded decoding step of a registry coding. -/
def stage (ext : Externals) (c : Coding) (bytes : List UInt8) :
    Except (DecodeError Coding) (List UInt8) :=
  match c.decoder? ext with
  | none => .error (.unsupported c)
  | some dec =>
    match dec bytes with
    | none => .error (.malformed c)
    | some out => .ok out

/-- A decoding step whose successful outputs must satisfy `within input output`;
otherwise it reports `tooLarge`. -/
def guarded {α : Type} (within : List UInt8 → List UInt8 → Bool)
    (dec : α → List UInt8 → Except (DecodeError α) (List UInt8)) (c : α) (bytes : List UInt8) :
    Except (DecodeError α) (List UInt8) :=
  match dec c bytes with
  | .error e => .error e
  | .ok out => if within bytes out then .ok out else .error (.tooLarge c)

/-! ## Chains of codings (RFC 9110 §8.4) -/

/-- Decode a Content-Encoding list. The list is in the order the codings were
applied, so the **last** coding is decoded first. -/
def decodeChain {α ε : Type} (dec : α → List UInt8 → Except ε (List UInt8)) :
    List α → List UInt8 → Except ε (List UInt8)
  | [], bytes => .ok bytes
  | c :: cs, bytes =>
    match decodeChain dec cs bytes with
    | .error e => .error e
    | .ok mid => dec c mid

/-- Apply codings in list order (the first is applied first). -/
def encodeChain {α : Type} (enc : α → List UInt8 → Option (List UInt8)) :
    List α → List UInt8 → Option (List UInt8)
  | [], data => some data
  | c :: cs, data =>
    match enc c data with
    | none => none
    | some coded => encodeChain enc cs coded

/-- The chain with every stage guarded by `within`. -/
def guardedChain {α : Type} (within : List UInt8 → List UInt8 → Bool)
    (dec : α → List UInt8 → Except (DecodeError α) (List UInt8)) :
    List α → List UInt8 → Except (DecodeError α) (List UInt8) :=
  decodeChain (guarded within dec)

/-- Every stage of a decoding run of `cs` on `bytes` satisfies `within`. -/
def StagesWithin {α ε : Type} (within : List UInt8 → List UInt8 → Bool)
    (dec : α → List UInt8 → Except ε (List UInt8)) : List α → List UInt8 → Prop
  | [], _ => True
  | c :: cs, bytes =>
    StagesWithin within dec cs bytes ∧
      ∀ mid out, decodeChain dec cs bytes = .ok mid → dec c mid = .ok out → within mid out = true

/-- Decode a registry chain without bounds. -/
def decodeAll (ext : Externals) : List Coding → List UInt8 →
    Except (DecodeError Coding) (List UInt8) :=
  decodeChain (stage ext)

/-- Encode with a registry chain (fails on a coding without an encoder). -/
def encodeAll : List Coding → List UInt8 → Option (List UInt8) :=
  encodeChain (fun c data => c.encoder?.map (· data))

/-! ## Profiles -/

/-- `2^20`. -/
def mebibyte : Nat := 1048576

/-- RFC 9659 §3: HTTP zstd decoders MUST support a `Window_Size` up to and
including 8 MB (`8 * 2^20` bytes), and encoders MUST NOT exceed it. -/
def zstdHttpWindowMax : Nat := 8 * mebibyte

/-- RFC 9842 §4: `dcb` clients MUST handle a 16 MB window. -/
def dcbWindow : Nat := 16 * mebibyte

/-- RFC 9842 §5: the `dcz` window a client MUST support: 8 MB or 1.25 times the
dictionary size, whichever is greater, at most 128 MB. -/
def dczWindow (dictionarySize : Nat) : Nat :=
  min (128 * mebibyte) (max (8 * mebibyte) (dictionarySize * 5 / 4))

/-- The resource and feature settings of a deployment. -/
structure Profile where
  /-- The codings the deployment enables. -/
  allowed : List Coding
  /-- The maximum size of any decoded stage, in bytes. -/
  maxDecoded : Nat
  /-- The maximum expansion ratio `output ≤ ratio * input` of a stage, if any. -/
  maxRatio : Option Nat := none
  /-- Whether a negotiated compression dictionary is available (RFC 9842). -/
  dictionaryAvailable : Bool := false
  /-- The maximum number of codings in a Content-Encoding chain. -/
  maxChain : Nat := 4

/-- The coding is allowed, has a decoder, and has its dictionary if it needs one. -/
def Profile.supports (p : Profile) (ext : Externals) (c : Coding) : Bool :=
  p.allowed.contains c && (c.decoder? ext).isSome &&
    (!c.needsDictionary || p.dictionaryAvailable)

/-- The output limit of a stage with `inputLength` input bytes. -/
def Profile.limit (p : Profile) (inputLength : Nat) : Nat :=
  match p.maxRatio with
  | none => p.maxDecoded
  | some r => min p.maxDecoded (r * inputLength)

/-- The stage bound of a profile. -/
def Profile.within (p : Profile) (input output : List UInt8) : Bool :=
  decide (output.length ≤ p.limit input.length)

/-- One decoding step under a profile: unsupported codings are refused, and
outputs beyond the limit are `tooLarge`. -/
def Profile.stage (p : Profile) (ext : Externals) (c : Coding) (bytes : List UInt8) :
    Except (DecodeError Coding) (List UInt8) :=
  if p.supports ext c then guarded p.within (Registry.stage ext) c bytes
  else .error (.unsupported c)

/-- Decode a Content-Encoding chain under a profile. -/
def Profile.decode (p : Profile) (ext : Externals) (cs : List Coding) (bytes : List UInt8) :
    Except (DecodeError Coding) (List UInt8) :=
  decodeChain (p.stage ext) cs bytes

/-- A conservative HTTP client profile: identity, gzip and deflate, at most
`maxDecoded` decoded bytes per stage. -/
def httpProfile (maxDecoded : Nat) : Profile where
  allowed := [.identity, .gzip, .deflate]
  maxDecoded := maxDecoded

/-! ## Bounded member decoding -/

/-- Why a bounded member decode failed. -/
inductive BoundError where
  | malformed
  | tooLarge
  deriving DecidableEq, Repr

/-- A member decoder that reports `tooLarge` when the member's output is longer
than `limit` (a semantic bound; see the module docstring). -/
def _root_.Silmaril.Formats.Compression.Decoder.bounded (d : Decoder) (limit : Nat)
    (bytes : List UInt8) : Except BoundError (List UInt8 × List UInt8) :=
  match d bytes with
  | none => .error .malformed
  | some (out, rest) => if out.length ≤ limit then .ok (out, rest) else .error .tooLarge

end Silmaril.Formats.Compression.Registry

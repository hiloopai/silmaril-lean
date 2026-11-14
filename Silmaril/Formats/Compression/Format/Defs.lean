module

public import Silmaril.Formats.Compression.Defs

/-!
# Compressed formats, and what is claimed about each

The framework of `Compression.Defs` fixes what a member decoder is and which laws
one may state. This module adds the layer formats are catalogued at:

* `Format`: an algorithm or container, given by its **decode-side parameters**
  `Params` (a preset dictionary or history, a window limit, a dictionary table)
  and a member decoder `decodeE p` that reports format-specific `Error`s.
  `Format.decode p` is the framework `Decoder` it denotes. A format is defined
  by its decoder; nothing about it is assumed.
* `Encoding F`: an optional encoder family. `EParams` are the encoder's own
  choices (a header to write, a level), `params` the decode parameters its
  output is meant for. Encodings are only claimed to round-trip, never assumed.
* `Capability F`: one **separately proved** claim about `F`, with `Holds`
  saying what it means. Capabilities name the parameters they cover (`Scope`),
  because laws rarely hold uniformly: the DEFLATE decoder meets RFC 1951's
  relational semantics with an empty history, the zlib member machine is
  complete for the dictionary-free decoder only, and so on.
* `Certified F`: the list of capabilities proved for `F`, with their proofs, and
  its `Security` notes. A format lists exactly what is proved: there is no
  default, and a missing claim is a statement that nothing is claimed.
* `Security`: the assumptions a *keyed* transform rests on, and the hazards of
  using a format in a protocol. These are **data**: names, never Lean axioms and
  never theorems, mirroring the crypto track's catalogue (`Crypto.Catalog`,
  `Evidence` kept separate from `Assumption`).

## Capability kinds

| Kind | Capabilities | What is proved |
| --- | --- | --- |
| `boundary` | `consumes`, `local` | member boundary laws (`Decoder.Consumes`, `Decoder.Local`) |
| `functional` | `spec`, `deterministic` | the decoder is exactly an independent relational spec; that spec is a function |
| `vectors` | `vector` | a known answer, kernel-checked |
| `roundTrip` | `roundTrip` | an encoding round-trips (`RoundTrip`) for every encoder parameter |
| `integrity` | `trailer`, `checksumSpec` | every member ends with the trailer of its output; the checksum meets its independent definition |
| `resource` | `outputLinear`, `callCapacity` | intrinsic output bound per consumed byte; one streaming call emits at most its capacity |
| `streaming` | `streamSound`, `streamRejectSound`, `streamComplete` | an `Incremental` machine is sound / rejection-sound / complete for the decoder |

There is deliberately no `refinement` kind: no compression decoder here is
proved to be computed by machine code. Integrity claims are about accidental
corruption: CRC-32 and Adler-32 are not MACs (`Hazard.checksumNotMac`).

## Where future formats fit

* **zstd** (RFC 8878): a `Format` whose `Params` are the dictionaries available
  by ID and a window limit (RFC 9659's 8 MiB for HTTP is such a parameter, not a
  different format). A frame is `Framing.wrapDep` around the block decoder: the
  frame header yields the window size, dictionary ID and checksum flag, so the
  body decoder depends on it. The XXH64 content checksum is a `Checksum` with a
  `checksumSpec` claim; skippable frames and frame concatenation are
  `Decoder.members` with a member decoder that also accepts skippable frames.
* **brotli** (RFC 7932): a raw self-delimiting `Format` with no container,
  `Params` the window bits limit (and, for shared-dictionary brotli, the
  dictionary). The built-in static dictionary is part of the algorithm, not a
  parameter.
* **LZ4 frame**: `Framing.wrapDep` (the frame descriptor fixes block size,
  block independence and checksum flags) around LZ4 block decoding; `Params`
  hold an optional dictionary. Content and block checksums are xxHash-32.
* **xz**: `Framing` (stream header/footer, block headers, index) around LZMA2,
  whose filter chain and dictionary size come from the block header: `wrapDep`.
  CRC-32, CRC-64 and SHA-256 checks are `Checksum`s or keyed digests.
* **bzip2**: stream header (block size), per-block and combined CRC-32 around
  the BWT, MTF/RLE and Huffman stages; concatenated streams are `members`.
* **Keyed transforms** (the `aes128gcm` content coding of RFC 8188, decrypting
  with a key): not formats but whole-message `Transform`s whose `Params` hold
  key material, with `Security.assumptions` naming the AEAD assumption. Their
  definitions and proofs belong to the crypto track; only the shape is here.
* **HTTP content codings** (registry names, profiles with output limits,
  `Accept-Encoding` negotiation): an adapter on top, mapping coding names to
  `Certified` formats and chaining them with `Transform.andThen`. Nothing here
  depends on HTTP.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

/-- A compressed format: decode-side parameters, a format-specific error type,
and the decoder of one self-delimiting member (output, unread rest). -/
structure Format where
  /-- Decode-side parameters and context (dictionary, history, window limit). -/
  Params : Type
  /-- Why a member is rejected. -/
  Error : Type
  /-- Decode one member at the front of the input. -/
  decodeE : Params → List UInt8 → Except Error (List UInt8 × List UInt8)

namespace Format

/-- The member decoder of `F` at parameters `p`, forgetting the error. -/
def decode (F : Format) (p : F.Params) : Decoder := Decoder.ofExcept (F.decodeE p)

/-- A format given by an `Option`-valued decoder, with no error taxonomy. -/
def ofDecoder (Params : Type) (d : Params → Decoder) : Format where
  Params := Params
  Error := Unit
  decodeE p bytes :=
    match d p bytes with
    | some r => .ok r
    | none => .error ()

end Format

/-- An optional encoder family for `F`: `encode e` is meant to be read back by
`F.decode (params e)`. Nothing is assumed; `Capability.roundTrip` claims it. -/
structure Encoding (F : Format) where
  /-- The encoder's own choices: a header to write, a level, a dictionary. -/
  EParams : Type
  /-- The decode parameters the output is meant for. -/
  params : EParams → F.Params
  encode : EParams → Encoder

/-- Which decode parameters a claim covers. -/
abbrev Scope (F : Format) := F.Params → Prop

/-- Every parameter. -/
def Scope.all {F : Format} : Scope F := fun _ => True

/-- Exactly one parameter. -/
def Scope.only {F : Format} (p : F.Params) : Scope F := (· = p)

/-- A relational specification of a member decoder: `R p input out rest`. -/
abbrev Rel (F : Format) := F.Params → List UInt8 → List UInt8 → List UInt8 → Prop

/-- The kinds of evidence. They are not a ladder, and none of them is security. -/
inductive Kind where
  | boundary | functional | vectors | roundTrip | integrity | resource | streaming
  deriving DecidableEq, Repr

/-- One claim about a format. `Holds` says what it means. -/
inductive Capability (F : Format) : Type 1 where
  /-- Members consume a prefix of their input. -/
  | consumes (s : Scope F)
  /-- Bytes after a member never change how it decodes. -/
  | «local» (s : Scope F)
  /-- The decoder returns `(out, rest)` exactly when `R p input out rest`. -/
  | spec (s : Scope F) (R : Rel F)
  /-- The relational spec `R` gives at most one meaning and one rest. -/
  | deterministic (s : Scope F) (R : Rel F)
  /-- A known answer: `input` decodes to `out`, leaving `rest`. -/
  | vector (p : F.Params) (input out rest : List UInt8)
  /-- The encoding round-trips for every encoder parameter. -/
  | roundTrip (E : Encoding F)
  /-- Every member ends with `trl out`, followed by the rest. -/
  | trailer (s : Scope F) (trl : List UInt8 → List UInt8)
  /-- The incremental checksum `c` computes the independently defined `ref`. -/
  | checksumSpec (c : Checksum) (ref : List UInt8 → UInt32)
  /-- At most `k` output bytes per consumed input byte. -/
  | outputLinear (s : Scope F) (k : Nat)
  /-- One call of the streaming machine `i` appends at most `capacity call` to
  its observed `output`. -/
  | callCapacity (i : Incremental) (output : i.Machine → List UInt8) (capacity : i.Call → Nat)
  /-- The streaming machine `i` is sound for `F.decode p`. -/
  | streamSound (p : F.Params) (i : Incremental)
  /-- Failures of `i` are rejections by `F.decode p`. -/
  | streamRejectSound (p : F.Params) (i : Incremental)
  /-- `i` finishes every member `F.decode p` accepts. -/
  | streamComplete (p : F.Params) (i : Incremental)

namespace Capability

variable {F : Format}

/-- What a capability claims. -/
def Holds : Capability F → Prop
  | .consumes s => ∀ p, s p → (F.decode p).Consumes
  | .local s => ∀ p, s p → (F.decode p).Local
  | .spec s R => ∀ p, s p → ∀ input out rest,
      F.decode p input = some (out, rest) ↔ R p input out rest
  | .deterministic s R => ∀ p, s p → ∀ input out rest out' rest',
      R p input out rest → R p input out' rest' → out = out' ∧ rest = rest'
  | .vector p input out rest => F.decode p input = some (out, rest)
  | .roundTrip E => ∀ e, RoundTrip (F.decode (E.params e)) (E.encode e)
  | .trailer s trl => ∀ p, s p → ∀ ⦃bytes out rest⦄,
      F.decode p bytes = some (out, rest) → ∃ pre, bytes = pre ++ (trl out ++ rest)
  | .checksumSpec c ref => ∀ bytes, c.digest bytes = ref bytes
  | .outputLinear s k => ∀ p, s p → (F.decode p).OutputLinear k
  | .callCapacity i output capacity => ∀ m call,
      ∃ emitted, output (i.step m call) = output m ++ emitted ∧ emitted.length ≤ capacity call
  | .streamSound p i => i.Sound (F.decode p)
  | .streamRejectSound p i => i.RejectSound (F.decode p)
  | .streamComplete p i => i.Complete (F.decode p)

/-- The kind of evidence a capability is. -/
def kind : Capability F → Kind
  | .consumes _ | .local _ => .boundary
  | .spec _ _ | .deterministic _ _ => .functional
  | .vector .. => .vectors
  | .roundTrip _ => .roundTrip
  | .trailer _ _ | .checksumSpec _ _ => .integrity
  | .outputLinear _ _ | .callCapacity .. => .resource
  | .streamSound _ _ | .streamRejectSound _ _ | .streamComplete _ _ => .streaming

/-- Every capability in a list holds. -/
def All : List (Capability F) → Prop
  | [] => True
  | c :: cs => c.Holds ∧ All cs

end Capability

/-! ## Security: data only -/

/-- Assumptions a keyed transform's security rests on, as names. They are data:
not Lean axioms, and nothing here derives a security statement from them. The
algorithm names are those of the crypto track's catalogue. -/
inductive Assumption where
  /-- The AEAD (for instance `AEAD_AES_128_GCM`) is IND-CPA and INT-CTXT secure. -/
  | aeadSecure (algorithm : String)
  /-- The key derivation (for instance HKDF-SHA-256) is a PRF on its inputs. -/
  | kdfSecure (algorithm : String)
  /-- Keying material is secret and never reused across contexts. -/
  | keySecret
  /-- Salts or nonces come from a secure random source. -/
  | goodRandomness
  deriving DecidableEq, Repr

/-- Known hazards of using a format in a protocol, as names. -/
inductive Hazard where
  /-- The named checksum detects accidental corruption only; it is not a MAC. -/
  | checksumNotMac (checksum : String)
  /-- Compressing secrets together with attacker-chosen data leaks through the
  compressed length (CRIME, BREACH). -/
  | compressionLengthOracle
  /-- No integrity check at all: corruption may decode to other data. -/
  | noIntegrity
  deriving DecidableEq, Repr

/-- The security notes of a format or transform. -/
structure Security where
  assumptions : List Assumption := []
  hazards : List Hazard := []
  deriving Repr

/-! ## Certified formats -/

/-- A format with the capabilities proved for it, and its security notes. -/
structure Certified (F : Format) where
  claims : List (Capability F)
  proofs : ∀ c ∈ claims, c.Holds
  security : Security := {}

end Silmaril.Formats.Compression

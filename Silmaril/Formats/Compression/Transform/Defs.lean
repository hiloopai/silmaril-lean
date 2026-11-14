module

public import Silmaril.Formats.Compression.Format.Defs

/-!
# Whole-message transforms and their composition

A `Transform` decodes a whole message under parameters, or rejects it. It is the
unit an HTTP content-coding chain (`Content-Encoding: gzip, br`) or a keyed
transform (decrypt, then decompress) is assembled from:

* `Transform.whole F`, `Transform.members F`: a `Format` read as a whole buffer
  holding exactly one member, or as one or more concatenated members;
* `Transform.id`: the identity (the `identity` content coding);
* `Transform.andThen t u`: run `t`, then `u` on its output, with the pair of
  their parameters (`comp u t` is the same in the order of function
  composition);
* `Transform.Inverts t p enc`: the encoder `enc` is read back by `t` at `p`;
  `Transform.LinearAt t p k`: output at most `k` bytes per input byte.

The laws (`Transform.Thms`) say that round trips compose, linear bounds
multiply, `id` is neutral and `andThen` is associative.

Keyed transforms (the `aes128gcm` coding of RFC 8188, with key material as
`Params` and its AEAD assumption as `Security` data) belong to the crypto
track; only the shape is fixed here.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

/-- A whole-message transform: decode a message under parameters, or reject it. -/
structure Transform where
  Params : Type
  run : Params → List UInt8 → Option (List UInt8)

namespace Transform

/-- The identity transform. -/
def id : Transform where
  Params := Unit
  run _ bytes := some bytes

/-- Run `t`, then `u` on its output. -/
def andThen (t u : Transform) : Transform where
  Params := t.Params × u.Params
  run p bytes := (t.run p.1 bytes).bind (u.run p.2)

/-- `u ∘ t`: run `t`, then `u`. -/
abbrev comp (u t : Transform) : Transform := t.andThen u

/-- A format on a whole buffer holding exactly one member. -/
def whole (F : Format) : Transform where
  Params := F.Params
  run p := (F.decode p).whole

/-- A format on a file of one or more concatenated members. -/
def members (F : Format) : Transform where
  Params := F.Params
  run p := (F.decode p).members

/-- The encoder `enc` is read back by `t` at `p`. -/
def Inverts (t : Transform) (p : t.Params) (enc : Encoder) : Prop :=
  ∀ data, t.run p (enc data) = some data

/-- At parameters `p`, `t` outputs at most `k` bytes per input byte. -/
def LinearAt (t : Transform) (p : t.Params) (k : Nat) : Prop :=
  ∀ ⦃bytes out⦄, t.run p bytes = some out → out.length ≤ k * bytes.length

end Transform

end Silmaril.Formats.Compression

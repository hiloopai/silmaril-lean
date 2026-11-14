module

public import Silmaril.Formats.Compression.DeflateSpec.Defs
public import Silmaril.Formats.Compression.Deflate.Defs
import Silmaril.Proofs.Formats.Compression.DeflateSpec.Policy
import Silmaril.Proofs.Formats.Compression.DeflateSpec.Vectors
import Silmaril.Proofs.Formats.Compression.DeflateSpec.History
import Silmaril.Proofs.Formats.Compression.DeflateSpec.Witness
public import Silmaril.Formats.Compression.Deflate.WithHistory

/-!
# DEFLATE (RFC 1951): the decoder against the declarative semantics

Proved (standard axioms):

* `deflateTake_sound`, `deflateTake_complete`, `deflateTake_iff`: the decoder
  `Deflate.deflateTake` returns `(out, rest)` exactly when `input` begins with a
  `Stream .strict` decoding to `out` and followed by `rest`;
* `Stream.functional`: a stream prefix has at most one meaning and one length;
* `Stream.mono`, `Stream.strict_rfc`, `deflateTake_sound_rfc`: relaxing the
  policy keeps every stream and its meaning, so every stream the decoder accepts
  is also valid under the letter of the RFC (`Policy.rfc`);
* `deflateTakeWithHistory_iff`: the same for a stream decoded after a preset
  history (`StreamWithHistory`, used by zlib's `FDICT`), and
  `StreamWithHistory.window`: only the last 32 KiB of a history matter, as
  distances are at most 32768 (§3.2.5);
* `kat_stored`, `kat_fixed`, `kat_dynamic`: the zlib vectors of `Deflate.Thms`
  (one per block type) are `Stream .strict` derivations, so the relation is not
  vacuous;
* `fixedLitLenCode_table`, `ofLengths_example`, `copyMatch_example`: the spec
  reproduces the code table of §3.2.6, the worked example of §3.2.2
  (`ABCDEFGH` with lengths `(3, 3, 3, 3, 3, 2, 4, 4)`) and the overlapping copy
  of §3.2.3.

## Where the decoder is stricter than the letter of RFC 1951

`deflateTake` accepts exactly `Policy.strict` streams, which is zlib's policy.
Streams valid under `Policy.rfc` that it rejects:

* dynamic blocks with `HDIST = 30` or `31` (31 or 32 distance codes), which the
  RFC's header description "(1 - 32)" allows (zlib: "too many length or distance
  symbols");
* incomplete code length codes, and incomplete literal/length or distance codes
  with more than one used symbol (zlib: "incomplete … tree"); the RFC only
  requires a prefix code, and mentions the incomplete one-code distance case.

These differences are exact: `stream_strict_iff` (an RFC stream is strict iff
`deflateTake` accepts its input), and `rfcOnly_hdist`, `rfcOnly_clCode`,
`rfcOnly_litCode`, `rfcOnly_distCode` exhibit one RFC stream per difference that
`deflateTake` rejects. The RFC-permissive decoder `Deflate.deflateTakeRfc`
accepts exactly `Policy.rfc` streams (`deflateTakeRfc_iff`,
`deflateTakeWithHistoryRfc_iff`); `Deflate.deflateTakeProfile .strict` is
`deflateTake` (`deflateTakeProfile_strict`). With a window,
`DecodeProfile.windowed w` accepts exactly `StreamWithin .strict (some w)`
(`deflateTakeWindowed_iff`, with history `deflateTakeWithHistoryWindowed_iff`;
`windowOnly` is a stream it rejects).

Both policies, like zlib and the decoder, reject literal/length symbols 286 and
287, distance symbols 30 and 31, `BTYPE = 11`, back-references before the start
of the output, and `NLEN` other than the one's complement of `LEN`; and both
accept code 284 with extra bits `11111` as length 258 (the §3.2.5 table lists
227–257 for it). See the docstring of `DeflateSpec.Defs`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.DeflateSpec

/-- **Soundness**: whatever the decoder returns is the meaning of an RFC 1951
stream (under zlib's acceptance policy) at the front of the input. -/
theorem deflateTake_sound {input out rest : List UInt8}
    (h : Deflate.deflateTake input = .ok (out, rest)) : Stream .strict input out rest :=
  Proofs.Formats.Compression.DeflateSpec.deflateTake_sound h

/-- **Completeness**: the decoder decodes every stream that `Policy.strict`
accepts, to its meaning. -/
theorem deflateTake_complete {input out rest : List UInt8}
    (h : Stream .strict input out rest) : Deflate.deflateTake input = .ok (out, rest) :=
  Proofs.Formats.Compression.DeflateSpec.deflateTake_complete h

theorem deflateTake_iff {input out rest : List UInt8} :
    Deflate.deflateTake input = .ok (out, rest) ↔ Stream .strict input out rest :=
  ⟨deflateTake_sound, deflateTake_complete⟩

theorem Stream.functional {input out out' rest rest' : List UInt8}
    (h : Stream .strict input out rest) (h' : Stream .strict input out' rest') :
    out = out' ∧ rest = rest' := by
  have := (deflateTake_complete h).symm.trans (deflateTake_complete h'); simp_all

theorem Stream.mono {p q : Policy} (hd : p.maxDistCodes ≤ q.maxDistCodes)
    (hcl : ∀ L, p.clCodeOK L → q.clCodeOK L) (hc : ∀ L, p.codeOK L → q.codeOK L)
    {input out rest : List UInt8} (h : Stream p input out rest) : Stream q input out rest :=
  Proofs.Formats.Compression.DeflateSpec.stream_mono hd hcl hc h

theorem Stream.strict_rfc {input out rest : List UInt8} (h : Stream .strict input out rest) :
    Stream .rfc input out rest :=
  Proofs.Formats.Compression.DeflateSpec.stream_strict_rfc h

theorem deflateTake_sound_rfc {input out rest : List UInt8}
    (h : Deflate.deflateTake input = .ok (out, rest)) : Stream .rfc input out rest :=
  (deflateTake_sound h).strict_rfc

/-! ### Preset history -/

/-- The decoder with an installed history decodes exactly the streams of
`StreamWithHistory .strict`: back-references may reach into the history, which
is not returned. -/
theorem deflateTakeWithHistory_iff {history input out rest : List UInt8} :
    Deflate.deflateTakeWithHistory history input = .ok (out, rest) ↔
      StreamWithHistory .strict history input out rest :=
  ⟨Proofs.Formats.Compression.DeflateSpec.deflateTakeWithHistory_sound,
   Proofs.Formats.Compression.DeflateSpec.deflateTakeWithHistory_complete⟩

theorem stream_iff_withHistory_nil {p : Policy} {input out rest : List UInt8} :
    Stream p input out rest ↔ StreamWithHistory p [] input out rest := Iff.rfl

/-- Only the last 32 KiB of a history can be referenced (RFC 1951 §3.2.5: distances
are at most 32768). -/
theorem StreamWithHistory.window {p : Policy} {history input out rest : List UInt8} :
    StreamWithHistory p (history.drop (history.length - 32768)) input out rest ↔
      StreamWithHistory p history input out rest :=
  Proofs.Formats.Compression.DeflateSpec.streamWithHistory_window

/-! ### Known answers -/

/-- zlib level 0, `"abc"`: one stored block. -/
theorem kat_stored :
    Stream .strict [0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63] [0x61, 0x62, 0x63] [] :=
  deflateTake_sound Proofs.Formats.Compression.DeflateSpec.deflateTake_stored_vector

/-- zlib, `"abc"`: one fixed-Huffman block. -/
theorem kat_fixed : Stream .strict [0x4b, 0x4c, 0x4a, 0x06, 0x00] [0x61, 0x62, 0x63] [] :=
  deflateTake_sound Proofs.Formats.Compression.DeflateSpec.deflateTake_fixed_vector

/-- zlib level 9, a 40-byte string over `a b c d`: one dynamic-Huffman block. -/
theorem kat_dynamic :
    Stream .strict [0x25, 0x88, 0xb1, 0x09, 0x00, 0x00, 0x0c, 0x83, 0x6e, 0x35, 0xe6, 0xff,
      0x1b, 0x1a, 0xa8, 0x83, 0x88, 0xd8, 0x02, 0xd5, 0xe0, 0x82, 0x7c, 0x4e, 0x1d, 0xd8,
      0xb8, 0xe3, 0x01]
      [0x61, 0x63, 0x64, 0x64, 0x61, 0x61, 0x61, 0x64, 0x63, 0x63, 0x62, 0x61,
        0x63, 0x61, 0x61, 0x61, 0x61, 0x62, 0x64, 0x63, 0x63, 0x62, 0x61, 0x63, 0x63,
        0x63, 0x62, 0x64, 0x64, 0x64, 0x64, 0x61, 0x63, 0x64, 0x62, 0x63, 0x64, 0x63,
        0x63, 0x63] [] :=
  deflateTake_sound Proofs.Formats.Compression.DeflateSpec.deflateTake_dynamic_vector

/-- The fixed literal/length codes listed in §3.2.6 (first and last of each range). -/
theorem fixedLitLenCode_table :
    fixedLitLenCode 0 = some (codeBits 0b00110000 8) ∧
    fixedLitLenCode 143 = some (codeBits 0b10111111 8) ∧
    fixedLitLenCode 144 = some (codeBits 0b110010000 9) ∧
    fixedLitLenCode 255 = some (codeBits 0b111111111 9) ∧
    fixedLitLenCode 256 = some (codeBits 0b0000000 7) ∧
    fixedLitLenCode 279 = some (codeBits 0b0010111 7) ∧
    fixedLitLenCode 280 = some (codeBits 0b11000000 8) ∧
    fixedLitLenCode 287 = some (codeBits 0b11000111 8) ∧
    fixedLitLenCode 288 = none :=
  Proofs.Formats.Compression.DeflateSpec.fixedLitLenCode_table

/-- §3.2.2: lengths `(3, 3, 3, 3, 3, 2, 4, 4)` give the codes `010, 011, 100, 101,
110, 00, 1110, 1111`. -/
theorem ofLengths_example :
    (List.range 8).map (Code.ofLengths [3, 3, 3, 3, 3, 2, 4, 4]) =
      [some [false, true, false], some [false, true, true], some [true, false, false],
       some [true, false, true], some [true, true, false], some [false, false],
       some [true, true, true, false], some [true, true, true, true]] :=
  Proofs.Formats.Compression.DeflateSpec.ofLengths_example

/-- §3.2.3: after `X, Y`, the reference `<length = 5, distance = 2>` adds
`X, Y, X, Y, X`. -/
theorem copyMatch_example (x y : UInt8) : copyMatch [x, y] 2 5 = [x, y, x, y, x, y, x] :=
  Proofs.Formats.Compression.DeflateSpec.copyMatch_example x y

/-! ### Strict against RFC-permissive: the exact difference

`Policy.strict` and `Policy.rfc` differ only in the conditions on dynamic block
headers (`HDIST`, completeness of the three codes). Every strict stream is an
RFC stream with the same meaning (`Stream.strict_rfc`); conversely an RFC stream
is strict exactly when `deflateTake` accepts its input (`stream_strict_iff`, a
decidable condition). Each of the four header conditions makes a difference:
`rfcOnly_hdist`, `rfcOnly_clCode`, `rfcOnly_litCode`, `rfcOnly_distCode` are
RFC streams that `deflateTake` (and zlib 1.3.1) reject. -/

/-- The RFC-permissive decoder `Deflate.deflateTakeRfc` decodes exactly the
`Policy.rfc` streams. Incomplete codes are decoded by their canonical code;
decoding fails only when an unassigned code word is read (`rfc_unassigned`). -/
theorem deflateTakeRfc_iff {input out rest : List UInt8} :
    Deflate.deflateTakeRfc input = .ok (out, rest) ↔ Stream .rfc input out rest :=
  Proofs.Formats.Compression.DeflateSpec.deflateTakeRfc_iff

theorem deflateTakeWithHistoryRfc_iff {history input out rest : List UInt8} :
    Deflate.deflateTakeWithHistoryRfc history input = .ok (out, rest) ↔
      StreamWithHistory .rfc history input out rest :=
  Proofs.Formats.Compression.DeflateSpec.deflateTakeWithHistoryRfc_iff

/-- The generalised decoder at the strict profile is `deflateTake`. -/
theorem deflateTakeProfile_strict (input : List UInt8) :
    Deflate.deflateTakeProfile .strict input = Deflate.deflateTake input :=
  Proofs.Formats.Compression.DeflateSpec.deflateTakeProfile_strict input

theorem deflateTakeWithHistoryProfile_strict (history input : List UInt8) :
    Deflate.deflateTakeWithHistoryProfile .strict history input =
      Deflate.deflateTakeWithHistory history input :=
  Proofs.Formats.Compression.DeflateSpec.deflateTakeWithHistoryProfile_strict history input

theorem Stream.rfc_functional {input out out' rest rest' : List UInt8}
    (h : Stream .rfc input out rest) (h' : Stream .rfc input out' rest') :
    out = out' ∧ rest = rest' :=
  Proofs.Formats.Compression.DeflateSpec.stream_rfc_functional h h'

/-- **Strict = RFC + a decidable side condition.** -/
theorem stream_strict_iff {input out rest : List UInt8} :
    Stream .strict input out rest ↔
      Stream .rfc input out rest ∧ (Deflate.deflateTake input).toBool = true :=
  Proofs.Formats.Compression.DeflateSpec.stream_strict_iff

/-- `HDIST = 30` (31 distance codes; §3.2.7 allows "1 - 32"), all codes complete:
zlib "too many length or distance symbols". -/
theorem rfcOnly_hdist :
    Stream .rfc [0x05, 0xde, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90, 0x56, 0xff, 0x13, 0x94,
      0x10] [0x61] [] ∧
    ∀ out rest, ¬ Stream .strict [0x05, 0xde, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90, 0x56,
      0xff, 0x13, 0x94, 0x10] out rest :=
  Proofs.Formats.Compression.DeflateSpec.rfc_only
    Proofs.Formats.Compression.DeflateSpec.witness_hdist_rfc
    Proofs.Formats.Compression.DeflateSpec.witness_hdist_strict

/-- An incomplete code length code (three symbols of length 2): zlib "invalid
code lengths set". -/
theorem rfcOnly_clCode :
    Stream .rfc [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x00, 0xa0, 0xac, 0xf6, 0x2f, 0x21,
      0x02] [0x61] [] ∧
    ∀ out rest, ¬ Stream .strict [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x00, 0xa0, 0xac,
      0xf6, 0x2f, 0x21, 0x02] out rest :=
  Proofs.Formats.Compression.DeflateSpec.rfc_only
    Proofs.Formats.Compression.DeflateSpec.witness_clCode_rfc
    Proofs.Formats.Compression.DeflateSpec.witness_clCode_strict

/-- An incomplete literal/length code with two used symbols (`a` of length 1,
end-of-block of length 2): zlib "invalid literal/lengths set". -/
theorem rfcOnly_litCode :
    Stream .rfc [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x80, 0xa0, 0xad, 0xfe, 0x3f, 0x11,
      0x02] [0x61] [] ∧
    ∀ out rest, ¬ Stream .strict [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x80, 0xa0, 0xad,
      0xfe, 0x3f, 0x11, 0x02] out rest :=
  Proofs.Formats.Compression.DeflateSpec.rfc_only
    Proofs.Formats.Compression.DeflateSpec.witness_litCode_rfc
    Proofs.Formats.Compression.DeflateSpec.witness_litCode_strict

/-- An incomplete distance code with two used symbols (both of length 2), one
of them used by a back-reference: zlib "invalid distances set". -/
theorem rfcOnly_distCode :
    Stream .rfc [0x0d, 0xc1, 0x81, 0x00, 0x00, 0x00, 0x00, 0x80, 0x20, 0xd6, 0xfc, 0x25, 0xfe,
      0x4d] [0x61, 0x61, 0x61, 0x61] [] ∧
    ∀ out rest, ¬ Stream .strict [0x0d, 0xc1, 0x81, 0x00, 0x00, 0x00, 0x00, 0x80, 0x20, 0xd6,
      0xfc, 0x25, 0xfe, 0x4d] out rest :=
  Proofs.Formats.Compression.DeflateSpec.rfc_only
    Proofs.Formats.Compression.DeflateSpec.witness_distCode_rfc
    Proofs.Formats.Compression.DeflateSpec.witness_distCode_strict

/-- The stream of `rfcOnly_litCode` with the unassigned code word `11` read
where the end-of-block code `10` was: not a stream under either policy. -/
theorem rfc_unassigned :
    ∀ out rest, ¬ Stream .rfc [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x80, 0xa0, 0xad, 0xfe,
      0x3f, 0x11, 0x06] out rest :=
  Proofs.Formats.Compression.DeflateSpec.none_not_rfc
    Proofs.Formats.Compression.DeflateSpec.witness_unassigned_rfc

/-! ### A bounded window

`StreamWithin p window` is `Stream p` with every back-reference distance at most
the window (zlib's `CINFO`, RFC 1950 §2.2). `DecodeProfile.windowed w` is zlib's
policy with that bound. -/

theorem streamWithin_none {p : Policy} {input out rest : List UInt8} :
    StreamWithin p none input out rest ↔ Stream p input out rest :=
  Proofs.Formats.Compression.DeflateSpec.streamWithHistoryWithin_none

theorem streamWithHistoryWithin_none {p : Policy} {history input out rest : List UInt8} :
    StreamWithHistoryWithin p none history input out rest ↔
      StreamWithHistory p history input out rest :=
  Proofs.Formats.Compression.DeflateSpec.streamWithHistoryWithin_none

/-- A window of at least 32 KiB is no restriction (distances are at most 32768). -/
theorem streamWithHistoryWithin_large {p : Policy} {w : Nat} (hw : 32768 ≤ w)
    {history input out rest : List UInt8} :
    StreamWithHistoryWithin p (some w) history input out rest ↔
      StreamWithHistory p history input out rest :=
  Proofs.Formats.Compression.DeflateSpec.streamWithHistoryWithin_large hw

theorem StreamWithHistoryWithin.unwindowed {p : Policy} {w : Option Nat}
    {history input out rest : List UInt8} (h : StreamWithHistoryWithin p w history input out rest) :
    StreamWithHistory p history input out rest :=
  Proofs.Formats.Compression.DeflateSpec.streamWithHistoryWithin_forget h

/-- With a window of `w` bytes, only the last `w` bytes of a history matter. -/
theorem StreamWithHistoryWithin.window {p : Policy} {w : Nat}
    {history input out rest : List UInt8} :
    StreamWithHistoryWithin p (some w) (history.drop (history.length - w)) input out rest ↔
      StreamWithHistoryWithin p (some w) history input out rest :=
  Proofs.Formats.Compression.DeflateSpec.streamWithHistoryWithin_window

theorem deflateTakeWindowed_iff {w : Nat} {input out rest : List UInt8} :
    Deflate.deflateTakeProfile (.windowed w) input = .ok (out, rest) ↔
      StreamWithin .strict (some w) input out rest :=
  Proofs.Formats.Compression.DeflateSpec.deflateTakeWithHistoryWindowed_iff

theorem deflateTakeWithHistoryWindowed_iff {w : Nat} {history input out rest : List UInt8} :
    Deflate.deflateTakeWithHistoryProfile (.windowed w) history input = .ok (out, rest) ↔
      StreamWithHistoryWithin .strict (some w) history input out rest :=
  Proofs.Formats.Compression.DeflateSpec.deflateTakeWithHistoryWindowed_iff

/-- A strict stream (`ab`, then `<length 3, distance 2>`) that a one-byte window
rejects. -/
theorem windowOnly :
    Stream .strict [0x4b, 0x4c, 0x02, 0x42, 0x00] [0x61, 0x62, 0x61, 0x62, 0x61] [] ∧
      ∀ out rest, ¬ StreamWithin .strict (some 1) [0x4b, 0x4c, 0x02, 0x42, 0x00] out rest :=
  Proofs.Formats.Compression.DeflateSpec.window_witness

end Silmaril.Formats.Compression.DeflateSpec

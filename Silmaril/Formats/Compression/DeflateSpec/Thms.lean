module

public import Silmaril.Formats.Compression.DeflateSpec.Defs
public import Silmaril.Formats.Compression.Deflate.Defs
import Silmaril.Proofs.Formats.Compression.DeflateSpec.Policy
import Silmaril.Proofs.Formats.Compression.DeflateSpec.Vectors
import Silmaril.Proofs.Formats.Compression.DeflateSpec.History
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

end Silmaril.Formats.Compression.DeflateSpec

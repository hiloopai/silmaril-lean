module

public import Silmaril.Formats.Compression.Registry.Defs
public import Silmaril.Formats.Compression.Thms
public import Silmaril.Formats.Compression.Gzip.Thms
public import Silmaril.Formats.Compression.Zlib.Thms
public import Silmaril.Formats.Compression.Deflate.Thms
import Silmaril.Proofs.Formats.Compression.Registry

/-!
# Named content codings: facts

Proved (standard axioms):

* the registry: `ofName?_name` (every coding is found by its token),
  case-insensitive and alias lookups (`ofName?_X_GZIP`, `ofName?_x_gzip`,
  `ofName?_x_compress`), `ofName?_chunked`, `ofName?_trailers` (transfer-only
  names are not content codings), `layer_*` and `status_*` (the recorded layer
  and status of each row), `decoder?_proved` (the `proved` codings have a decoder
  and an encoder), `decoder?_planned`;
* the decoders: `decoder?_identity`, `decoder?_gzip` (a gzip file,
  `Gzip.decoder.members`), `decoder?_deflate` (the zlib format); `deflate_ne_raw`,
  `deflate_rejects_raw`, `raw_rejects_deflate`: the `deflate` coding is **not**
  raw DEFLATE (RFC 9110 §8.4.1.2);
* round trips: `gzip_roundTrip`, `gzip_concat` (concatenated members, RFC 1952
  §2.2), `gzip_trailing_zero` (trailing garbage is rejected),
  `deflate_roundTrip`, `encoder_roundTrip`, `decodeAll_encodeAll` (every chain
  of codings with encoders decodes back);
* chains: `decodeChain_append` (decoding an appended chain decodes the later
  codings first), `encodeChain_append`, `decodeChain_encodeChain` (per-coding
  round trips give the chain round trip), `decodeChain_neutral` and
  `encodeChain_neutral` (`identity` is neutral anywhere in a chain),
  `decodeChain_congr`;
* bounds: `guarded_eq_ok_iff`, `guardedChain_sound`, `guardedChain_complete`,
  `guardedChain_within`, `guardedChain_agree` (a guarded chain agrees with the
  unguarded one or reports `tooLarge`); for profiles `Profile.decode_sound`,
  `Profile.decode_le` (every successful non-empty chain is within
  `maxDecoded`), `Profile.decode_complete`, `Profile.decode_single`; for member
  decoders `bounded_eq_ok_iff`, `bounded_tooLarge_iff`, `bounded_malformed_iff`,
  and `sound_bounded`: a finished run of a sound streaming decoder (such as zlib
  1.3.1's inflater, `Inflate.zlib_sound`) whose output fits the limit is the
  bounded decoder's answer;
* RFC constants: `zstdHttpWindowMax_eq` (8 MiB, RFC 9659), `dczWindow_*`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Registry

/-! ## The registry -/

theorem ofName?_name (c : Coding) : ofName? c.name = some c := by
  cases c <;> decide

theorem ofName?_X_GZIP : ofName? (ascii "X-GZIP") = some .gzip := by decide

theorem ofName?_x_gzip : ofName? (ascii "x-gzip") = some .gzip := by decide

theorem ofName?_x_compress : ofName? (ascii "x-compress") = some .compress := by decide

theorem ofName?_Deflate : ofName? (ascii "Deflate") = some .deflate := by decide

/-- `chunked` is a transfer coding (RFC 9112 §7.1), never a content coding. -/
theorem ofName?_chunked : ofName? (ascii "chunked") = none := by decide

/-- `trailers` is reserved in the transfer coding registry (RFC 9112 §7.3). -/
theorem ofName?_trailers : ofName? (ascii "trailers") = none := by decide

theorem lowerOctet_idem (b : UInt8) : lowerOctet (lowerOctet b) = lowerOctet b := by
  revert b; decide

theorem lower_lower (n : Name) : lower (lower n) = lower n := by
  simp only [lower, List.map_map]
  exact List.map_congr_left (fun b _ => lowerOctet_idem b)

theorem ofName?_lower (n : Name) : ofName? (lower n) = ofName? n := by
  simp only [ofName?, lookup, lower_lower]

theorem layer_chunked : (lookup (ascii "chunked")).map Entry.layer = some ⟨false, true⟩ := by
  decide

theorem layer_identity : (lookup (ascii "identity")).map Entry.layer = some ⟨true, false⟩ := by
  decide

theorem layer_gzip : (lookup (ascii "gzip")).map Entry.layer = some ⟨true, true⟩ := by decide

theorem layer_br : (lookup (ascii "br")).map Entry.layer = some ⟨true, false⟩ := by decide

theorem status_proved : Coding.all.filter (·.status == .proved) = [.deflate, .gzip] := by decide

theorem status_planned :
    Coding.all.filter (·.status == .planned) = [.br, .compress, .dcb, .dcz, .exi] := by
  decide

theorem status_zstd : Coding.zstd.status = .partialSubset := by decide

theorem status_aes128gcm : Coding.aes128gcm.status = .abstract := by decide

theorem status_identity : Coding.identity.status = .reserved := by decide

theorem status_pack200gzip : Coding.pack200gzip.status = .deprecated := by decide

/-! ## Decoders -/

theorem decoder?_identity (ext : Externals) : Coding.identity.decoder? ext = some some := rfl

/-- `gzip` decodes a gzip **file**: one or more members (RFC 1952 §2.2). -/
theorem decoder?_gzip (ext : Externals) : Coding.gzip.decoder? ext = some Gzip.decoder.members :=
  rfl

/-- `deflate` decodes the **zlib** format (RFC 9110 §8.4.1.2). -/
theorem decoder?_deflate (ext : Externals) :
    Coding.deflate.decoder? ext = some Zlib.decoder.whole := rfl

/-- `zstd` is the partial frame decoder, with the configured window limit. -/
theorem decoder?_zstd (ext : Externals) :
    Coding.zstd.decoder? ext = some (Zstd.decode ext.zstdWindowMax) := rfl

theorem externals_zstdWindowMax : ({} : Externals).zstdWindowMax = zstdHttpWindowMax := rfl

theorem decoder?_aes128gcm (ext : Externals) : Coding.aes128gcm.decoder? ext = ext.aes128gcm :=
  rfl

theorem decoder?_planned (ext : Externals) {c : Coding}
    (h : c ∈ [Coding.compress, .br, .dcb, .dcz, .exi, .pack200gzip]) :
    c.decoder? ext = none := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem decoder?_proved (ext : Externals) {c : Coding} (h : c.status = .proved) :
    (c.decoder? ext).isSome ∧ c.encoder?.isSome := by
  cases c <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-- A raw DEFLATE stream (zlib level 0, `"abc"`, RFC 1951 stored block) is not a
`deflate` content coding: it has no zlib header. -/
theorem deflate_rejects_raw :
    Zlib.decoder.whole [0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63] = none := by decide

set_option maxRecDepth 100000 in
/-- …while raw DEFLATE accepts it. -/
theorem raw_accepts_raw :
    Deflate.decoder.whole [0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63] =
      some [0x61, 0x62, 0x63] := by decide

set_option maxRecDepth 100000 in
/-- CPython's `zlib.compress(b"hello")` is a `deflate` coding of `hello`, and not a
raw DEFLATE stream. -/
theorem raw_rejects_deflate :
    Zlib.decoder.whole Zlib.sampleHello = some Zlib.helloBytes ∧
      Deflate.decoder.whole Zlib.sampleHello = none := by
  refine ⟨?_, by decide⟩
  simp only [Decoder.whole, Zlib.decoder_sampleHello]

/-- The `deflate` content coding is not raw DEFLATE. -/
theorem deflate_ne_raw : Zlib.decoder.whole ≠ Deflate.decoder.whole := fun h =>
  nomatch (deflate_rejects_raw.symm.trans (congrFun h _)).trans raw_accepts_raw

/-! ## Round trips -/

theorem gzip_roundTrip (data : List UInt8) : Gzip.decoder.members (Gzip.encoder data) = some data :=
  Proofs.Formats.Compression.Registry.gzip_members_encoder data

/-- A gzip body made of several members decodes to the concatenation. -/
theorem gzip_concat {xs : List (List UInt8)} (hxs : xs ≠ []) :
    (Coding.gzip.decoder? {}).bind (· (xs.flatMap Gzip.encoder)) = some xs.flatten :=
  Gzip.members_encoder hxs

/-- Trailing bytes that are not a member are rejected (here a single zero byte;
GNU gzip would warn and ignore trailing zeros). -/
theorem gzip_trailing_zero (data : List UInt8) :
    Gzip.decoder.members (Gzip.encoder data ++ [0]) = none :=
  Proofs.Formats.Compression.Registry.gzip_trailing_zero data

theorem deflate_roundTrip (data : List UInt8) :
    Zlib.decoder.whole (Zlib.encoder data) = some data :=
  Zlib.roundTrip.whole data

theorem encoder_roundTrip (ext : Externals) {c : Coding} {e : Encoder} (he : c.encoder? = some e)
    (data : List UInt8) : stage ext c (e data) = .ok data :=
  Proofs.Formats.Compression.Registry.encoder_roundTrip ext he data

theorem decodeAll_encodeAll (ext : Externals) {cs : List Coding} {data coded : List UInt8}
    (h : encodeAll cs data = some coded) : decodeAll ext cs coded = .ok data :=
  Proofs.Formats.Compression.Registry.decodeAll_encodeAll ext h

/-! ## Chains -/

section Chain

variable {α ε : Type}

theorem decodeChain_append (dec : α → List UInt8 → Except ε (List UInt8)) (cs ds : List α)
    (bytes : List UInt8) :
    decodeChain dec (cs ++ ds) bytes = (decodeChain dec ds bytes).bind (decodeChain dec cs) :=
  Proofs.Formats.Compression.Registry.decodeChain_append dec cs ds bytes

theorem encodeChain_append (enc : α → List UInt8 → Option (List UInt8)) (cs ds : List α)
    (data : List UInt8) :
    encodeChain enc (cs ++ ds) data = (encodeChain enc cs data).bind (encodeChain enc ds) :=
  Proofs.Formats.Compression.Registry.encodeChain_append enc cs ds data

/-- Per-coding round trips give the round trip of every chain. -/
theorem decodeChain_encodeChain {dec : α → List UInt8 → Except ε (List UInt8)}
    {enc : α → List UInt8 → Option (List UInt8)}
    (h : ∀ c data coded, enc c data = some coded → dec c coded = .ok data)
    (cs : List α) (data coded : List UInt8) (hc : encodeChain enc cs data = some coded) :
    decodeChain dec cs coded = .ok data :=
  Proofs.Formats.Compression.Registry.decodeChain_encodeChain h cs data coded hc

theorem decodeChain_congr {f g : α → List UInt8 → Except ε (List UInt8)} {cs : List α}
    (h : ∀ c ∈ cs, ∀ b, f c b = g c b) (b : List UInt8) :
    decodeChain f cs b = decodeChain g cs b :=
  Proofs.Formats.Compression.Registry.decodeChain_congr h b

/-- A coding that decodes to its input (such as `identity`) is neutral anywhere. -/
theorem decodeChain_neutral {dec : α → List UInt8 → Except ε (List UInt8)} {i : α}
    (hi : ∀ b, dec i b = .ok b) (cs ds : List α) (bytes : List UInt8) :
    decodeChain dec (cs ++ i :: ds) bytes = decodeChain dec (cs ++ ds) bytes :=
  Proofs.Formats.Compression.Registry.decodeChain_neutral hi cs ds bytes

theorem encodeChain_neutral {enc : α → List UInt8 → Option (List UInt8)} {i : α}
    (hi : ∀ d, enc i d = some d) (cs ds : List α) (data : List UInt8) :
    encodeChain enc (cs ++ i :: ds) data = encodeChain enc (cs ++ ds) data :=
  Proofs.Formats.Compression.Registry.encodeChain_neutral hi cs ds data

end Chain

theorem stage_identity (ext : Externals) (b : List UInt8) : stage ext .identity b = .ok b := rfl

theorem decodeAll_identity (ext : Externals) (cs ds : List Coding) (bytes : List UInt8) :
    decodeAll ext (cs ++ .identity :: ds) bytes = decodeAll ext (cs ++ ds) bytes :=
  decodeChain_neutral (stage_identity ext) cs ds bytes

/-! ## Bounds -/

section Guarded

variable {α : Type} {within : List UInt8 → List UInt8 → Bool}
  {dec : α → List UInt8 → Except (DecodeError α) (List UInt8)}

theorem guarded_eq_ok_iff {c : α} {bytes out : List UInt8} :
    guarded within dec c bytes = .ok out ↔ dec c bytes = .ok out ∧ within bytes out = true :=
  Proofs.Formats.Compression.Registry.guarded_eq_ok_iff

theorem guardedChain_sound {cs : List α} {bytes out : List UInt8}
    (h : guardedChain within dec cs bytes = .ok out) : decodeChain dec cs bytes = .ok out :=
  Proofs.Formats.Compression.Registry.guardedChain_sound h

theorem guardedChain_complete {cs : List α} {bytes out : List UInt8}
    (h : decodeChain dec cs bytes = .ok out) (hw : StagesWithin within dec cs bytes) :
    guardedChain within dec cs bytes = .ok out :=
  Proofs.Formats.Compression.Registry.guardedChain_complete h hw

/-- The last stage of a successful guarded chain satisfies the bound. -/
theorem guardedChain_within {c : α} {cs : List α} {bytes out : List UInt8}
    (h : guardedChain within dec (c :: cs) bytes = .ok out) :
    ∃ mid, guardedChain within dec cs bytes = .ok mid ∧ within mid out = true :=
  Proofs.Formats.Compression.Registry.guardedChain_within h

theorem guardedChain_agree {cs : List α} {bytes out : List UInt8}
    (h : decodeChain dec cs bytes = .ok out) :
    guardedChain within dec cs bytes = .ok out ∨
      ∃ c, guardedChain within dec cs bytes = .error (.tooLarge c) :=
  Proofs.Formats.Compression.Registry.guardedChain_agree h

end Guarded

theorem Profile.limit_le (p : Profile) (n : Nat) : p.limit n ≤ p.maxDecoded :=
  Proofs.Formats.Compression.Registry.limit_le p n

theorem Profile.decode_sound {p : Profile} {ext : Externals} {cs : List Coding}
    {bytes out : List UInt8} (h : p.decode ext cs bytes = .ok out) :
    decodeAll ext cs bytes = .ok out :=
  Proofs.Formats.Compression.Registry.profile_decode_sound h

/-- **Output bound**: a successful decode of a non-empty chain under a profile is
at most `maxDecoded` bytes (as is every intermediate stage, by
`Profile.decode_le` on the chain's suffixes). -/
theorem Profile.decode_le {p : Profile} {ext : Externals} {c : Coding} {cs : List Coding}
    {bytes out : List UInt8} (h : p.decode ext (c :: cs) bytes = .ok out) :
    out.length ≤ p.maxDecoded :=
  Proofs.Formats.Compression.Registry.profile_decode_le h

/-- **Agreement within the limit**: a supported chain whose every stage fits the
profile decodes as without bounds. -/
theorem Profile.decode_complete {p : Profile} {ext : Externals} {cs : List Coding}
    {bytes out : List UInt8} (hs : ∀ c ∈ cs, p.supports ext c = true)
    (hd : decodeAll ext cs bytes = .ok out)
    (hw : StagesWithin p.within (Registry.stage ext) cs bytes) :
    p.decode ext cs bytes = .ok out :=
  Proofs.Formats.Compression.Registry.profile_decode_complete hs hd hw

theorem Profile.decode_single {p : Profile} {ext : Externals} {c : Coding} {e : Encoder}
    (hs : p.supports ext c = true) (he : c.encoder? = some e) {data : List UInt8}
    (hl : data.length ≤ p.limit (e data).length) : p.decode ext [c] (e data) = .ok data :=
  Proofs.Formats.Compression.Registry.profile_decode_single hs he hl

theorem httpProfile_supports (n : Nat) (ext : Externals) :
    Coding.all.filter ((httpProfile n).supports ext) = [.deflate, .gzip, .identity] := by
  simp only [Coding.all, httpProfile, Profile.supports, List.filter]
  rfl

theorem bounded_eq_ok_iff {d : Decoder} {limit : Nat} {bytes out rest : List UInt8} :
    d.bounded limit bytes = .ok (out, rest) ↔ d bytes = some (out, rest) ∧ out.length ≤ limit :=
  Proofs.Formats.Compression.Registry.bounded_eq_ok_iff

theorem bounded_tooLarge_iff {d : Decoder} {limit : Nat} {bytes : List UInt8} :
    d.bounded limit bytes = .error .tooLarge ↔
      ∃ out rest, d bytes = some (out, rest) ∧ limit < out.length :=
  Proofs.Formats.Compression.Registry.bounded_tooLarge_iff

theorem bounded_malformed_iff {d : Decoder} {limit : Nat} {bytes : List UInt8} :
    d.bounded limit bytes = .error .malformed ↔ d bytes = none :=
  Proofs.Formats.Compression.Registry.bounded_malformed_iff

/-- A finished run of a sound streaming decoder whose output fits the limit is the
bounded member decoder's answer. -/
theorem sound_bounded {i : Incremental} {d : Decoder} (hs : i.Sound d) {initial : List UInt8}
    {calls : List i.Call} {out : List UInt8} {limit : Nat}
    (hdone : i.status (i.run (i.start initial) calls) = .done out) (hl : out.length ≤ limit) :
    ∃ rest, d.bounded limit (initial ++ i.delivered calls) = .ok (out, rest) :=
  Proofs.Formats.Compression.Registry.sound_bounded hs hdone hl

/-! ## Constants -/

theorem zstdHttpWindowMax_eq : zstdHttpWindowMax = 8388608 := rfl

theorem dczWindow_small : dczWindow 0 = 8 * mebibyte := rfl

theorem dczWindow_large : dczWindow (200 * mebibyte) = 128 * mebibyte := by decide

end Silmaril.Formats.Compression.Registry

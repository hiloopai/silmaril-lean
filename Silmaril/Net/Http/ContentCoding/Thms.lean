module

public import Silmaril.Net.Http.ContentCoding.Defs
public import Silmaril.Formats.Compression.Registry.Thms
import Silmaril.Proofs.Net.Http.ContentCoding

/-!
# Content codings in HTTP: facts

Proved (standard axioms):

* quality values: `parseAcceptEncoding_le` (from `Qvalue.parseQvalue_le`), `qOf_le`: weights are
  thousandths in `0 … 1000`;
* selection: `select_pos` (a selected coding has `q > 0`), `select_mem` (it is a
  server coding or `identity`), `select_max` (no candidate has a higher weight),
  `select_eq_none` (nothing is selected only when every candidate has `q = 0`),
  `selectFor_supported` (under a profile, the selection is `identity` or a
  supported coding);
* the identity rules of RFC 9110 §12.5.3: `qOf_identity_eq_zero_iff` (`identity`
  is unacceptable exactly when excluded by `identity;q=0`, or by `*;q=0` without
  an `identity` entry); `qOf_empty`, `select_empty` (an empty field value means
  no content coding: only `identity`); `qOf_noField`, `select_noField` (no field:
  every coding acceptable, the server's first choice is selected);
* Content-Encoding: `decodeContent_none` (no field: the body as is),
  `decodeContent_sound`, `decodeContent_le` (a decoded body is the body itself or
  within the profile's `maxDecoded`), `decodeContent_gzip`,
  `decodeContent_deflate` (the stored encoders round-trip through the HTTP path),
  `decodeContent_gnu` (GNU gzip's `hello`, labelled `x-gzip`), and
  `decodeContent_chunked` (a transfer coding is not a content coding);
* the examples of RFC 9110 §12.5.3, parsed (`example_*`).
-/

@[expose] public section

namespace Silmaril.Net.Http.ContentCoding

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Registry
open Silmaril.Net.Http.Qvalue (parseQvalue)

/-! ## Quality values -/

theorem parseQvalue_half : parseQvalue (ascii "0.5") = some 500 := by decide

theorem parseQvalue_one : parseQvalue (ascii "1.000") = some 1000 := by decide

theorem parseQvalue_least : parseQvalue (ascii "0.001") = some 1 := by decide

/-- More than three decimals, and values above 1, are not qvalues. -/
theorem parseQvalue_rejects :
    parseQvalue (ascii "0.0001") = none ∧ parseQvalue (ascii "1.001") = none ∧
      parseQvalue (ascii "2") = none := by decide

theorem parseAcceptEncoding_le {v : List UInt8} {prefs : List Pref}
    (h : parseAcceptEncoding v = some prefs) : ∀ p ∈ prefs, p.q ≤ 1000 :=
  Proofs.Net.Http.ContentCoding.parseAcceptEncoding_le h

theorem qOf_le {prefs : List Pref} (hp : ∀ p ∈ prefs, p.q ≤ 1000) (c : Coding) :
    qOf (some prefs) c ≤ 1000 :=
  Proofs.Net.Http.ContentCoding.qOf_le hp c

/-! ## Selection -/

section Select

variable {field : Option (List Pref)} {supported : List Coding} {c : Coding}

theorem select_pos (h : select field supported = some c) : 0 < qOf field c :=
  (Proofs.Net.Http.ContentCoding.select_spec h).1

theorem select_mem (h : select field supported = some c) : c ∈ supported ∨ c = .identity := by
  have := (Proofs.Net.Http.ContentCoding.select_spec h).2.1
  simpa using this

theorem select_max (h : select field supported = some c) :
    ∀ d ∈ supported ++ [.identity], qOf field d ≤ qOf field c :=
  (Proofs.Net.Http.ContentCoding.select_spec h).2.2

theorem select_eq_none (h : select field supported = none) :
    ∀ d ∈ supported ++ [.identity], qOf field d = 0 :=
  Proofs.Net.Http.ContentCoding.select_eq_none h

end Select

theorem selectFor_supported {p : Profile} {ext : Externals} {field : Option (List Pref)}
    {c : Coding} (h : selectFor p ext field = some c) :
    0 < qOf field c ∧ (c = .identity ∨ p.supports ext c = true) :=
  Proofs.Net.Http.ContentCoding.selectFor_spec h

/-! ## The identity rules (RFC 9110 §12.5.3) -/

/-- Rule 2: `identity` is excluded exactly by `identity;q=0`, or by `*;q=0`
without an entry for `identity`. -/
theorem qOf_identity_eq_zero_iff (prefs : List Pref) :
    qOf (some prefs) .identity = 0 ↔
      lookupQ prefs Coding.identity.name = some 0 ∨
        (lookupQ prefs Coding.identity.name = none ∧ anyQ prefs = some 0) :=
  Proofs.Net.Http.ContentCoding.qOf_identity_eq_zero_iff prefs

theorem acceptable_identity_iff (prefs : List Pref) :
    acceptable (some prefs) .identity = true ↔
      ¬ (lookupQ prefs Coding.identity.name = some 0 ∨
        (lookupQ prefs Coding.identity.name = none ∧ anyQ prefs = some 0)) := by
  rw [← qOf_identity_eq_zero_iff, acceptable, decide_eq_true_iff]
  omega

/-- An empty field value parses to no preferences. -/
theorem parseAcceptEncoding_empty : parseAcceptEncoding [] = some [] := rfl

/-- With an empty field value, only `identity` is acceptable. -/
theorem qOf_empty (c : Coding) : qOf (some []) c = if c = .identity then 1 else 0 :=
  Proofs.Net.Http.ContentCoding.qOf_empty c

/-- "An Accept-Encoding header field with a field value that is empty implies that
the user agent does not want any content coding in response." -/
theorem select_empty (supported : List Coding) : select (some []) supported = some .identity :=
  Proofs.Net.Http.ContentCoding.select_empty supported

/-- Rule 1: without the field every coding is acceptable. -/
theorem qOf_noField (c : Coding) : qOf none c = 1000 := rfl

theorem select_noField (c : Coding) (cs : List Coding) : select none (c :: cs) = some c :=
  Proofs.Net.Http.ContentCoding.select_noField c cs

/-! ## RFC 9110 §12.5.3 examples -/

theorem example_compress_gzip :
    parseAcceptEncoding (ascii "compress, gzip") =
      some [⟨.named (ascii "compress"), 1000⟩, ⟨.named (ascii "gzip"), 1000⟩] := by decide

theorem example_star : parseAcceptEncoding (ascii "*") = some [⟨.any, 1000⟩] := by decide

theorem example_weights :
    parseAcceptEncoding (ascii "compress;q=0.5, gzip;q=1.0") =
      some [⟨.named (ascii "compress"), 500⟩, ⟨.named (ascii "gzip"), 1000⟩] := by decide

theorem example_identity :
    parseAcceptEncoding (ascii "gzip;q=1.0, identity; q=0.5, *;q=0") =
      some [⟨.named (ascii "gzip"), 1000⟩, ⟨.named (ascii "identity"), 500⟩, ⟨.any, 0⟩] := by
  decide

/-- Aliases, case and `OWS` are normalised; empty list elements are ignored. -/
theorem example_alias :
    parseAcceptEncoding (ascii "X-Gzip ;Q=0.125 , ,br") =
      some [⟨.named (ascii "gzip"), 125⟩, ⟨.named (ascii "br"), 1000⟩] := by decide

/-- With `gzip;q=1.0, identity; q=0.5, *;q=0`, a gzip server sends gzip, a br-only
server falls back to identity. -/
theorem example_select :
    select (parseAcceptEncoding (ascii "gzip;q=1.0, identity; q=0.5, *;q=0"))
        [.br, .gzip] = some .gzip ∧
      select (parseAcceptEncoding (ascii "gzip;q=1.0, identity; q=0.5, *;q=0"))
        [.br] = some .identity := by decide

/-- `identity;q=0` with nothing else acceptable leaves no choice (406). -/
theorem example_none :
    select (parseAcceptEncoding (ascii "br, identity;q=0")) [.gzip] = none := by decide

/-- `*;q=0` excludes identity when it has no entry of its own. -/
theorem example_star_zero :
    select (parseAcceptEncoding (ascii "*;q=0")) [.gzip, .deflate] = none := by decide

/-! ## Content-Encoding -/

theorem example_contentEncoding :
    parseContentEncoding (ascii "gzip, Deflate") = some [ascii "gzip", ascii "deflate"] := by
  decide

theorem renderContentEncoding_example :
    renderContentEncoding [.deflate, .gzip] = ascii "deflate, gzip" := by decide

theorem decodeContent_none (p : Profile) (ext : Externals) (body : List UInt8) :
    decodeContent p ext none body = .ok body := rfl

/-- `chunked` is a transfer coding: as a Content-Encoding it names no content coding. -/
theorem decodeContent_chunked (p : Profile) (ext : Externals) (body : List UInt8) :
    decodeContent p ext (some (ascii "chunked")) body = .error (.unknownCoding (ascii "chunked")) :=
  rfl

theorem decodeContent_sound {p : Profile} {ext : Externals} {v body out : List UInt8}
    (h : decodeContent p ext (some v) body = .ok out) :
    ∃ names cs, parseContentEncoding v = some names ∧ resolve names = .ok cs ∧
      p.decode ext cs body = .ok out :=
  Proofs.Net.Http.ContentCoding.decodeContent_sound h

/-- A decoded body is the body itself (an empty list of codings) or within the
profile's `maxDecoded`. -/
theorem decodeContent_le {p : Profile} {ext : Externals} {v body out : List UInt8}
    (h : decodeContent p ext (some v) body = .ok out) :
    out = body ∨ out.length ≤ p.maxDecoded :=
  Proofs.Net.Http.ContentCoding.decodeContent_le h

theorem decodeContent_gzip {L : Nat} (ext : Externals) {data : List UInt8} (hl : data.length ≤ L) :
    decodeContent (httpProfile L) ext (some (ascii "gzip")) (Gzip.encoder data) = .ok data :=
  Proofs.Net.Http.ContentCoding.decodeContent_gzip ext hl

theorem decodeContent_deflate {L : Nat} (ext : Externals) {data : List UInt8}
    (hl : data.length ≤ L) :
    decodeContent (httpProfile L) ext (some (ascii "deflate")) (Zlib.encoder data) = .ok data :=
  Proofs.Net.Http.ContentCoding.decodeContent_deflate ext hl

/-- GNU gzip's encoding of `hello`, sent as `Content-Encoding: x-gzip`. -/
theorem decodeContent_gnu {L : Nat} (ext : Externals) (hl : 5 ≤ L) :
    decodeContent (httpProfile L) ext (some (ascii "x-gzip")) gzipGnu.data.toList =
      .ok helloBytes.data.toList :=
  Proofs.Net.Http.ContentCoding.decodeContent_gnu ext hl

/-- The same body with a 4-byte limit is `tooLarge`. -/
theorem decodeContent_gnu_tooLarge (ext : Externals) :
    decodeContent (httpProfile 4) ext (some (ascii "x-gzip")) gzipGnu.data.toList =
      .error (.stage (.tooLarge .gzip)) :=
  Proofs.Net.Http.ContentCoding.decodeContent_gnu_tooLarge ext

end Silmaril.Net.Http.ContentCoding

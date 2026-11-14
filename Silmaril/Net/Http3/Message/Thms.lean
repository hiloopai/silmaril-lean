module

public import Silmaril.Net.Http3.Message.Defs
import Silmaril.Proofs.Net.Http3.Message

@[expose] public section

/-!
# HTTP/3 messages: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http3/Message.lean`):

* `requestOf_requestFields`: a canonical `Http.Request` whose regular fields are valid HTTP/3
  fields and whose header section satisfies RFC 9114 §4.2–§4.3 (`Http2.validRequest`, reused)
  maps to field lists and back to itself — method, scheme, authority, path, field lines,
  content and trailers are all preserved;
* `responseOf_responseFields`: the same for responses with a three-digit status code;
* `parseStatus_statusDigits`: `:status` values round trip for every code below 1000.

CHECKED (`rfl`/`decide`): a GET request mapped from its decoded field list, the rejection of
an uppercase field name, of a `transfer-encoding` field (§4.1) and of a pseudo-header field in
a trailer section (§4.3), and a field-section-size check against
`SETTINGS_MAX_FIELD_SECTION_SIZE` (§4.2.2).
-/

namespace Silmaril.Net.Http3

open Silmaril.Net.Hpack Silmaril.Net.Http2 Silmaril.Net.Http

theorem parseStatus_statusDigits {s : Nat} (h : s < 1000) : parseStatus (statusDigits s) = some s :=
  Silmaril.Proofs.Net.Http3.Message.parseStatus_statusDigits h

theorem requestOf_requestFields (r : Request) (hm : r.method.Canonical)
    (hs : ∀ sc, r.target.scheme = some sc → schemeCanonical sc)
    (hreg : ∀ l ∈ r.headers, validRegular (ofLine l) = true)
    (hv : validRequest (requestFields r) = true) (ht : trailersValid (requestTrailers r) = true)
    (hcl : contentLengthMatches (requestFields r) r.content.length = true) :
    requestOf (requestFields r) r.content (requestTrailers r) = some r :=
  Silmaril.Proofs.Net.Http3.Message.requestOf_requestFields r hm hs hreg hv ht hcl

theorem responseOf_responseFields (r : Response) (hs : r.status < 1000)
    (hreg : ∀ l ∈ r.headers, validRegular (ofLine l) = true)
    (hv : validResponse (responseFields r) = true)
    (ht : trailersValid (r.trailers.map ofLine) = true)
    (hcl : contentLengthMatches (responseFields r) r.content.length = true) :
    responseOf (responseFields r) r.content (r.trailers.map ofLine) = some r :=
  Silmaril.Proofs.Net.Http3.Message.responseOf_responseFields r hs hreg hv ht hcl

/-! ## Known answers -/

/-- `GET https://example.com/index.html` with one `accept` field. -/
def sampleFields : List Entry :=
  [.ofStrings ":method" "GET", .ofStrings ":scheme" "https", .ofStrings ":authority" "example.com",
   .ofStrings ":path" "/index.html", .ofStrings "accept" "*/*"]

theorem sample_request :
    requestOf sampleFields [] [] =
      some { control := ⟨.get, ⟨some .https, some (ascii "example.com"), some (ascii "/index.html")⟩⟩
             headers := [⟨ascii "accept", ascii "*/*"⟩], content := [], trailers := [] } := by
  decide

theorem sample_uppercase :
    requestOf (sampleFields ++ [.ofStrings "Accept" "*/*"]) [] [] = none := by decide

theorem sample_transfer_encoding :
    requestOf (sampleFields ++ [.ofStrings "transfer-encoding" "chunked"]) [] [] = none := by decide

theorem sample_pseudo_trailer :
    requestOf sampleFields [] [.ofStrings ":path" "/"] = none := by decide

theorem sample_content_length :
    requestOf (sampleFields ++ [.ofStrings "content-length" "3"]) [1, 2] [] = none := by decide

/-- The sample header section is 5 fields of 32 bytes overhead plus 68 bytes of names and
values: 228 bytes. -/
theorem sample_limit :
    withinLimit { maxFieldSectionSize := some 228 } sampleFields = true ∧
      withinLimit { maxFieldSectionSize := some 227 } sampleFields = false := by decide

theorem sample_response :
    responseOf [.ofStrings ":status" "204"] [] [] =
      some { control := 204, headers := [], content := [], trailers := [] } := by decide

end Silmaril.Net.Http3

module

public import Silmaril.Net.Http2.Fields.Defs
import Silmaril.Proofs.Net.Http2.Fields

@[expose] public section

/-!
# HTTP/2 field sections: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http2/Fields.lean`), RFC 9113 §8.2:

* `validRequest_regular`, `validResponse_regular`: every regular field of a well-formed
  request or response satisfies the field rules of §8.2.1 and §8.2.2;
* **translation safety** (the reason for §8.2.1; see §10.3, intermediary encapsulation
  attacks): for such a field, its HTTP/1.1 line `name ": " value` contains no CR, LF or NUL
  (`crlf_not_mem_h1Line`), so it cannot inject a line or a message into an HTTP/1.1
  connection, and the first colon of the line is the separator (`breakColon_h1Line`), so an
  HTTP/1.1 recipient reads back the same name and value;
* `validRegular_not_connectionSpecific`: no `Transfer-Encoding`, `Connection`, `Keep-Alive`,
  `Proxy-Connection` or `Upgrade` field survives, so the HTTP/1.1 framing of a translated
  message cannot be chosen by an HTTP/2 peer through these fields.

The full smuggling theorem, connecting this with the HTTP/1.1 framing rules
(`Silmaril.Net.Http1.Framing`) and `content-length` (§8.1.1), is roadmap work.
-/

namespace Silmaril.Net.Http2

open Silmaril.Net.Hpack

theorem validRequest_regular {fs : List Entry} (h : validRequest fs = true) {e : Entry}
    (he : e ∈ fs) (hp : isPseudo e = false) : validRegular e = true :=
  Silmaril.Proofs.Net.Http2.validRequest_regular h he hp

theorem validResponse_regular {fs : List Entry} (h : validResponse fs = true) {e : Entry}
    (he : e ∈ fs) (hp : isPseudo e = false) : validRegular e = true :=
  Silmaril.Proofs.Net.Http2.validResponse_regular h he hp

theorem crlf_not_mem_h1Line {e : Entry} (h : validRegular e = true) :
    (0x0d : UInt8) ∉ h1Line e ∧ (0x0a : UInt8) ∉ h1Line e ∧ (0x00 : UInt8) ∉ h1Line e :=
  Silmaril.Proofs.Net.Http2.crlf_not_mem_h1Line h

theorem breakColon_h1Line {e : Entry} (h : validRegular e = true) :
    breakColon (h1Line e) = (e.name, 0x20 :: e.value) :=
  Silmaril.Proofs.Net.Http2.breakColon_h1Line h

theorem validRegular_not_connectionSpecific {e : Entry} (h : validRegular e = true) :
    e.name ∉ connectionSpecific :=
  Silmaril.Proofs.Net.Http2.validRegular_not_connectionSpecific h

/-! Examples, checked by evaluation. -/

/-- The fields of a request from strings. -/
def fields (xs : List (String × String)) : List Entry := xs.map fun (n, v) => Entry.ofStrings n v

/-- A GET request (§8.3.1, §8.8.1). -/
example : validRequest (fields [(":method", "GET"), (":scheme", "https"), (":path", "/"),
    (":authority", "example.org"), ("accept", "image/jpeg")]) = true := by decide +kernel

/-- CONNECT omits `:scheme` and `:path` (§8.5). -/
example : validRequest (fields [(":method", "CONNECT"), (":authority", "example.org:443")]) =
    true := by decide +kernel

/-- Missing `:path` (§8.3.1). -/
example : validRequest (fields [(":method", "GET"), (":scheme", "https")]) = false := by
  decide +kernel

/-- A pseudo-header field after a regular field (§8.3). -/
example : validRequest (fields [(":method", "GET"), (":scheme", "https"), ("accept", "*/*"),
    (":path", "/")]) = false := by decide +kernel

/-- Upper case in a field name (§8.2.1). -/
example : validRequest (fields [(":method", "GET"), (":scheme", "https"), (":path", "/"),
    ("Accept", "*/*")]) = false := by decide +kernel

/-- `transfer-encoding` is connection-specific (§8.2.2); `te: trailers` is allowed. -/
example : validRequest (fields [(":method", "POST"), (":scheme", "https"), (":path", "/"),
    ("transfer-encoding", "chunked")]) = false := by decide +kernel
example : validRequest (fields [(":method", "POST"), (":scheme", "https"), (":path", "/"),
    ("te", "trailers")]) = true := by decide +kernel

/-- A CR LF in a value, the classic header-injection payload (§8.2.1). -/
example : validRequest (fields [(":method", "GET"), (":scheme", "https"), (":path", "/"),
    ("x", "a\r\nTransfer-Encoding: chunked")]) = false := by decide +kernel

/-- A response with `:status` and a matching `content-length` (§8.3.2, §8.1.1). -/
example : validResponse (fields [(":status", "200"), ("content-length", "5")]) = true := by
  decide +kernel
example : contentLengthMatches (fields [(":status", "200"), ("content-length", "5")]) 5 = true := by
  decide +kernel
example : contentLengthMatches (fields [(":status", "200"), ("content-length", "5")]) 6 = false := by
  decide +kernel

end Silmaril.Net.Http2

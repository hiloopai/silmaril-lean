module

public import Silmaril.Net.Hpack.Table.Defs

@[expose] public section

/-!
# QPACK static table (RFC 9204 §3.1, Appendix A)

"The static table consists of a predefined list of field lines, each of which has a fixed
index over time. Its entries are defined in Appendix A" (§3.1). It has 99 entries, indices
`0..98`: "Note that the QPACK static table is indexed from 0, whereas the HPACK static table is
indexed from 1."

Entries reuse HPACK's `Entry` (a name and a value, as octets), whose `Entry.size`
(`|name| + |value| + 32`) is also QPACK's entry size (§3.2.1).

"When the decoder encounters an invalid static table index in a field line representation, it
MUST treat this as a connection error of type QPACK_DECOMPRESSION_FAILED. If this index is
received on the encoder stream, this MUST be treated as a connection error of type
QPACK_ENCODER_STREAM_ERROR" (§3.1). `staticLookup` returns `none` for such an index; the
callers choose the error.

The list below was transcribed from Appendix A (Table 4), joining the values the RFC wraps
across lines (for example index 52, `text/html; charset=utf-8`).
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry Entry.ofStrings)

/-- The static table (Appendix A), index `i` at position `i`. -/
def staticTable : List Entry :=
 [
  (":authority", ""),
  (":path", "/"),
  ("age", "0"),
  ("content-disposition", ""),
  ("content-length", "0"),
  ("cookie", ""),
  ("date", ""),
  ("etag", ""),
  ("if-modified-since", ""),
  ("if-none-match", ""),
  ("last-modified", ""),
  ("link", ""),
  ("location", ""),
  ("referer", ""),
  ("set-cookie", ""),
  (":method", "CONNECT"),
  (":method", "DELETE"),
  (":method", "GET"),
  (":method", "HEAD"),
  (":method", "OPTIONS"),
  (":method", "POST"),
  (":method", "PUT"),
  (":scheme", "http"),
  (":scheme", "https"),
  (":status", "103"),
  (":status", "200"),
  (":status", "304"),
  (":status", "404"),
  (":status", "503"),
  ("accept", "*/*"),
  ("accept", "application/dns-message"),
  ("accept-encoding", "gzip, deflate, br"),
  ("accept-ranges", "bytes"),
  ("access-control-allow-headers", "cache-control"),
  ("access-control-allow-headers", "content-type"),
  ("access-control-allow-origin", "*"),
  ("cache-control", "max-age=0"),
  ("cache-control", "max-age=2592000"),
  ("cache-control", "max-age=604800"),
  ("cache-control", "no-cache"),
  ("cache-control", "no-store"),
  ("cache-control", "public, max-age=31536000"),
  ("content-encoding", "br"),
  ("content-encoding", "gzip"),
  ("content-type", "application/dns-message"),
  ("content-type", "application/javascript"),
  ("content-type", "application/json"),
  ("content-type", "application/x-www-form-urlencoded"),
  ("content-type", "image/gif"),
  ("content-type", "image/jpeg"),
  ("content-type", "image/png"),
  ("content-type", "text/css"),
  ("content-type", "text/html; charset=utf-8"),
  ("content-type", "text/plain"),
  ("content-type", "text/plain;charset=utf-8"),
  ("range", "bytes=0-"),
  ("strict-transport-security", "max-age=31536000"),
  ("strict-transport-security", "max-age=31536000; includesubdomains"),
  ("strict-transport-security", "max-age=31536000; includesubdomains; preload"),
  ("vary", "accept-encoding"),
  ("vary", "origin"),
  ("x-content-type-options", "nosniff"),
  ("x-xss-protection", "1; mode=block"),
  (":status", "100"),
  (":status", "204"),
  (":status", "206"),
  (":status", "302"),
  (":status", "400"),
  (":status", "403"),
  (":status", "421"),
  (":status", "425"),
  (":status", "500"),
  ("accept-language", ""),
  ("access-control-allow-credentials", "FALSE"),
  ("access-control-allow-credentials", "TRUE"),
  ("access-control-allow-headers", "*"),
  ("access-control-allow-methods", "get"),
  ("access-control-allow-methods", "get, post, options"),
  ("access-control-allow-methods", "options"),
  ("access-control-expose-headers", "content-length"),
  ("access-control-request-headers", "content-type"),
  ("access-control-request-method", "get"),
  ("access-control-request-method", "post"),
  ("alt-svc", "clear"),
  ("authorization", ""),
  ("content-security-policy", "script-src 'none'; object-src 'none'; base-uri 'none'"),
  ("early-data", "1"),
  ("expect-ct", ""),
  ("forwarded", ""),
  ("if-range", ""),
  ("origin", ""),
  ("purpose", "prefetch"),
  ("server", ""),
  ("timing-allow-origin", "*"),
  ("upgrade-insecure-requests", "1"),
  ("user-agent", ""),
  ("x-forwarded-for", ""),
  ("x-frame-options", "deny"),
  ("x-frame-options", "sameorigin")
 ].map fun (n, v) => Entry.ofStrings n v

/-- The number of static entries (99). -/
def staticLength : Nat := 99

/-- The static entry at index `i` (§3.1); `none` for an invalid index. -/
def staticLookup (i : Nat) : Option Entry := staticTable[i]?

end Silmaril.Net.Qpack

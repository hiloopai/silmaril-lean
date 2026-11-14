module

public import Silmaril.Net.Http1.Pipeline.Defs
public import Silmaril.Net.Http1.Examples.Defs
public meta import Silmaril.Net.Http1.Pipeline.Defs
public meta import Silmaril.Net.Http1.Examples.Defs

/-!
# HTTP/1.1 compliance examples

Executable checks (`#guard`, evaluated when the module is built) of the request checks,
connection management, profiles and the pipelined server, on requests from RFC 9112 and on
the usual smuggling and noncompliance probes. The theorems are in the `Thms` headers; these
checks exercise the executable definitions on concrete octets.
-/

@[expose] public section

namespace Silmaril.Net.Http1.ComplianceExamples

open Silmaril.Parse.ByteParse
open Silmaril.Net.Http1.Examples (b okAt isErr value?)

/-- Parse a head and check it with the default configuration; the status a server answers
(`200` for acceptable). -/
def statusOf (cfg : ServerConfig) (s : String) : Nat :=
  match parseRequestHead (b s) with
  | .err _ => 400
  | .ok h _ => match checkRequest cfg h with
    | .ok _ => 200
    | .error e => e.status

def dflt : ServerConfig := {}

/-! ## Line-level leniency is rejected by the strict head grammar (RFC 9112 §2.2, §5.1, §5.2) -/

-- bare LF as a line terminator
#guard isErr (parseRequestHead (b "GET / HTTP/1.1\nHost: a\n\n"))
-- obs-fold
#guard isErr (parseRequestHead (b "GET / HTTP/1.1\r\nHost: a\r\nX: a\r\n b\r\n\r\n"))
-- whitespace between field name and colon (§5.1: MUST reject with 400)
#guard isErr (parseRequestHead (b "GET / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding : chunked\r\n\r\n"))
-- whitespace before the first field line (§2.2)
#guard isErr (parseRequestHead (b "GET / HTTP/1.1\r\n Host: a\r\n\r\n"))

/-! ## Request checks (RFC 9112 §3.2, §6.1, §6.3; RFC 9110 §7.2) -/

#guard statusOf dflt "GET /where?q=now HTTP/1.1\r\nHost: www.example.org\r\n\r\n" = 200
-- `Host` missing, repeated, invalid
#guard statusOf dflt "GET / HTTP/1.1\r\n\r\n" = 400
#guard statusOf dflt "GET / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n" = 400
#guard statusOf dflt "GET / HTTP/1.1\r\nHost: a b\r\n\r\n" = 400
-- HTTP/1.0 without `Host` is acceptable
#guard statusOf dflt "GET / HTTP/1.0\r\n\r\n" = 200
-- an empty `Host` (a target without authority) is acceptable
#guard statusOf dflt "GET / HTTP/1.1\r\nHost:\r\n\r\n" = 200
-- version
#guard statusOf dflt "GET / HTTP/2.0\r\nHost: a\r\n\r\n" = 505
-- target forms: RFC 9112 §3.2.2 absolute-form, §3.2.3 authority-form, §3.2.4 asterisk-form
#guard statusOf dflt "GET http://www.example.org/pub/WWW/TheProject.html HTTP/1.1\r\nHost: www.example.org\r\n\r\n" = 200
#guard statusOf dflt "CONNECT www.example.com:80 HTTP/1.1\r\nHost: www.example.com\r\n\r\n" = 200
#guard statusOf dflt "OPTIONS * HTTP/1.1\r\nHost: www.example.org:8001\r\n\r\n" = 200
#guard statusOf dflt "CONNECT / HTTP/1.1\r\nHost: a\r\n\r\n" = 400
#guard statusOf dflt "GET * HTTP/1.1\r\nHost: a\r\n\r\n" = 400
#guard statusOf dflt "GET www.example.com:80 HTTP/1.1\r\nHost: a\r\n\r\n" = 400
-- framing and codings
#guard statusOf dflt "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip, chunked\r\n\r\n" = 501
#guard statusOf { dflt with implements := (· == gzipName) }
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip, chunked\r\n\r\n" = 200
#guard statusOf { dflt with implements := (· == gzipName) }
  "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: x-gzip, chunked\r\n\r\n" = 200
#guard statusOf dflt "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, chunked\r\n\r\n" = 400
#guard statusOf dflt "POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip\r\n\r\n" = 400
#guard statusOf dflt "POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n" = 400
#guard statusOf dflt "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 1, 2\r\n\r\n" = 400
#guard statusOf dflt "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 2, 2\r\n\r\n" = 200
-- both framing headers: the compliant `teWins` profile accepts and closes, `strict` rejects
#guard statusOf dflt "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\nTransfer-Encoding: chunked\r\n\r\n" = 200
#guard statusOf { dflt with profile := Profile.strict }
  "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\nTransfer-Encoding: chunked\r\n\r\n" = 400

/-! ## Persistence (RFC 9112 §9.3) -/

def persistsOf (s : String) : Option Bool :=
  (value? (parseRequestHead (b s))).bind fun h =>
    match checkRequest dflt h with
    | .ok c => some c.persistent
    | .error _ => none

#guard persistsOf "GET / HTTP/1.1\r\nHost: a\r\n\r\n" = some true
#guard persistsOf "GET / HTTP/1.1\r\nHost: a\r\nConnection: Close\r\n\r\n" = some false
#guard persistsOf "GET / HTTP/1.0\r\n\r\n" = some false
#guard persistsOf "GET / HTTP/1.0\r\nConnection: keep-alive\r\n\r\n" = some true
#guard persistsOf "POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\nTransfer-Encoding: chunked\r\n\r\n" = some false

/-! ## Hop-by-hop fields (RFC 9110 §7.6.1) -/

#guard (stripHopByHop [⟨ascii "Connection", ascii "close, X-Secret"⟩, ⟨ascii "x-secret", ascii "1"⟩,
    ⟨ascii "Keep-Alive", ascii "timeout=5"⟩, ⟨ascii "Accept", ascii "*/*"⟩,
    ⟨ascii "Transfer-Encoding", ascii "chunked"⟩]).map (·.name) = [ascii "Accept"]

/-! ## `TE` (RFC 9112 §10.1) -/

#guard teOffers [⟨ascii "TE", ascii "deflate"⟩] = [.coding (ascii "deflate") 1000]
#guard teOffers [⟨ascii "TE", ascii "trailers, deflate;q=0.5"⟩] =
  [.trailers, .coding (ascii "deflate") 500]
#guard teTrailers [⟨ascii "TE", ascii "trailers, deflate;q=0.5"⟩]
#guard !teAccepts [⟨ascii "TE", ascii "gzip;q=0"⟩] gzipName
#guard teAccepts [] chunkedName

/-! ## Profiles on the smuggling probes -/

#guard okAt (parseRequestWith Profile.clWins ⟨clteOctets.toArray⟩ 0) (clteOctets.length)
#guard okAt (parseRequestWith Profile.teWins ⟨clteOctets.toArray⟩ 0) (clteOctets.length - 1)
#guard isErr (parseRequestWith Profile.strict ⟨clteOctets.toArray⟩ 0)
#guard isErr (parseRequestWith Profile.teWins ⟨teteOctets.toArray⟩ 0)
#guard Profile.all.length = 108
#guard (Profile.all.filter fun p => decide p.Compliant).length = 2

/-! ## A pipelined connection -/

/-- A handler answering `200` with the request target as content. -/
def echoTarget : Handler := fun h _ _ =>
  (⟨⟨Version.http11, 200, ascii "OK"⟩,
    [⟨ascii "Content-Length", decDigits h.line.target.length⟩]⟩, .content h.line.target)

def pipelined : String :=
  "GET /a HTTP/1.1\r\nHost: x\r\n\r\n" ++
  "POST /b HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\n\r\nabc" ++
  "GET /c HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n" ++
  "GET /smuggled HTTP/1.1\r\nHost: x\r\n\r\n"

#guard (serve dflt echoTarget 10 (b pipelined) 0).1.map (·.request.line.target) =
  [ascii "/a", ascii "/b", ascii "/c"]
#guard (serve dflt echoTarget 10 (b pipelined) 0).2 = .closed
#guard serveOutput (serve dflt echoTarget 10 (b pipelined) 0) =
  ascii ("HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\n/a" ++
    "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\n/b" ++
    "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\n/c")
-- a rejected request ends the connection with an error response
#guard (serve dflt echoTarget 10 (b "GET / HTTP/1.1\r\n\r\nGET / HTTP/1.1\r\nHost: x\r\n\r\n") 0).2 =
  .rejected 400

/-! ## Interim responses (RFC 9110 §15.2) -/

def withInterim : String :=
  "HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 103 Early Hints\r\nLink: </s.css>\r\n\r\n" ++
  "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nhi"

#guard (value? (readResponse (ascii "GET") (b withInterim) 5 0)).map (fun r => (r.1.length, r.2.1.line.code)) =
  some (2, 200)
#guard okAt (readResponse (ascii "GET") (b withInterim) 5 0) withInterim.utf8ByteSize

end Silmaril.Net.Http1.ComplianceExamples

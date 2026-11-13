module

public import Silmaril.Net.Http1.Framing.Defs
public meta import Silmaril.Net.Http1.Framing.Defs

/-!
# HTTP/1.1 examples

Executable checks (`#guard`, evaluated when the module is built) of the HTTP/1.1 parsers
on the examples of RFC 9112 and RFC 9110 and on hand-written edge cases.
-/

@[expose] public section

namespace Silmaril.Net.Http1.Examples

open Silmaril.Parse.ByteParse

/-- The octets of a string. -/
def b (s : String) : ByteArray := s.toUTF8

/-- Did the parse succeed, consuming `n` octets? -/
def okAt {α : Type} (r : Res α) (n : Nat) : Bool :=
  match r with
  | .ok _ j => j == n
  | .err _ => false

def isErr {α : Type} (r : Res α) : Bool :=
  match r with
  | .ok _ _ => false
  | .err _ => true

def value? {α : Type} (r : Res α) : Option α :=
  match r with
  | .ok a _ => some a
  | .err _ => none

/-- RFC 9112 §3.2.1 (origin-form example) and RFC 9110 §7.2 (`Host`). -/
def get1 : String := "GET /where?q=now HTTP/1.1\r\nHost: www.example.org\r\n\r\n"

#guard okAt (parseRequestHead (b get1)) get1.utf8ByteSize
#guard (value? (parseRequestHead (b get1))).map (·.line.method) = some (ascii "GET")
#guard (value? (parseRequestHead (b get1))).map (·.line.target) = some (ascii "/where?q=now")
#guard (value? (parseRequestHead (b get1))).map (·.line.version) = some Version.http11
#guard (value? (parseRequestHead (b get1))).map (·.fields) =
  some [⟨ascii "Host", ascii "www.example.org"⟩]

/-- Optional whitespace around a value is dropped, inner whitespace kept (RFC 9112 §5). -/
def ows : String := "GET / HTTP/1.1\r\nX-A:\t  a  b \t\r\nX-B:\r\n\r\nbody"
#guard (value? (parseRequestHead (b ows))).map (·.fields) =
  some [⟨ascii "X-A", ascii "a  b"⟩, ⟨ascii "X-B", []⟩]
#guard okAt (parseRequestHead (b ows)) (ows.utf8ByteSize - 4)

/-- RFC 9112 §4 / RFC 9110 §15: a status line. -/
def resp : String := "HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
#guard okAt (parseResponseHead (b resp)) resp.utf8ByteSize
#guard (value? (parseResponseHead (b resp))).map (·.line.code) = some 200
#guard (value? (parseResponseHead (b resp))).map (·.line.reason) = some (ascii "OK")

-- An empty reason phrase still has its `SP` (RFC 9112 §4).
#guard okAt (parseResponseHead (b "HTTP/1.1 204 \r\n\r\n")) 17
#guard isErr (parseResponseHead (b "HTTP/1.1 204\r\n\r\n"))

-- Rejections: whitespace before the colon (RFC 9112 §5.1), bare `LF`, obs-fold (§5.2),
-- lowercase `HTTP-name` (`%s"HTTP"` is case-sensitive, §2.3), a space in the target.
#guard isErr (parseRequestHead (b "GET / HTTP/1.1\r\nHost : a\r\n\r\n"))
#guard isErr (parseRequestHead (b "GET / HTTP/1.1\nHost: a\n\n"))
#guard isErr (parseRequestHead (b "GET / HTTP/1.1\r\nX: a\r\n b\r\n\r\n"))
#guard isErr (parseRequestHead (b "GET / http/1.1\r\n\r\n"))
#guard isErr (parseRequestHead (b "GET /a b HTTP/1.1\r\n\r\n"))
#guard isErr (parseRequestHead (b "GET / HTTP/1.1\r\nHost: a\r\n"))

/-- Serializing and parsing again. -/
def h1 : RequestHead :=
  ⟨⟨ascii "POST", ascii "/upload", Version.http11⟩,
    [⟨ascii "Host", ascii "example.com"⟩, ⟨ascii "Transfer-Encoding", ascii "chunked"⟩]⟩
#guard decide h1.Valid
#guard value? (parseRequestHead ⟨(encRequestHead h1).toArray⟩) = some h1
#guard String.fromUTF8? ⟨(encRequestHead h1).toArray⟩ =
  some "POST /upload HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\n\r\n"

/-! ## Chunked bodies (RFC 9112 §7.1) -/

def chunked1 : String := "4\r\nWiki\r\n5\r\npedia\r\nE\r\n in\r\n\r\nchunks.\r\n0\r\n\r\n"
#guard okAt (parseChunked (b chunked1) 0) chunked1.utf8ByteSize
#guard (value? (parseChunked (b chunked1) 0)).map (·.content) =
  some (ascii "Wikipedia in\r\n\r\nchunks.")

-- extensions (token and quoted values, BWS) and trailers (§7.1.1, §7.1.2)
def chunked2 : String :=
  "5 ; a=b;c = \"d\\\"e\" ;f\r\nhello\r\n000;last\r\nExpires: never\r\nX-T: 1\r\n\r\nNEXT"
#guard okAt (parseChunked (b chunked2) 0) (chunked2.utf8ByteSize - 4)
#guard (value? (parseChunked (b chunked2) 0)).map (·.chunks.map (·.ext)) =
  some [ascii " ; a=b;c = \"d\\\"e\" ;f"]
#guard (value? (parseChunked (b chunked2) 0)).map (·.lastExt) = some (ascii ";last")
#guard (value? (parseChunked (b chunked2) 0)).map (·.trailers.length) = some 2

-- rejections: data longer than the size, missing last chunk, bad extensions
#guard isErr (parseChunked (b "3\r\nabcd\r\n0\r\n\r\n") 0)
#guard isErr (parseChunked (b "3\r\nabc\r\n") 0)
#guard isErr (parseChunked (b "3;\r\nabc\r\n0\r\n\r\n") 0)
#guard isErr (parseChunked (b "3;a=\r\nabc\r\n0\r\n\r\n") 0)
#guard isErr (parseChunked (b "3;a \r\nabc\r\n0\r\n\r\n") 0)
#guard isErr (parseChunked (b "3x\r\nabc\r\n0\r\n\r\n") 0)
#guard isErr (parseChunked (b "\r\nabc\r\n0\r\n\r\n") 0)

-- large sizes and leading zeros
#guard (value? (parseChunked (b "0001\r\nx\r\n0\r\n\r\n") 0)).map (·.content) = some (ascii "x")

def c1 : Chunked := ⟨[⟨ascii ";x=1", ascii "abc"⟩, ⟨[], ascii "de"⟩], [], [⟨ascii "T", ascii "v"⟩]⟩
#guard decide c1.Valid
#guard value? (parseChunked ⟨(encChunked c1).toArray⟩ 0) = some c1
#guard String.fromUTF8? ⟨(encChunked c1).toArray⟩ = some "3;x=1\r\nabc\r\n2\r\nde\r\n0\r\nT: v\r\n\r\n"

/-! ## Framing (RFC 9112 §6.3) -/

def fl (n v : String) : FieldLine := ⟨ascii n, ascii v⟩

#guard requestBodyLength [] = .none
#guard requestBodyLength [fl "Content-Length" "42"] = .length 42
#guard requestBodyLength [fl "content-length" "42, 42", fl "CONTENT-LENGTH" "42"] = .length 42
#guard requestBodyLength [fl "Content-Length" "42, 43"] = .invalid
#guard requestBodyLength [fl "Content-Length" "4x"] = .invalid
#guard requestBodyLength [fl "Content-Length" ""] = .none
-- Transfer-Encoding overrides Content-Length (rule 3), the request-smuggling case
#guard requestBodyLength [fl "Content-Length" "5", fl "Transfer-Encoding" "chunked"] = .chunked
#guard requestBodyLength [fl "Transfer-Encoding" "gzip, Chunked"] = .chunked
#guard requestBodyLength [fl "Transfer-Encoding" "gzip", fl "Transfer-Encoding" "chunked"] = .chunked
#guard requestBodyLength [fl "Transfer-Encoding" "chunked, gzip"] = .invalid
#guard responseBodyLength (ascii "GET") 200 [fl "Transfer-Encoding" "chunked, gzip"] = .close
#guard responseBodyLength (ascii "GET") 200 [] = .close
#guard responseBodyLength (ascii "HEAD") 200 [fl "Content-Length" "42"] = .none
#guard responseBodyLength (ascii "GET") 304 [fl "Content-Length" "42"] = .none
#guard responseBodyLength (ascii "GET") 101 [] = .none
#guard responseBodyLength (ascii "CONNECT") 200 [] = .tunnel
#guard responseBodyLength (ascii "CONNECT") 407 [fl "Content-Length" "3"] = .length 3

-- Two pipelined requests on one connection (RFC 9112 §9.3).
def pipe1 : String := "POST /a HTTP/1.1\r\nHost: h\r\nContent-Length: 5\r\n\r\nhello"
def pipe2 : String :=
  "POST /b HTTP/1.1\r\nHost: h\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n"
def pipe3 : String := "GET /c HTTP/1.1\r\nHost: h\r\n\r\n"
def pipe : String := pipe1 ++ pipe2 ++ pipe3
def pipeEnds : Option (List Nat) := do
  let .ok (_, b1) j1 := parseRequestAt (b pipe) 0 | none
  let .ok (_, b2) j2 := parseRequestAt (b pipe) j1 | none
  let .ok (_, b3) j3 := parseRequestAt (b pipe) j2 | none
  guard (b1.payload == ascii "hello" && b2.payload == ascii "abc" && b3 == .none)
  pure [j1, j2, j3]
#guard pipeEnds = some [pipe1.utf8ByteSize, (pipe1 ++ pipe2).utf8ByteSize, pipe.utf8ByteSize]

-- a response read until close, and one with an invalid length
#guard (value? (parseResponse (ascii "GET") (b "HTTP/1.0 200 OK\r\n\r\nall of it"))).map
  (·.2.payload) = some (ascii "all of it")
#guard isErr (parseResponse (ascii "GET") (b "HTTP/1.1 200 OK\r\nContent-Length: 1, 2\r\n\r\nx"))

/-! ## The chunk-ext automaton against a backtracking reading of the ABNF

A direct, nondeterministic transcription of RFC 9112 §7.1.1 (each function returns every
possible remainder after one production), compared with `isChunkExt` on every string of
length at most 6 over an alphabet that exercises every transition: an executable cross-check
of the proved `isChunkExt_iff_abnf` against an independent transcription. -/

namespace Abnf

/-- `BWS`: every remainder after zero or more `SP`/`HTAB`. -/
def ws : Bytes → List Bytes
  | [] => [[]]
  | c :: r => (c :: r) :: (if isWS c then ws r else [])

def lit (x : UInt8) : Bytes → List Bytes
  | c :: r => if c = x then [r] else []
  | [] => []

/-- `1*tchar`. -/
def token : Bytes → List Bytes
  | c :: r => if isTchar c then r :: token r else []
  | [] => []

/-- `*( qdtext / quoted-pair )`. -/
def qbody : Bytes → List Bytes
  | [] => [[]]
  | c :: r =>
    (c :: r) :: ((if isQdtext c then qbody r else []) ++
      (match r with
       | d :: r' => if c = BSLASH && isFieldByte d then qbody r' else []
       | [] => []))

def quoted (r : Bytes) : List Bytes := (lit DQUOTE r).flatMap fun r => (qbody r).flatMap (lit DQUOTE)

/-- One item `BWS ";" BWS name [ BWS "=" BWS value ]`. -/
def item (r : Bytes) : List Bytes :=
  ((((ws r).flatMap (lit SEMI)).flatMap ws).flatMap token).flatMap fun r =>
    r :: ((((ws r).flatMap (lit EQ)).flatMap ws).flatMap fun r => token r ++ quoted r)

/-- `*item`; each item consumes at least two octets. -/
def items : Nat → Bytes → List Bytes
  | 0, r => [r]
  | n + 1, r => r :: (item r).flatMap (items n)

def accepts (l : Bytes) : Bool := (items l.length l).contains []

/-- All strings of length `n` over `alpha`. -/
def strings (alpha : Bytes) : Nat → List Bytes
  | 0 => [[]]
  | n + 1 => (strings alpha n).flatMap fun s => alpha.map (· :: s)

def alpha : Bytes := [SP, SEMI, EQ, DQUOTE, BSLASH, 0x61]

end Abnf

#guard (List.range 7).all fun n => (Abnf.strings Abnf.alpha n).all fun l =>
  isChunkExt l == Abnf.accepts l
#guard Abnf.accepts (ascii " ; a=b;c = \"d\\\"e\" ;f")
#guard !Abnf.accepts (ascii ";a ")

end Silmaril.Net.Http1.Examples

module

public import Silmaril.Net.Http1.Codings.Defs

/-!
# HTTP/1.1 connection management (RFC 9112 §9, RFC 9110 §7.6.1, §7.8)

A connection carries a sequence of messages (RFC 9112 §9.3). Whether it stays open after a
response is decided from the `Connection` field, the protocol versions and the framing:

* **Connection options** (`connectionOptions`, RFC 9110 §7.6.1): the lowercase elements of
  `Connection`, a list of tokens (`close`, `keep-alive`, and the names of hop-by-hop fields).
* **Persistence** (`persists`, RFC 9112 §9.3), the ordered rules: `close` present → the
  connection closes; HTTP/1.1 or later → it persists; HTTP/1.0 with `keep-alive`, when the
  recipient is not a proxy (or the message is a response) and chooses to honour the
  HTTP/1.0 mechanism → it persists; otherwise it closes.
* **Faulty framing that forces closure** (`framingForcesClose`): a request with both
  `Transfer-Encoding` and `Content-Length` (§6.3 rule 3: "the server MUST close the
  connection after responding to such a request"), and an HTTP/1.0 message with
  `Transfer-Encoding` (§6.1: "MUST treat the message as if the framing is faulty … and
  close the connection after processing the message").
* **The server's decision** after a response (`keepOpen`, §9.3, §9.6): the request
  persists, neither side sent `close`, the request's framing does not force closure and the
  response is not delimited by closing the connection (§6.3 rule 8). A server that
  answers an upgrade with `101` switches the connection to another protocol (`switches`,
  RFC 9110 §7.8); this module does not follow it there.
* **Hop-by-hop fields** (`stripHopByHop`, RFC 9110 §7.6.1): an intermediary removes the
  `Connection` field, every field it names, and `Proxy-Connection`, `Keep-Alive`, `TE`,
  `Transfer-Encoding` and `Upgrade` before forwarding.
* **Option declarations** (§7.4, RFC 9110 §7.8): a sender of `TE` or `Upgrade` also lists it
  in `Connection` (`declaresHopByHop`).
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

/-- `connection`. -/
def connectionName : Bytes := ascii "connection"
/-- `close`. -/
def closeOption : Bytes := ascii "close"
/-- `keep-alive`. -/
def keepAliveOption : Bytes := ascii "keep-alive"
/-- `upgrade`. -/
def upgradeName : Bytes := ascii "upgrade"
/-- `host`. -/
def hostName : Bytes := ascii "host"

/-- The connection options (RFC 9110 §7.6.1), lowercase. -/
def connectionOptions (fs : List FieldLine) : List Bytes :=
  (fieldElements fs connectionName).map lower

/-- The `close` option is present (RFC 9112 §9.6). -/
def hasClose (fs : List FieldLine) : Bool := (connectionOptions fs).contains closeOption

/-- The version is HTTP/1.1 or later. -/
def Version.atLeast11 (v : Version) : Bool := v.major > 1 || (v.major == 1 && v.minor ≥ 1)

/-- The version is HTTP/1.0 (or an earlier 1.x, which does not exist). -/
def Version.is10 (v : Version) : Bool := v.major == 1 && v.minor == 0

/-- How the recipient treats the HTTP/1.0 `keep-alive` mechanism (RFC 9112 §9.3, Appendix
C.2.2): `honour` says it wants to honour it, `proxyRequest` that the recipient is a proxy
and the message a request (then `keep-alive` is not honoured). -/
structure KeepAlive where
  honour : Bool := true
  proxyRequest : Bool := false
  deriving DecidableEq, Repr

/-- RFC 9112 §9.3: does the connection persist after the current response, judging by the
received message with version `v` and fields `fs`? -/
def persists (ka : KeepAlive) (v : Version) (fs : List FieldLine) : Bool :=
  if hasClose fs then false
  else if v.atLeast11 then true
  else v.is10 && (connectionOptions fs).contains keepAliveOption && !ka.proxyRequest && ka.honour

/-- The framing of a received request is faulty in a way that obliges the server to close the
connection after responding (§6.1, §6.3 rule 3). -/
def framingForcesClose (v : Version) (fs : List FieldLine) : Bool :=
  !(transferCodings fs).isEmpty && (v.is10 || !(fieldElements fs contentLengthName).isEmpty)

/-- The server keeps the connection open after sending `resp` to `req` (§6.3, §9.3, §9.6). -/
def keepOpen (ka : KeepAlive) (req : RequestHead) (resp : ResponseHead) : Bool :=
  persists ka req.line.version req.fields && !hasClose resp.fields &&
    !framingForcesClose req.line.version req.fields &&
    responseBodyLength req.line.method resp.line.code resp.fields != .close &&
    resp.line.code != 101

/-- A `101 (Switching Protocols)` response switches the connection to the protocol named by
its `Upgrade` field (RFC 9110 §7.8, §15.2.2). -/
def switches (resp : ResponseHead) : Bool :=
  resp.line.code == 101 && !(fieldElements resp.fields upgradeName).isEmpty

/-! ## Hop-by-hop fields -/

/-- `Proxy-Connection`, `Keep-Alive`, `TE`, `Transfer-Encoding`, `Upgrade` and `Connection`
itself: the fields RFC 9110 §7.6.1 removes whether or not they are named. -/
def hopByHopNames : List Bytes :=
  [connectionName, ascii "proxy-connection", keepAliveOption, teName, transferEncodingName,
    upgradeName]

/-- A field name (any case) is hop-by-hop in a message with fields `fs`. -/
def isHopByHop (fs : List FieldLine) (n : Bytes) : Bool :=
  hopByHopNames.contains (lower n) || (connectionOptions fs).contains (lower n)

/-- The fields an intermediary forwards (RFC 9110 §7.6.1). -/
def stripHopByHop (fs : List FieldLine) : List FieldLine :=
  fs.filter fun f => !isHopByHop fs f.name

/-- Every field in `TE` and `Upgrade` is declared by a `Connection` option (§7.4, RFC 9110
§7.8: the sender "MUST also send" the option). -/
def declaresHopByHop (fs : List FieldLine) : Bool :=
  ((fieldValues fs teName).isEmpty || (connectionOptions fs).contains teName) &&
    ((fieldValues fs upgradeName).isEmpty || (connectionOptions fs).contains upgradeName)

end Silmaril.Net.Http1

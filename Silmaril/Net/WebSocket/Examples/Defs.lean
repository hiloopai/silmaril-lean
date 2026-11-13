module

public import Silmaril.Net.WebSocket.Handshake.Defs
public import Silmaril.Net.WebSocket.Message.Defs
public meta import Silmaril.Net.WebSocket.Handshake.Defs
public meta import Silmaril.Net.WebSocket.Message.Defs

/-!
# WebSocket end to end: octets → HTTP/1.1 head → handshake → frames

Executable checks (`#guard`, evaluated when the module is built) that compose the pieces
through their public APIs:

1. the client handshake of RFC 6455 §1.2, as octets, is parsed by the HTTP/1.1 parser
   (`Silmaril.Net.Http1.parseRequestHead`, RFC 9112) and read by `readOffer`;
2. the server's `respond` is serialized (`encResponseHead`), parsed back by the client, and
   accepted by `checkResponse` with the subprotocol `chat` selected (§1.2 offers `chat,
   superchat`);
3. the octets after the response head are frames: the masked `Hello` of RFC 6455 §5.7 is read
   by `decode` and delivered by the server's `Receiver`.

These are tests, not proofs: the kernel-checked facts are in the `Thms` modules
(`checkResponse_respond`, `readOffer_clientRequest`, `decode_encode`, `run_fragments`).
-/

@[expose] public section

namespace Silmaril.Net.WebSocket.Examples

open Silmaril.Net.WebSocket Silmaril.Net.WebSocket.Handshake
open Silmaril.Net.Http1 (parseRequestHead parseResponseHead encResponseHead Version ascii)
open Silmaril.Parse.ByteParse

/-- The client handshake of RFC 6455 §1.2. -/
def clientHello : String :=
  "GET /chat HTTP/1.1\r\nHost: server.example.com\r\nUpgrade: websocket\r\n" ++
  "Connection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n" ++
  "Origin: http://example.com\r\nSec-WebSocket-Protocol: chat, superchat\r\n" ++
  "Sec-WebSocket-Version: 13\r\n\r\n"

def value? {α : Type} : Res α → Option α
  | .ok a _ => some a
  | .err _ => none

/-- The server's reading of the handshake. -/
def offer? : Option Offer :=
  (value? (parseRequestHead clientHello.toUTF8)).bind fun h =>
    match readOffer h with
    | .ok o => some o
    | .error _ => none

#guard offer?.map (·.key) = some (ascii "dGhlIHNhbXBsZSBub25jZQ==")
#guard offer?.map (·.protocols) = some [ascii "chat", ascii "superchat"]
#guard offer?.map (·.target) = some (ascii "/chat")

/-- The server's response, as octets. -/
def serverHello : Option (List UInt8) :=
  offer?.map fun o => encResponseHead (respond o (some (ascii "chat")))

-- §1.2: the response the RFC shows.
#guard serverHello.map (fun b => String.fromUTF8? ⟨b.toArray⟩) = some (some
  ("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n" ++
   "Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=\r\nSec-WebSocket-Protocol: chat\r\n\r\n"))

/-- The client parses the response and checks it. -/
def clientResult : Option (Except HandshakeError (Option (List UInt8))) :=
  serverHello.bind fun b =>
    (value? (parseResponseHead ⟨b.toArray⟩)).map
      (checkResponse (ascii "dGhlIHNhbXBsZSBub25jZQ==") [ascii "chat", ascii "superchat"])

#guard match clientResult with
  | some (.ok (some p)) => p == ascii "chat"
  | _ => false

-- A forged accept value is refused.
#guard match checkResponse (ascii "dGhlIHNhbXBsZSBub25jZQ==") []
    ⟨⟨Version.http11, 101, []⟩, [⟨ascii "Upgrade", ascii "websocket"⟩,
      ⟨ascii "Connection", ascii "upgrade"⟩, ⟨ascii "Sec-WebSocket-Accept", ascii "AAAA"⟩]⟩ with
  | .error .accept => true
  | _ => false

/-- A handshake with `Sec-WebSocket-Version: 8` (§4.4). -/
def oldVersionHello : String :=
  "GET / HTTP/1.1\r\nHost: a\r\nUpgrade: websocket\r\nConnection: keep-alive, Upgrade\r\n" ++
  "Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 8\r\n\r\n"

#guard match (value? (parseRequestHead oldVersionHello.toUTF8)).map readOffer with
  | some (.error .wsVersion) => true
  | _ => false

-- After the handshake, the masked `Hello` of §5.7 arrives at the server.
#guard match decode 1024 [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58] with
  | .ok (f, []) => match Receiver.run .server {} [f] with
    | .ok (_, [.message op d]) => op == opText && d == ascii "Hello"
    | _ => false
  | _ => false

end Silmaril.Net.WebSocket.Examples

module

public import Silmaril.Net.WebSocket.Message.Defs
import Silmaril.Proofs.Net.WebSocket.Message

@[expose] public section

/-!
# WebSocket messages: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/WebSocket/Message.lean`):

* `run_fragments`: **any fragmentation is transparent** (RFC 6455 §5.4). For every chunking of
  a text or binary message and every key supply that respects the masking direction (§5.1),
  the receiver delivers exactly one message, the concatenation of the chunks, and ends with no
  message in progress. For text, the hypothesis is that the whole message is UTF-8 (§8.1), not
  each chunk.
* `run_filter_keepalive`: **control frames injected between fragments do not change the data
  messages** (§5.4: "Control frames … MAY be injected in the middle of a fragmented message").
  Removing every acceptable ping and pong from any frame sequence changes neither the final
  state, nor the data messages delivered, nor whether the connection fails.

CHECKED (`rfl`): the §5.7 fragmented example with an injected ping; rejections.
-/

namespace Silmaril.Net.WebSocket

theorem run_fragments (role : Role) (keys : Nat → Option MaskKey) (hk : KeysFor role.peer keys)
    (op : Nat) (hop : op = opText ∨ op = opBinary) (chunks : List (List UInt8))
    (hu : op = opText → isUtf8 chunks.flatten = true) :
    Receiver.run role {} (fragments keys op chunks) = .ok ({}, [.message op chunks.flatten]) :=
  Silmaril.Proofs.Net.WebSocket.run_fragments role keys hk op hop chunks hu

theorem run_filter_keepalive (role : Role) (r : Receiver) (fs : List Frame) :
    (r.run role fs).map (fun p => (p.1, dataOnly p.2)) =
      (r.run role (fs.filter fun f => !f.isKeepalive role)).map
        (fun p => (p.1, dataOnly p.2)) :=
  Silmaril.Proofs.Net.WebSocket.run_filter_keepalive role r fs

/-! ## Examples -/

/-- The §5.7 fragmented text message `Hel` + `lo`, sent by a server, with an unmasked ping
injected between the fragments, as a client receives it. -/
example : Receiver.run .client {}
    [⟨false, 0, opText, none, [0x48, 0x65, 0x6c]⟩, ⟨true, 0, opPing, none, []⟩,
     ⟨true, 0, opContinuation, none, [0x6c, 0x6f]⟩] =
    .ok ({}, [.ping [], .message opText [0x48, 0x65, 0x6c, 0x6c, 0x6f]]) := by
  rfl

/-- A client receiving a masked frame fails the connection (§5.1). -/
example : Receiver.run .client {} [⟨true, 0, opText, some ⟨1, 2, 3, 4⟩, []⟩] = .error .masking := by
  rfl

/-- A server receiving an unmasked frame fails the connection (§5.1). -/
example : Receiver.run .server {} [⟨true, 0, opText, none, []⟩] = .error .masking := by rfl

/-- A fragmented ping is rejected (§5.5). -/
example : Receiver.run .client {} [⟨false, 0, opPing, none, []⟩] = .error .controlFrame := by rfl

/-- A continuation with nothing to continue (§5.4). -/
example : Receiver.run .client {} [⟨true, 0, opContinuation, none, []⟩] =
    .error .unexpectedContinuation := by
  rfl

/-- A new message while one is in progress (§5.4). -/
example : Receiver.run .client {} [⟨false, 0, opText, none, []⟩, ⟨true, 0, opBinary, none, []⟩] =
    .error .interleaved := by
  rfl

/-- The two octets of `é` (U+00E9) split across fragments are accepted (§5.6), but a lone
continuation octet in a text message fails the connection (§8.1, status 1007). -/
example : Receiver.run .client {}
    [⟨false, 0, opText, none, [0xc3]⟩, ⟨true, 0, opContinuation, none, [0xa9]⟩] =
    .ok ({}, [.message opText [0xc3, 0xa9]]) := by
  rfl

example : Receiver.run .client {} [⟨true, 0, opText, none, [0xa9]⟩] = .error .invalidUtf8 := by
  rfl

/-- An RSV bit without an extension (§5.2). -/
example : Receiver.run .client {} [⟨true, 4, opText, none, []⟩] = .error .reservedBits := by rfl

end Silmaril.Net.WebSocket

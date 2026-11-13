module

public import Silmaril.Net.Quic.Error.Defs

@[expose] public section

/-!
# QUIC flow control (RFC 9000 §4.1, §4.2, §4.5)

"QUIC employs a limit-based flow control scheme where a receiver advertises the limit of total
bytes it is prepared to receive on a given stream or for the entire connection" (§4.1). Both
limits are absolute: "A MAX_STREAM_DATA frame indicates the maximum absolute byte offset of a
stream", and MAX_DATA "indicates the maximum of the sum of the absolute byte offsets of all
streams".

**Sender (`Credit`, `SendFlow`).** A `Credit` is a limit received from the peer and the amount
`used` against it. "Senders MUST NOT send data in excess of either limit": `SendFlow.send id n`
sends `n` new bytes on stream `id` only if both the stream credit and the connection credit
allow it. "A sender MUST ignore any MAX_STREAM_DATA or MAX_DATA frames that do not increase
flow control limits": `Credit.onMax` takes the maximum. "If a sender has sent data up to the
limit, it will be unable to send new data and is considered blocked" (`Credit.blocked`; it
then SHOULD send DATA_BLOCKED / STREAM_DATA_BLOCKED with the limit).

**Receiver (`RecvFlow`).** "A receiver maintains a cumulative sum of bytes received on all
streams, which is used to check for violations of the advertised connection or stream data
limits": `received` is the sum of the per-stream `highest` offsets. `RecvFlow.onData id e`
accounts for data (or a final size) reaching offset `e` on stream `id`; "A receiver MUST close
the connection with an error of type FLOW_CONTROL_ERROR if the sender violates the advertised
connection or stream data limits". Loss and reordering mean an offset may arrive below one
already seen; only the increase of the highest offset is new credit ("When counting data toward
this limit, an endpoint accounts for the largest received offset of data that is sent or
received on the stream", §19.10). For a reset stream the caller passes the final size, since
"The receiver MUST use the final size of the stream to account for all bytes sent on the
stream in its connection-level flow controller" (§4.5). `RecvFlow.raise*` advertise new limits;
"it is not an error to advertise a smaller limit, but the smaller limit has no effect".

`Sync snd rcv` relates a sender to the receiver when every byte sent has arrived and every limit
the sender knows was advertised by the receiver (MAX_* frames may still be in flight or
reordered: the sender's limits are at most the receiver's). `Silmaril.Net.Quic.Flow.Thms`
proves that a sender respecting its credit never causes FLOW_CONTROL_ERROR.

Not modelled: *when* to send MAX_* frames (§4.2 autotuning), CRYPTO data (not flow
controlled, §4), and the initial limits from transport parameters (§7.4, §18.2), which are
just the starting `limit`s. Stream counts (MAX_STREAMS) are in `Silmaril.Net.Quic.StreamId`.
-/

namespace Silmaril.Net.Quic

/-- One flow-control limit as seen by the sender. -/
structure Credit where
  /-- The largest limit received (initial transport parameter or MAX_* frame). -/
  limit : Nat
  /-- Bytes sent against it (stream: highest offset; connection: sum over streams). -/
  used : Nat := 0
  deriving DecidableEq, Repr

namespace Credit

/-- The bytes that may still be sent. -/
def available (c : Credit) : Nat := c.limit - c.used

/-- Use `n` more bytes, if the limit allows it. -/
def consume (c : Credit) (n : Nat) : Option Credit :=
  if c.used + n ≤ c.limit then some { c with used := c.used + n } else none

/-- Receive MAX_DATA / MAX_STREAM_DATA: smaller values are ignored. -/
def onMax (c : Credit) (m : Nat) : Credit := { c with limit := max c.limit m }

/-- Blocked: sent up to the limit. -/
def blocked (c : Credit) : Bool := c.limit ≤ c.used

/-- The limit is respected. -/
def Ok (c : Credit) : Prop := c.used ≤ c.limit

end Credit

/-- Update a function at one point. -/
def update {α : Type} (f : Nat → α) (i : Nat) (a : α) : Nat → α := fun j => if j = i then a else f j

/-- The sender's flow-control state: the connection credit and one credit per stream. -/
structure SendFlow where
  conn : Credit
  streams : Nat → Credit

namespace SendFlow

/-- Send `n` new bytes on stream `id`, if both limits allow it (§4.1). -/
def send (f : SendFlow) (id n : Nat) : Option SendFlow := do
  let c ← f.conn.consume n
  let s ← (f.streams id).consume n
  pure { conn := c, streams := update f.streams id s }

/-- Receive MAX_DATA. -/
def onMaxData (f : SendFlow) (m : Nat) : SendFlow := { f with conn := f.conn.onMax m }

/-- Receive MAX_STREAM_DATA for stream `id`. -/
def onMaxStreamData (f : SendFlow) (id m : Nat) : SendFlow :=
  { f with streams := update f.streams id ((f.streams id).onMax m) }

/-- Every limit is respected. -/
def Ok (f : SendFlow) : Prop := f.conn.Ok ∧ ∀ id, (f.streams id).Ok

end SendFlow

/-- The receiver's flow-control state. -/
structure RecvFlow where
  /-- The connection limit advertised (MAX_DATA). -/
  maxData : Nat
  /-- The sum of the highest offsets of all streams. -/
  received : Nat := 0
  /-- The stream limits advertised (MAX_STREAM_DATA). -/
  streamMax : Nat → Nat
  /-- The highest offset received on each stream. -/
  highest : Nat → Nat := fun _ => 0

namespace RecvFlow

/-- Data (or a final size) reaching offset `e` on stream `id`: FLOW_CONTROL_ERROR beyond the
stream limit or when the new credit exceeds the connection limit (§4.1). -/
def onData (f : RecvFlow) (id e : Nat) : Except TransportError RecvFlow :=
  if f.streamMax id < e then .error .flowControlError
  else
    let inc := e - f.highest id
    if f.maxData < f.received + inc then .error .flowControlError
    else .ok { f with received := f.received + inc,
                      highest := update f.highest id (max (f.highest id) e) }

/-- Advertise a connection limit (MAX_DATA); a smaller one has no effect. -/
def raiseMaxData (f : RecvFlow) (m : Nat) : RecvFlow := { f with maxData := max f.maxData m }

/-- Advertise a stream limit (MAX_STREAM_DATA); a smaller one has no effect. -/
def raiseStreamMax (f : RecvFlow) (id m : Nat) : RecvFlow :=
  { f with streamMax := update f.streamMax id (max (f.streamMax id) m) }

/-- Every limit is respected. -/
def Ok (f : RecvFlow) : Prop := f.received ≤ f.maxData ∧ ∀ id, f.highest id ≤ f.streamMax id

end RecvFlow

/-- The sender's view agrees with the receiver: the data sent arrived, and the sender's
limits were advertised by the receiver (they may lag behind). -/
def Sync (snd : SendFlow) (rcv : RecvFlow) : Prop :=
  snd.conn.used = rcv.received ∧ snd.conn.limit ≤ rcv.maxData ∧
    ∀ id, (snd.streams id).used = rcv.highest id ∧ (snd.streams id).limit ≤ rcv.streamMax id

end Silmaril.Net.Quic

module

/-!
# Channels: the datagram service of the Internet layer

The Internet Protocol is a best-effort datagram service: "There are no mechanisms to augment
end-to-end data reliability, flow control, sequencing, or other services commonly found in
host-to-host protocols" (RFC 791 §1.2), and UDP adds none: "delivery and duplicate protection
are not guaranteed" (RFC 768, "Introduction"). TCP is specified to work over exactly this:
"TCP assumes it can obtain a simple, potentially unreliable datagram service from the lower
level protocols" (RFC 9293 §2.2 and §3.8, segments may be lost, duplicated, delayed or
reordered).

* `Ev α`: a channel event, `send m` or `recv m`, for messages `m : α`.
* **`Loose tr`**: the *loose channel*: every message received was sent before. Nothing else
  is promised: messages may be lost (never received), duplicated (received more than once) and
  reordered. Messages are never altered or merged: each receive carries one whole sent
  message (datagram boundaries are kept). `okFrom seen tr` is the same with the messages
  `seen` already in flight.
* `Fifo tr`: a reliable FIFO channel (each receive is the oldest message not yet received), the
  strongest service; `Channel.Thms.fifo_loose` proves it is an instance of `Loose`.
* `liftT dec tr`: the trace seen through a partial decoder `dec : β → Option α` (a layer above:
  undecodable messages are dropped, as UDP drops datagrams whose checksum fails).
  `Channel.Thms.loose_liftT`: a layer above a loose channel sees a loose channel.

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`). The channel is a trace predicate on one
direction between two endpoints; a network of endpoints is a family of channels.
-/

@[expose] public section

namespace Silmaril.Net.Channel

/-- **A channel event**: a message is sent into the channel, or received from it. -/
inductive Ev (α : Type) where
  | send (m : α)
  | recv (m : α)
  deriving DecidableEq, Repr

variable {α β : Type}

/-- The messages sent in a trace, in order. -/
def sent : List (Ev α) → List α
  | [] => []
  | .send m :: t => m :: sent t
  | .recv _ :: t => sent t

/-- The messages received in a trace, in order. -/
def received : List (Ev α) → List α
  | [] => []
  | .send _ :: t => received t
  | .recv m :: t => m :: received t

/-- Every receive of `tr` is of a message in `seen` or sent earlier in `tr`. -/
def okFrom : List α → List (Ev α) → Prop
  | _, [] => True
  | seen, .send m :: t => okFrom (m :: seen) t
  | seen, .recv m :: t => m ∈ seen ∧ okFrom seen t

/-- **The loose channel**: every message received was sent before; loss, duplication and
reordering are allowed, alteration is not (RFC 791 §1.2, RFC 768, RFC 9293 §3.8). -/
def Loose (tr : List (Ev α)) : Prop := okFrom [] tr

/-- A FIFO queue of messages in flight: each receive takes the oldest one. -/
def fifoFrom : List α → List (Ev α) → Prop
  | _, [] => True
  | q, .send m :: t => fifoFrom (q ++ [m]) t
  | q, .recv m :: t => q.head? = some m ∧ fifoFrom q.tail t

/-- **A reliable FIFO channel**: messages are received in the order sent, each at most once. -/
def Fifo (tr : List (Ev α)) : Prop := fifoFrom [] tr

/-- An event seen through a partial decoder. -/
def Ev.lift (dec : β → Option α) : Ev β → Option (Ev α)
  | .send b => (dec b).map .send
  | .recv b => (dec b).map .recv

/-- A trace seen through a partial decoder: undecodable messages are dropped. -/
def liftT (dec : β → Option α) (tr : List (Ev β)) : List (Ev α) := tr.filterMap (Ev.lift dec)

/-- An event with its message transformed. -/
def Ev.map (f : β → α) : Ev β → Ev α
  | .send b => .send (f b)
  | .recv b => .recv (f b)

end Silmaril.Net.Channel

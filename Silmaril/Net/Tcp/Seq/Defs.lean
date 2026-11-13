module

/-!
# TCP sequence numbers (RFC 9293 §3.4)

"The actual sequence number space is finite, though large. This space ranges from 0 to
2^32 - 1. Since the space is finite, all arithmetic dealing with sequence numbers must be
performed modulo 2^32" (RFC 9293 §3.4). `SeqNum` is `UInt32`, whose `+` and `-` are exactly
arithmetic modulo 2^32.

* `off a b`: how far `b` lies ahead of `a`, going forward around the circle (`(b - a) mod 2^32`).
* `adv a n`: `a` advanced by `n` octets (`SEG.SEQ + SEG.LEN`, `RCV.NXT + RCV.WND`, …).
* `lt a b`, `le a b`: RFC 9293's `<` and `=<` "modulo 2^32", read as serial-number comparison:
  `b` lies strictly (resp. weakly) less than half the space ahead of `a`. RFC 9293 leaves the
  reading to the implementer ("great care should be taken in programming the comparison");
  this is the usual one. `Tcp.Seq.Thms.lt_not_trans`: it is not transitive.
* `inWindow lo wnd x`: `lo =< x < lo + wnd`, read on offsets: `off lo x < wnd`.
* `acceptableAck una nxt ack`: "SND.UNA < SEG.ACK =< SND.NXT" (§3.4), read on offsets from
  `SND.UNA`; `Tcp.Seq.Thms.acceptableAck_iff` relates it to `lt`/`le` when less than half the
  space is outstanding.
* `segAcceptable rcvNxt rcvWnd seq len`: the four cases of Table 5, "Segment Acceptability
  Tests" (§3.4).

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Tcp

/-- **A sequence number**: 32 bits, arithmetic modulo 2^32 (RFC 9293 §3.4). -/
abbrev SeqNum : Type := UInt32

namespace SeqNum

/-- How far `b` lies ahead of `a`, modulo 2^32. -/
def off (a b : SeqNum) : Nat := (b - a).toNat

/-- `a` advanced by `n`, modulo 2^32. -/
def adv (a : SeqNum) (n : Nat) : SeqNum := a + UInt32.ofNat n

/-- RFC 9293's `a < b` modulo 2^32: `b` is strictly less than half the space ahead of `a`. -/
def lt (a b : SeqNum) : Prop := 0 < off a b ∧ off a b < 2 ^ 31

/-- RFC 9293's `a =< b` modulo 2^32. -/
def le (a b : SeqNum) : Prop := off a b < 2 ^ 31

instance (a b : SeqNum) : Decidable (lt a b) := by unfold lt; infer_instance
instance (a b : SeqNum) : Decidable (le a b) := by unfold le; infer_instance

/-- `lo =< x < lo + wnd` (RFC 9293 §3.4), on offsets. -/
def inWindow (lo : SeqNum) (wnd : Nat) (x : SeqNum) : Bool := decide (off lo x < wnd)

/-- **An acceptable ack**, "SND.UNA < SEG.ACK =< SND.NXT" (RFC 9293 §3.4), on offsets from
`SND.UNA`. -/
def acceptableAck (una nxt ack : SeqNum) : Bool := decide (0 < off una ack ∧ off una ack ≤ off una nxt)

/-- **Table 5 of RFC 9293 §3.4**, the acceptability of an incoming segment occupying `len`
sequence numbers from `seq`, for the receive window `rcvNxt`, `rcvWnd`. -/
def segAcceptable (rcvNxt : SeqNum) (rcvWnd : Nat) (seq : SeqNum) (len : Nat) : Bool :=
  if len = 0 then
    if rcvWnd = 0 then seq == rcvNxt else inWindow rcvNxt rcvWnd seq
  else
    if rcvWnd = 0 then false
    else inWindow rcvNxt rcvWnd seq || inWindow rcvNxt rcvWnd (adv seq (len - 1))

end SeqNum

end Silmaril.Net.Tcp

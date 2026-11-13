module

public import Silmaril.Wasi.Versions.Net3.Defs
public import Silmaril.Wasi.Versions.P3.Defs

@[expose] public section

/-!
# WASI 0.3 TCP `send` and `receive` streams: a loose theory and a host

In 0.3 (`vendor/wasi/0.3.2/sockets/types.wit`, resource `tcp-socket`) data moves through
Component Model streams:

```
send: func(data: stream<u8>) -> future<result<_, error-code>>;
receive: func() -> tuple<stream<u8>, future<result<_, error-code>>>;
```

* `send`: "This function may be called at most once and returns once the full contents of the
  stream are transmitted or an error is encountered." The caller writes into the writable end
  of the stream it passed and drops it to close.
* `receive`: "Returns a `stream` of data sent by the peer. The implementation drops the stream
  once no more data is available." … "`receive` may be called only once per socket.
  Subsequent calls return a closed stream and a future resolved to `err(invalid-state)`."

**The theory** `tcp3sTh D` is relative to the data `D : Val → List (BitVec 8)` each remote
address sends on a connection before it shuts down (a peer model, as `SockMore.Conn` for
`accept`). Its state records the sockets connected by `connect` (answered `ok`) with their
remote address, the sockets that have called `send` and `receive`, the stream pairs created
with `stream.new`, and the dropped writable ends. It checks:

* a `stream.read` on the stream of the first `receive` of a connected socket to `addr` that
  completes with `k` bytes needs them to be the next `k` bytes of `D addr`; one that reports
  `DROPPED` needs all of `D addr` delivered. On the stream of a later `receive` nothing is
  pending: a completed read must carry no bytes;
* a `future.read` of the future of a `send` that completes with `ok` needs the writable end of
  the stream to be dropped (the full contents are known) and the `send` to be the socket's
  first.

Blocked and cancelled reads, errors, traps and other functions are not constrained; what the
peer receives from `send` is not observable by the component and is not stated here.

**The host** `tcp3sImpl D`: `connect` succeeds, `stream.new` and `receive` answer fresh
handles, `stream.write` completes in full, a `stream.read` on a receive stream delivers one
byte (none if asked for none) and `DROPPED` when none is left, and a `future.read` of a send
future answers `ok` once the writable end is dropped and the send was the first, `BLOCKED`
before the drop, and `err(invalid-state)` for a later `send`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Tcp3Stream

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult packCopy)
open Silmaril.Wasi.Versions.Net (gated lookup)
open Silmaril.Wasi.Versions.P3 (natV natOf copyOf cStreamNew cStreamWrite cStreamRead
  cStreamDropW cFutureRead)

/-! ## Names -/

def tcpSend3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.send"⟩
def tcpReceive3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.receive"⟩

/-- The data each remote address sends on a connection. -/
abbrev PeerData : Type := Val → List (BitVec 8)

/-! ## The state -/

/-- The value of `k` in an association list keyed by numbers. -/
def nlook {α : Type} (k : Nat) (l : List (Nat × α)) : Option α :=
  (l.find? (·.1 == k)).map (·.2)

/-- The theory state. -/
structure T3St where
  /-- Connected sockets with their remote address. -/
  conn : List (BitVec 32 × Val) := []
  /-- Sockets that called `receive`. -/
  recvd : List (BitVec 32) := []
  /-- Sockets that called `send`. -/
  sent : List (BitVec 32) := []
  /-- Stream pairs (readable, writable). -/
  pairs : List (Nat × Nat) := []
  /-- Dropped writable ends. -/
  dropped : List Nat := []
  /-- The bytes still to deliver on each receive stream. -/
  pend : List (Nat × List (BitVec 8)) := []
  /-- The send futures: the writable end, and whether the send was the socket's first. -/
  futs : List (Nat × (Nat × Bool)) := []

/-- The next state. -/
def t3Next (D : PeerData) (q : T3St) : WEv → T3St
  | .imp f a r =>
    if f = Silmaril.Wasi.Versions.Net.connect3 then
      (match a, r with
       | .u32 s :: addr :: _, some [.variant 0 none] => { q with conn := (s, addr) :: q.conn }
       | _, _ => q)
    else if f = tcpReceive3 then
      (match a, r with
       | .u32 s :: _, some [.record [rv, _]] =>
         (match natOf rv with
          | some r' =>
            let bs := if q.recvd.contains s then [] else ((lookup s q.conn).map D).getD []
            { q with recvd := s :: q.recvd, pend := (r', bs) :: q.pend }
          | none => q)
       | _, _ => q)
    else if f = tcpSend3 then
      (match a, r with
       | .u32 s :: rv :: _, some [fv] =>
         (match (natOf rv).bind (nlook · q.pairs), natOf fv with
          | some w, some f' =>
            { q with sent := s :: q.sent, futs := (f', (w, !q.sent.contains s)) :: q.futs }
          | _, _ => { q with sent := s :: q.sent })
       | _, _ => q)
    else if f = cStreamNew then
      (match r with
       | some [rv, wv] => (match natOf rv, natOf wv with
         | some r', some w' => { q with pairs := (r', w') :: q.pairs }
         | _, _ => q)
       | _ => q)
    else if f = cStreamDropW then
      (match a with
       | [wv] => { q with dropped := (natOf wv).toList ++ q.dropped }
       | _ => q)
    else if f = cStreamRead then
      (match a, r with
       | rv :: _, some [pv, _] =>
         (match natOf rv, (natOf pv).bind copyOf with
          | some r', some (some (.completed, k)) =>
            (match nlook r' q.pend with
             | some l => { q with pend := (r', l.drop k) :: q.pend }
             | none => q)
          | _, _ => q)
       | _, _ => q)
    else q
  | _ => q

/-! ## The checks -/

/-- The check of a `stream.read` answer with the pending bytes `l`. -/
def rdChk (l : List (BitVec 8)) : Option (List Val) → Bool
  | some [pv, items] =>
    (match (natOf pv).bind copyOf with
     | some (some (.completed, k)) => decide (k ≤ l.length) && bytesOf items == l.take k
     | some (some (.dropped, _)) => l.isEmpty
     | _ => true)
  | _ => true

/-- A send future is done: dropped writable end, first send. -/
def sendDone (q : T3St) (x : Nat × Bool) : Bool := q.dropped.contains x.1 && x.2

/-- The pending bytes of the stream read in `a`. -/
def pendOf (q : T3St) (a : List Val) : Option (List (BitVec 8)) :=
  match a with
  | rv :: _ => (natOf rv).bind (nlook · q.pend)
  | [] => none

/-- The send future read in `a`. -/
def futOf (q : T3St) (a : List Val) : Option (Nat × Bool) :=
  match a with
  | [fv] => (natOf fv).bind (nlook · q.futs)
  | _ => none

/-- The check of every answer. -/
def t3Ok (q : T3St) : WEv → Bool
  | .imp f a r =>
    if f = cStreamRead then
      (match pendOf q a with
       | some l => rdChk l r
       | none => true)
    else if f = cFutureRead then
      (match futOf q a, r with
       | some x, some [_, .variant 0 none] => sendDone q x
       | _, _ => true)
    else true
  | _ => true

/-- **The 0.3 TCP stream theory** of the peer data `D`. -/
def tcp3sTh (D : PeerData) : Protocol T3St WEv := gated {} (t3Next D) t3Ok

/-! ## The host -/

/-- The state after the answers `p`. -/
def t3State (D : PeerData) (p : List WEv) : T3St := p.foldl (t3Next D) {}

/-- The answer of a `stream.read` with the pending bytes `l`, asking for `n`. -/
def rdA (l : List (BitVec 8)) (n : Option Nat) : Option (List Val) :=
  if l.isEmpty then some [natV (packCopy .dropped 0), .record []]
  else
    let k := if n = some 0 then 0 else 1
    some [natV (packCopy .completed k), bytesV (l.take k)]

/-- 0.3 `error-code.invalid-state`. -/
abbrev eInvalidSt3 : Nat := 5

/-- The answer of a `future.read` of a send future. -/
def futA (q : T3St) (x : Nat × Bool) : Option (List Val) :=
  if sendDone q x then some [natV CopyResult.completed.toNat, .variant 0 none]
  else if x.2 then some [natV Silmaril.Wasm.Component.Async.blocked, .record []]
  else some [natV CopyResult.completed.toNat,
    .variant 1 (some (Silmaril.Wasi.Versions.Net.ecV3 eInvalidSt3))]

/-- **The concrete 0.3 TCP stream host** of the peer data `D`. -/
def tcp3sImpl (D : PeerData) : Impl := fun p f a =>
  let q := t3State D p
  if f = Silmaril.Wasi.Versions.Net.connect3 then some [.variant 0 none]
  else if f = cStreamNew then some [natV (2 * p.length + 1), natV (2 * p.length + 2)]
  else if f = tcpReceive3 then some [.record [natV (2 * p.length + 1), natV (2 * p.length + 2)]]
  else if f = tcpSend3 then some [natV (2 * p.length + 1)]
  else if f = cStreamWrite then
    some [natV (packCopy .completed (bytesOf (a.getD 1 (.record []))).length)]
  else if f = cStreamDropW then some []
  else if f = cStreamRead then
    (match pendOf q a with
     | some l => rdA l (a[1]?.bind natOf)
     | none => none)
  else if f = cFutureRead then
    (match futOf q a with
     | some x => futA q x
     | none => none)
  else none

end Silmaril.Wasi.Versions.Tcp3Stream

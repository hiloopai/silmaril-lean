module

public import Silmaril.Wasi.Versions.SockMore.Defs
public import Silmaril.Wasi.Versions.P3.Defs

@[expose] public section

/-!
# WASI 0.3 `listen`/accept through a `stream<tcp-socket>`: a loose theory and a host

In 0.3 (`vendor/wasi/0.3.2/sockets/types.wit`, resource `tcp-socket`) there is no `accept`:
`bind: func(local-address: ip-socket-address) -> result<_, error-code>` binds,
`listen: func() -> result<stream<tcp-socket>, error-code>` answers the readable end of a stream,
and accepted connections are the `tcp-socket` handles read from it with the Component Model
built-in `stream.read` (`$root` `stream.read(stream, count)`, answered with the packed copy result
and the items, as in `Silmaril.Wasi.Versions.P3`). `get-remote-address` names the peer.

* **The theory** `acc3Th P` over peers `P` (`NetMore.Peers`, as for the 0.2 `acceptTh P`): a
  `stream.read` on the stream of a socket listening at `local` that completes with at least one
  socket needs some peer to connect at `local`; each socket read is recorded as accepted at
  `local`, and its `get-remote-address` answered `ok(a)` needs `a` to be a peer of `local`.
  Blocked, dropped or empty reads are not constrained.
* **The host** `acc3Impl C` over connections `C` (`SockMore.Conn`): `bind` succeeds, `listen`
  answers a fresh stream, a `stream.read` of `n ≥ 1` items on a listening stream whose address has
  a connection completes with one fresh socket and is `BLOCKED` otherwise, and
  `get-remote-address` answers the peer (`error(invalid-state)` when there is none).

The adapters between this and the 0.2 `accept` (both directions) are not stated.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Accept3

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult)
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.P3 (natOf natV copyOf cStreamRead)
open Silmaril.Wasi.Versions.SockMore (Conn ConnOk)

def tcpBind3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.bind"⟩
def tcpListen3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.listen"⟩
def tcpRemote3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.get-remote-address"⟩

/-- The state: bound sockets, listening streams and accepted sockets, with their local address. -/
structure Acc3St where
  bound : List (BitVec 32 × Val) := []
  lst : List (BitVec 32 × Val) := []
  acc : List (BitVec 32 × Val) := []

/-- The number of completed items of a packed copy result. -/
def completedOf (pv : Val) : Option Nat :=
  match natOf pv with
  | some m => (match copyOf m with
    | some (some (.completed, k)) => some k
    | _ => none)
  | none => none

/-- The handles of a list of `tcp-socket`s. -/
def handlesOf : Val → List (BitVec 32)
  | .record vs => vs.filterMap fun | .u32 h => some h | _ => none
  | _ => []

/-- The next state. -/
def acc3Next (q : Acc3St) : WEv → Acc3St
  | .imp f (.u32 s :: rest) r =>
    if f = tcpBind3 then
      (match rest, r with
       | addr :: _, some [.variant 0 none] => { q with bound := (s, addr) :: q.bound }
       | _, _ => q)
    else if f = tcpListen3 then
      (match lookup s q.bound, r with
       | some addr, some [.variant 0 (some (.u32 st))] => { q with lst := (st, addr) :: q.lst }
       | _, _ => q)
    else if f = cStreamRead then
      (match lookup s q.lst, r with
       | some addr, some [pv, items] =>
         if (completedOf pv).isSome then
           { q with acc := (handlesOf items).map (fun c => (c, addr)) ++ q.acc }
         else q
       | _, _ => q)
    else q
  | _ => q

/-- The check of a `stream.read` answer on a stream listening at an address with `c` (some peer
connects). -/
def readChk (c : Bool) : Option (List Val) → Bool
  | some [pv, _] => (match completedOf pv with
    | some k => k == 0 || c
    | none => true)
  | _ => true

/-- The check of every answer. -/
def acc3Ok (P : Peers) (q : Acc3St) : WEv → Bool
  | .imp f (.u32 s :: _) r =>
    if f = cStreamRead then
      (match lookup s q.lst with
       | some addr => readChk (P.connects addr) r
       | none => true)
    else if f = tcpRemote3 then
      (match lookup s q.acc with
       | some addr => remoteOk (P.peer addr) r
       | none => true)
    else true
  | _ => true

/-- **The 0.3 listen/accept theory** of the peers `P`. -/
def acc3Th (P : Peers) : Protocol Acc3St WEv := gated {} acc3Next (acc3Ok P)

/-- `error-code.invalid-state` (0.3; `eInvalidState3'_wit`: the WIT case number of the name). -/
abbrev eInvalidState3' : Nat := 5

/-- The literal is the case number of `invalid-state` in the 0.3 `error-code` of the WIT. -/
theorem eInvalidState3'_wit : eInvalidState3' = WitImport.caseIdx Net.codes3 "invalid-state" := by
  decide +kernel

/-- The packed `COMPLETED 1`. -/
def completed1 : Val := natV 16

/-- **The concrete 0.3 listen/accept host of the connections `C`.** -/
def acc3Impl (C : Conn) : Impl := fun p f a =>
  let q := p.foldl acc3Next {}
  if f = tcpBind3 then some [okV none]
  else if f = tcpListen3 then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f = cStreamRead then
    (match lookup (selfH a) q.lst with
     | some addr =>
       (match C addr with
        | some _ => some [completed1, .record [.u32 (BitVec.ofNat 32 p.length)]]
        | none => some [natV Silmaril.Wasm.Component.Async.blocked, .record []])
     | none => none)
  else if f = tcpRemote3 then
    (match lookup (selfH a) q.acc with
     | some addr =>
       (match C addr with
        | some r => some [okV (some r)]
        | none => errAnsN eInvalidState3')
     | none => errAnsN eInvalidState3')
  else none

end Silmaril.Wasi.Versions.Accept3

module

public import Silmaril.Wasi.Versions.NetMore.Defs
public import Silmaril.Wasi.Versions.Net3.Defs
public import Silmaril.Wasi.Versions.WitImport.PickRest.Defs

@[expose] public section

/-!
# UDP receive in WASI 0.2 and 0.3: host models and the 0.3 theory

`Silmaril.Wasi.Versions.NetMore` states the 0.2 UDP receive theory `udpTh U` (an inbox `U` says
which `incoming-datagram` records the network delivers to each local address). This module
adds:

* **A 0.2 host** `udpImpl D` for a delivery `D : Val → List Val` (the datagrams queued at each
  local address): `create-udp-socket` and `stream` answer fresh handles, `start-bind` and
  `finish-bind` succeed, and `receive(i, n)` on a tied stream answers the first `n` datagrams
  queued at its address (the same ones every time: duplication is allowed by `udpTh`), and
  `error(invalid-state)` on another stream.
* **The 0.3 UDP theory** `udpTh3 U`, checked against `specs/wasi/0.3.2/sockets/types.wit`
  (resource `udp-socket`): `bind: func(local-address: ip-socket-address) -> result<_,
  error-code>` binds the socket, and `receive: async func() -> result<tuple<list<u8>,
  ip-socket-address>, error-code>` (sync-lowered) answers one datagram. The answer
  `ok(tuple<data, remote-address>)` is the value `.record [data, remote-address]`, the same value
  as the 0.2 record `incoming-datagram { data, remote-address }`, so one inbox serves both
  versions. A `receive` on a bound socket answered `ok(d)` needs `U local d`. Gated like
  `udpTh`: other answers (errors, traps, ill-typed answers) are not constrained.
* **A 0.3 host** `udpImpl3 D`: `create` answers a fresh handle, `bind` succeeds, and `receive`
  on a bound socket answers the first datagram queued at its address (`error(invalid-state)`
  when there is none, or the socket is not bound).

`udpSend3` (`send: async func(data: list<u8>, remote-address: option<ip-socket-address>)`) does
not observe the network and is not constrained.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Names -/

/-- `wasi:sockets/udp.[method]udp-socket.finish-bind` (0.2). -/
def udpFinishBind : FnName := ⟨"wasi:sockets/udp", "[method]udp-socket.finish-bind"⟩

/-- The 0.2 UDP functions of this slice, **read from the vendored WIT**: the functions of the
imported table `sock2T` with the keys `WitImport.udpKeys`. Proofs that need the members rewrite
with `udpImports_eq`. -/
def udpImports : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.sock2T) WitImport.udpKeys}

/-- **The imported functions of `udpImports` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem udpImports_eq :
    udpImports = {instanceNetwork, createUdp, udpBind, udpFinishBind, udpStream, udpReceive} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.sock2T) WitImport.udpKeys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.sock2T) WitImport.udpKeys).Perm
    [instanceNetwork, createUdp, udpBind, udpFinishBind, udpStream, udpReceive] by
      decide +kernel).mem_iff]
  simp

/-- `wasi:sockets/types@0.3.2.[static]udp-socket.create`. -/
def udpCreate3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[static]udp-socket.create"⟩
/-- `wasi:sockets/types@0.3.2.[method]udp-socket.bind`. -/
def udpBind3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]udp-socket.bind"⟩
/-- `wasi:sockets/types@0.3.2.[method]udp-socket.receive` (async, observed sync-lowered). -/
def udpReceive3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]udp-socket.receive"⟩
/-- `wasi:sockets/types@0.3.2.[method]udp-socket.send` (async, observed sync-lowered). -/
def udpSend3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]udp-socket.send"⟩

/-- The 0.3 UDP functions of this slice, **read from the vendored WIT** (`sock3T` with the keys
`WitImport.udp3Keys`). Proofs that need the members rewrite with `udp3Fns_eq`. -/
def udp3Fns : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.sock3T) WitImport.udp3Keys}

/-- **The imported functions of `udp3Fns` are the hand-written ones.** -/
theorem udp3Fns_eq : udp3Fns = {udpCreate3, udpBind3, udpReceive3, udpSend3} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.sock3T) WitImport.udp3Keys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.sock3T) WitImport.udp3Keys).Perm
    [udpCreate3, udpBind3, udpReceive3, udpSend3] by decide +kernel).mem_iff]
  simp

/-- 0.2 `error-code.invalid-state` (`eInvalidState_wit`: the WIT case number of the name). -/
abbrev eInvalidState : Nat := 9
/-- 0.3 `error-code.invalid-state` (`eInvalidState3_wit`). -/
abbrev eInvalidState3 : Nat := 5

/-- The literal is the case number of `invalid-state` in the 0.2 `error-code` of the WIT. -/
theorem eInvalidState_wit : eInvalidState = WitImport.caseIdx codes2 "invalid-state" := by
  decide +kernel
/-- The literal is the case number of `invalid-state` in the 0.3 `error-code` of the WIT. -/
theorem eInvalidState3_wit : eInvalidState3 = WitImport.caseIdx codes3 "invalid-state" := by
  decide +kernel

/-! ## The 0.2 host -/

/-- The state of the 0.2 UDP theory after the answers `p`. -/
def udpState (p : List WEv) : UdpSt := p.foldl udpNext {}

/-- A delivery: the datagrams queued at each local address. -/
abbrev Delivery : Type := Val → List Val

/-- The delivery is admitted by the inbox `U`. -/
def DeliveryOk (U : Inbox) (D : Delivery) : Prop := ∀ a d, d ∈ D a → U a d = true

/-- The number of datagrams asked for by `receive(self, max-results)`. -/
def maxOf : List Val → Nat
  | _ :: .u64 n :: _ => n.toNat
  | _ => 0

/-- **The concrete 0.2 UDP host of the delivery `D`.** -/
def udpImpl (D : Delivery) : Impl := fun p f a =>
  if f = instanceNetwork then some [.u32 (BitVec.ofNat 32 p.length)]
  else if f = createUdp then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f = udpBind ∨ f = udpFinishBind then some [okV none]
  else if f = udpStream then
    some [okV (some (.record [.u32 (BitVec.ofNat 32 p.length),
      .u32 (BitVec.ofNat 32 (p.length + 1))]))]
  else if f = udpReceive then
    (match lookup (selfH a) (udpState p).ins with
     | some addr => some [okV (some (.record ((D addr).take (maxOf a))))]
     | none => errAnsN eInvalidState)
  else none

/-! ## The 0.3 theory -/

/-- The 0.3 UDP theory state: bound sockets, with their local address. -/
abbrev Udp3St : Type := List (BitVec 32 × Val)

/-- The next 0.3 UDP state. -/
def udpNext3 (q : Udp3St) (e : WEv) : Udp3St :=
  match e with
  | .imp f (.u32 s :: addr :: _) (some [.variant 0 none]) =>
    if f = udpBind3 then (s, addr) :: q else q
  | _ => q

/-- A 0.3 `receive` answer for the datagrams `d` delivered to the socket's address. -/
def recvOk3 (d : Val → Bool) : Option (List Val) → Bool
  | some [.variant 0 (some x)] => d x
  | _ => true

/-- The check of a 0.3 UDP answer against the inbox `U`. -/
def udpOk3 (U : Inbox) (q : Udp3St) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 s :: _) r =>
    if f = udpReceive3 then
      (match lookup s q with
       | some addr => recvOk3 (U addr) r
       | none => true)
    else true
  | _ => true

/-- **The 0.3 UDP receive theory** of the inbox `U`. -/
def udpTh3 (U : Inbox) : Protocol Udp3St WEv := gated [] udpNext3 (udpOk3 U)

/-- A decisive 0.3 UDP event: `receive` on a bound socket answered `ok`. -/
def udpDecisive3 (q : Udp3St) (e : WEv) : Prop :=
  ∃ s a x, e = .imp udpReceive3 (.u32 s :: a) (some [.variant 0 (some x)]) ∧
    (lookup s q).isSome

/-- The state of the 0.3 UDP theory after the answers `p`. -/
def udpState3 (p : List WEv) : Udp3St := p.foldl udpNext3 []

/-- The 0.3 answer of a queue: its first datagram, or `error(invalid-state)`. -/
def recvAns3 : List Val → Option (List Val)
  | d :: _ => some [okV (some d)]
  | [] => some [errV (some (ecV3 eInvalidState3))]

/-- **The concrete 0.3 UDP host of the delivery `D`.** -/
def udpImpl3 (D : Delivery) : Impl := fun p f a =>
  if f = udpCreate3 then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f = udpBind3 ∨ f = udpSend3 then some [okV none]
  else if f = udpReceive3 then
    (match lookup (selfH a) (udpState3 p) with
     | some addr => recvAns3 (D addr)
     | none => recvAns3 [])
  else none

end Silmaril.Wasi.Versions.Net

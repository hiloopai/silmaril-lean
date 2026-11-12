module

public import Silmaril.Wasi.Versions.Udp.Defs

@[expose] public section

/-!
# WASI 0.3 UDP: `connect`, `disconnect`, `send` and the address getters

`Silmaril.Wasi.Versions.Udp` gives the 0.3 UDP receive theory (`udpTh3`) and a host whose `send`
always succeeds. This module states what `specs/wasi/0.3.2/sockets/types.wit` (resource
`udp-socket`) says about the other functions, as conditions on their `ok` answers:

* `create(address-family)`: "Whether this is a IPv4 or IPv6 socket. This is the value passed to
  the constructor" (`get-address-family`).
* `connect(remote-address)`: `invalid-argument` for the wrong address family, an IP address
  `0.0.0.0`/`::`, or port `0`. "On success, the `remote-address` of the socket is updated." It
  also binds implicitly; "the `local-address` may be updated as well".
* `disconnect()`: `invalid-state` "The socket is not connected".
* `send(data, remote-address: option<ip-socket-address>)`: `invalid-argument` for the wrong
  family, an any-address, port `0`, "The socket is in "connected" mode and `remote-address` is
  `some` value that does not match the address passed to `connect`", and "The socket is not
  "connected" and no value for `remote-address` was provided". It binds implicitly.
* `receive()`: "If the socket is connected, the sender address is guaranteed to match the
  remote address passed to `connect`."
* `get-local-address()`: `invalid-state` when not bound ("WASI is stricter"); after an explicit
  `bind` to an address with a nonzero IP address and port (and no `connect` since) the answer
  is that address.
* `get-remote-address()`: `invalid-state` when not connected; otherwise the connected address.

Addresses are compared through `akey`, their numbers (family, port, IP address and, for IPv6,
the flow information and scope), because `Val` has no lawful equality.

**The theory** `udpConnTh3` is gated: it constrains the `ok` answers above (and the
`get-address-family` answer) and nothing else. **The host** `udpConnImpl3` answers `ok` exactly
when the conditions hold, `error(invalid-argument)` / `error(invalid-state)` otherwise, the
stored addresses for the getters, and `error(invalid-state)` for `receive`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Udp3Conn

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net

/-! ## Names -/

def udpConnect3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]udp-socket.connect"⟩
def udpDisconnect3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]udp-socket.disconnect"⟩
def udpLocal3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]udp-socket.get-local-address"⟩
def udpRemote3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]udp-socket.get-remote-address"⟩
def udpFamily3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]udp-socket.get-address-family"⟩

/-! ## Addresses -/

/-- The numbers of an address: family (`0` IPv4, `1` IPv6), port, IP address, and the IPv6
flow information and scope. -/
structure AKey where
  fam : Nat
  port : Nat
  ip : List Nat
  extra : List Nat
  deriving DecidableEq

/-- A `u8` as a number. -/
def u8Of : Val → Option Nat
  | .u8 x => some x.toNat
  | _ => none

/-- A `u16` as a number. -/
def u16Of : Val → Option Nat
  | .u16 x => some x.toNat
  | _ => none

/-- The numbers of an `ip-socket-address`. -/
def akey : Val → Option AKey
  | .variant 0 (some (.record [.u16 port, .record ip])) =>
    (ip.mapM u8Of).bind fun l => if l.length = 4 then some ⟨0, port.toNat, l, []⟩ else none
  | .variant 1 (some (.record [.u16 port, .u32 fi, .record ip, .u32 sid])) =>
    (ip.mapM u16Of).bind fun l =>
      if l.length = 8 then some ⟨1, port.toNat, l, [fi.toNat, sid.toNat]⟩ else none
  | _ => none

/-- An address one may connect or send to: nonzero port and IP address, of the family `fam`
when known. -/
def destOk (fam : Option Nat) (k : AKey) : Bool :=
  k.port != 0 && k.ip.any (· != 0) && fam.all (· == k.fam)

/-- The family of an `ip-address-family` value. -/
def famOf : Val → Option Nat
  | .variant k none => some k
  | _ => none

/-! ## The state -/

/-- The theory state. -/
structure UCSt where
  /-- The family of each created socket. -/
  fam : List (BitVec 32 × Nat) := []
  /-- The bound sockets, with the bound address when it was bound explicitly to a fully
  specified address (nonzero IP address and port) and not connected since. -/
  bound : List (BitVec 32 × Option Val) := []
  /-- The connected sockets, with the address (`none`: disconnected). -/
  conn : List (BitVec 32 × Option Val) := []

/-- The connected address of `s`. -/
def connOf (q : UCSt) (s : BitVec 32) : Option Val := (lookup s q.conn).bind id

/-- Bind `s` implicitly (the local address becomes unknown). -/
def implicitBind (q : UCSt) (s : BitVec 32) : UCSt := { q with bound := (s, none) :: q.bound }

/-- A fully specified address: nonzero IP address and port. -/
def fullAddr (v : Val) : Bool :=
  match akey v with
  | some k => k.port != 0 && k.ip.any (· != 0)
  | none => false

/-- The next state. -/
def ucNext (q : UCSt) : WEv → UCSt
  | .imp f a r =>
    if f = udpCreate3 then
      (match a, r with
       | [af], some [.variant 0 (some (.u32 s))] =>
         (match famOf af with
          | some k => { q with fam := (s, k) :: q.fam }
          | none => q)
       | _, _ => q)
    else
      (match a, r with
       | .u32 s :: rest, some [.variant 0 none] =>
         if f = udpBind3 then
           (match rest with
            | addr :: _ =>
              { q with bound := (s, if fullAddr addr then some addr else none) :: q.bound }
            | [] => q)
         else if f = udpConnect3 then
           (match rest with
            | addr :: _ =>
              let q' := implicitBind q s
              { q' with conn := (s, some addr) :: q'.conn }
            | [] => q)
         else if f = udpDisconnect3 then { q with conn := (s, none) :: q.conn }
         else if f = udpSend3 then implicitBind q s
         else q
       | _, _ => q)
  | _ => q

/-! ## The checks -/

/-- The remote-address argument of `send(self, data, remote-address)`. -/
def sendDest : List Val → Option (Option Val)
  | [_, _, .variant 0 none] => some none
  | [_, _, .variant 1 (some a)] => some (some a)
  | _ => none

/-- The condition of an `ok` answer of `connect`. -/
def connectCond (q : UCSt) (s : BitVec 32) (addr : Val) : Bool :=
  match akey addr with
  | some k => destOk (lookup s q.fam) k
  | none => false

/-- The condition of an `ok` answer of `send`. -/
def sendCond (q : UCSt) (s : BitVec 32) (a : List Val) : Bool :=
  match sendDest a with
  | some none => (connOf q s).isSome
  | some (some addr) =>
    (match akey addr with
     | some k => destOk (lookup s q.fam) k && (connOf q s).all (akey · == some k)
     | none => false)
  | none => true

/-- An answer `ok(w)` with the same address as `v`. -/
def okAddrIs (v : Val) : Option (List Val) → Bool
  | some [.variant 0 (some w)] => akey w == akey v
  | _ => true

/-- An `ok` answer. -/
def isOk : Option (List Val) → Bool
  | some [.variant 0 _] => true
  | _ => false

/-- The check of every answer. -/
def ucOk (q : UCSt) : WEv → Bool
  | .imp f (.u32 s :: rest) r =>
    if f = udpConnect3 then
      (match rest with
       | addr :: _ => !isOk r || connectCond q s addr
       | [] => true)
    else if f = udpDisconnect3 then !isOk r || (connOf q s).isSome
    else if f = udpSend3 then !isOk r || sendCond q s (.u32 s :: rest)
    else if f = udpRemote3 then
      (match connOf q s with
       | some v => okAddrIs v r
       | none => !isOk r)
    else if f = udpLocal3 then
      (match lookup s q.bound with
       | some (some v) => okAddrIs v r
       | some none => true
       | none => !isOk r)
    else if f = udpReceive3 then
      (match connOf q s, r with
       | some v, some [.variant 0 (some (.record [_, src]))] => akey src == akey v
       | _, _ => true)
    else if f = udpFamily3 then
      (match lookup s q.fam, r with
       | some k, some [v] => famOf v == some k
       | _, _ => true)
    else true
  | _ => true

/-- **The 0.3 UDP connect/send theory.** -/
def udpConnTh3 : Protocol UCSt WEv := gated {} ucNext ucOk

/-! ## The host -/

/-- The state after the answers `p`. -/
def ucState (p : List WEv) : UCSt := p.foldl ucNext {}

/-- 0.3 `error-code.invalid-argument`. -/
abbrev eInvalidArg3 : Nat := 3

/-- `ok` (unit) if `c`, the error `e` otherwise. -/
def okIf (c : Bool) (e : Nat) : Option (List Val) :=
  if c then some [okV none] else some [errV (some (ecV3 e))]

/-- An unknown local address (port 1, `0.0.0.1`). -/
def someLocal : Val := .variant 0 (some (.record [.u16 1, .record [.u8 0, .u8 0, .u8 0, .u8 1]]))

/-- The host's answer to `f` on the socket `s` with the other arguments `rest`. -/
def sockA (q : UCSt) (f : FnName) (s : BitVec 32) (rest : List Val) : Option (List Val) :=
  if f = udpConnect3 then
    (match rest with
     | addr :: _ => okIf (connectCond q s addr) eInvalidArg3
     | [] => none)
  else if f = udpDisconnect3 then okIf (connOf q s).isSome eInvalidState3
  else if f = udpSend3 then okIf (sendCond q s (.u32 s :: rest)) eInvalidArg3
  else if f = udpRemote3 then
    (match connOf q s with
     | some v => some [okV (some v)]
     | none => some [errV (some (ecV3 eInvalidState3))])
  else if f = udpLocal3 then
    (match lookup s q.bound with
     | some (some v) => some [okV (some v)]
     | some none => some [okV (some someLocal)]
     | none => some [errV (some (ecV3 eInvalidState3))])
  else if f = udpReceive3 then some [errV (some (ecV3 eInvalidState3))]
  else if f = udpFamily3 then
    (match lookup s q.fam with
     | some k => some [.variant k none]
     | none => some [.variant 0 none])
  else none

/-- **The concrete 0.3 UDP connect/send host.** -/
def udpConnImpl3 : Impl := fun p f a =>
  if f = udpCreate3 then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f = udpBind3 then some [okV none]
  else
    match a with
    | .u32 s :: rest => sockA (ucState p) f s rest
    | _ => none

end Silmaril.Wasi.Versions.Udp3Conn

module

public import Silmaril.Wasi.Versions.Accept3.Defs
public import Silmaril.Wasi.Versions.NetAddr.Defs

@[expose] public section

/-!
# WASI 0.3 TCP: the socket state machine, `bind` and the address getters

`vendor/wasi/0.3.2/sockets/types.wit` (resource `tcp-socket`) describes a socket by its state,
"`unbound`, `bound`, `listening`, `connecting`, `connected`, `closed`", and states:

* `create(address-family)`: the new socket is `unbound`; `get-address-family` "is the value
  passed to the constructor".
* `bind(local-address)`: `invalid-argument` for "the wrong address family" and
  `invalid-state` when "The socket is already bound"; "Bind can be attempted multiple times
  ... as long as the previous bind failed. Once a bind succeeds, the binding can't be changed
  anymore."
* `listen()`: "Transitions the socket into the `listening` state. This can be called at most
  once per socket", `invalid-state` when "already in the `connected` state" or "already in
  the `listening` state"; it binds implicitly.
* `connect(remote-address)`: "On success, the socket is transitioned into the `connected`
  state"; `invalid-state` when connecting, connected or listening; "After a failed connection
  attempt, the socket will be in the `closed` state"; the local address "may be updated".
* `get-local-address()`: "WASI is stricter and requires `get-local-address` to return
  `invalid-state` when the socket hasn't been bound yet."
* `get-is-listening()`: "Whether the socket is in the `listening` state."

**The theory `tcpAddrTh3`** is gated. Its state follows each socket created in the trace
through the phases `TPhase` (`unbound`, `bound`, `listening`, `connected`, and `unknown` once
the trace no longer determines it, e.g. after a failed `connect` or a trap), with its family
and, when it was bound explicitly to a fully specified address (`NetAddr.SockAddr.full`) and
has not connected since, that address. It checks:

* an `ok` `bind` is on an `unbound` socket, of a decodable address of the socket's family;
* an `ok` `listen` is on an `unbound` or `bound` socket, an `ok` `connect` likewise;
* `get-is-listening` answers whether the phase is `listening` (when known);
* `get-address-family` answers the constructor's family;
* `get-local-address` of an `unbound` socket is not `ok`, and of a socket with a recorded
  address is that address (compared through `NetAddr.sockAddrOf`, decoded).

Sockets not created in the trace (for example those read from a `listen` stream) are not
checked. Errors are always admitted, so the theory is loose. **The host** `tcpAddrImpl3`
answers exactly by the state machine.

This is the WASI-level counterpart of the RFC 9293 §3.3.2 connection states the `Net` transport
track formalizes (`LISTEN`, `SYN-SENT`, `ESTABLISHED`, …): WASI's `listening` is `LISTEN`,
`connected` is `ESTABLISHED` or later, and `bound`/`unbound` are not TCP states (they are
socket-layer states). The relation is pass-2 work.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Tcp3Addr

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.NetAddr (SockAddr sockAddrOf)
open Silmaril.Wasi.Versions.Udp3Conn (famOf isOk okIf eInvalidArg3)
open Silmaril.Wasi.Versions.Accept3 (tcpBind3 tcpListen3)

/-! ## Names -/

def tcpLocal3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.get-local-address"⟩
def tcpIsListening3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.get-is-listening"⟩
def tcpFamily3 : FnName := ⟨"wasi:sockets/types@0.3.2", "[method]tcp-socket.get-address-family"⟩

/-! ## The state machine -/

/-- The phase of a socket, as far as the trace determines it. -/
inductive TPhase where
  | unbound | bound | listening | connected | unknown
  deriving DecidableEq, Repr

/-- What the theory knows of a socket. -/
structure TSock where
  /-- The family passed to `create`. -/
  fam : Nat
  /-- The phase. -/
  phase : TPhase
  /-- The explicitly bound, fully specified address (`none`: not recorded). -/
  addr : Option Val

/-- The theory state: the sockets created in the trace (latest entry first). -/
abbrev TASt : Type := List (BitVec 32 × TSock)

/-- Update the socket `s`. -/
def upd (q : TASt) (s : BitVec 32) (g : TSock → TSock) : TASt :=
  match lookup s q with
  | some t => (s, g t) :: q
  | none => q

/-- The address of a successful `bind`, when recorded: a decodable, fully specified one. -/
def boundAddr (a : Val) : Option Val :=
  match sockAddrOf a with
  | some x => if x.full then some a else none
  | none => none

/-- The next state. -/
def taNext (q : TASt) : WEv → TASt
  | .imp f a r =>
    if f = create3 then
      (match a, r with
       | [af], some [.variant 0 (some (.u32 s))] =>
         (match famOf af with
          | some k => (s, ⟨k, .unbound, none⟩) :: q
          | none => q)
       | _, _ => q)
    else
      (match a with
       | .u32 s :: rest =>
         if f = tcpBind3 then
           (if isOk r then
              (match rest with
               | addr :: _ => upd q s fun t => { t with phase := .bound, addr := boundAddr addr }
               | [] => q)
            else if r.isNone then upd q s fun t => { t with phase := .unknown }
            else q)
         else if f = tcpListen3 then
           (if isOk r then upd q s fun t => { t with phase := .listening }
            else upd q s fun t => { t with phase := .unknown })
         else if f = connect3 then
           (if isOk r then upd q s fun t => { t with phase := .connected, addr := none }
            else upd q s fun t => { t with phase := .unknown, addr := none })
         else q
       | _ => q)
  | _ => q

/-! ## The checks -/

/-- `unbound` or `bound`: `listen` and `connect` may succeed. -/
def TPhase.canStart : TPhase → Bool
  | .unbound | .bound | .unknown => true
  | _ => false

/-- The condition of an `ok` `bind` of `addr` on a socket in `t`. -/
def bindCond (t : TSock) (addr : Val) : Bool :=
  (t.phase == .unbound || t.phase == .unknown) &&
    (match sockAddrOf addr with
     | some x => x.fam == t.fam
     | none => false)

/-- The answer of `get-is-listening` for the phase. -/
def listeningOk (p : TPhase) : Option (List Val) → Bool
  | some [.bool b] => p == .unknown || b == (p == .listening)
  | _ => true

/-- The answer of `get-local-address` for the socket. -/
def localOk (t : TSock) (r : Option (List Val)) : Bool :=
  match t.phase, t.addr, r with
  | .unbound, _, r => !isOk r
  | _, some v, some [.variant 0 (some w)] => sockAddrOf w == sockAddrOf v
  | _, _, _ => true

/-- The check of every answer. -/
def taOk (q : TASt) : WEv → Bool
  | .imp f (.u32 s :: rest) r =>
    match lookup s q with
    | none => true
    | some t =>
      if f = tcpBind3 then
        (match rest with
         | addr :: _ => !isOk r || bindCond t addr
         | [] => true)
      else if f = tcpListen3 then !isOk r || t.phase.canStart
      else if f = connect3 then !isOk r || t.phase.canStart
      else if f = tcpIsListening3 then listeningOk t.phase r
      else if f = tcpFamily3 then
        (match r with
         | some [v] => famOf v == some t.fam
         | _ => true)
      else if f = tcpLocal3 then localOk t r
      else true
  | _ => true

/-- **The 0.3 TCP socket-state theory.** -/
def tcpAddrTh3 : Protocol TASt WEv := gated [] taNext taOk

/-! ## The host -/

/-- The state after the answers `p`. -/
def taState (p : List WEv) : TASt := p.foldl taNext []

/-- An unknown local address (port 1, `0.0.0.1`), for implicit bindings. -/
def someLocal4 : Val := Udp3Conn.someLocal

/-- The host's `get-local-address`: `invalid-state` when unbound, else the recorded address
(or an arbitrary one). -/
def localAns (t : TSock) : Option (List Val) :=
  match t.phase, t.addr with
  | .unbound, _ => some [errV (some (ecV3 eInvalidState3))]
  | _, some v => some [okV (some v)]
  | _, none => some [okV (some someLocal4)]

/-- The host's answer to `f` on the tracked socket `t`. -/
def sockA (t : TSock) (f : FnName) (rest : List Val) : Option (List Val) :=
  if f = tcpBind3 then
    (match rest with
     | addr :: _ => okIf (bindCond t addr) (if t.phase == .unbound then eInvalidArg3 else
         eInvalidState3)
     | [] => none)
  else if f = tcpListen3 then
    if t.phase.canStart then some [okV (some (.u32 0))] else some [errV (some (ecV3 eInvalidState3))]
  else if f = connect3 then okIf t.phase.canStart eInvalidState3
  else if f = tcpIsListening3 then some [.bool (t.phase == .listening)]
  else if f = tcpFamily3 then some [.variant t.fam none]
  else if f = tcpLocal3 then localAns t
  else none

/-- **The concrete 0.3 TCP socket-state host**: fresh handles; the other answers by the state
machine (untracked sockets: `invalid-state`). -/
def tcpAddrImpl3 : Impl := fun p f a =>
  if f = create3 then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else
    match a with
    | .u32 s :: rest =>
      match lookup s (taState p) with
      | some t => sockA t f rest
      | none => some [errV (some (ecV3 eInvalidState3))]
    | _ => none

end Silmaril.Wasi.Versions.Tcp3Addr

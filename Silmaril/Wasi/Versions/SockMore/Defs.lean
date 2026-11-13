module

public import Silmaril.Wasi.Versions.Udp.Defs

@[expose] public section

/-!
# Sockets: name-lookup and accept hosts, and socket options in 0.2 and 0.3

`Silmaril.Wasi.Versions.NetMore` states the theories `dnsTh R`, `dnsTh3 R` (name lookup) and
`acceptTh P` (bind/accept) without concrete hosts. This module adds:

* **Name-lookup hosts.** A lookup table `L : Val → List Val` (the addresses of each name),
  admitted by `R` (`LookupOk R L`). `dnsImpl L` (0.2): `resolve-addresses` answers a fresh
  stream, the `k`-th `resolve-next-address` on a stream of `name` answers `ok(some a)` for the
  `k`-th address of `L name` and `ok(none)` after the last. `dnsImpl3 L` (0.3, sync-lowered):
  `resolve-addresses(name)` answers `ok(L name)`.
* **An accept host** (0.2). Connections `C : Val → Option Val` (the peer connecting to each local
  address, if any), admitted by the peers `P` (`ConnOk P C`). `accImpl C`: `start-bind` and
  `start-listen` succeed; `accept` on a socket bound to `local` answers fresh handles when
  `C local` is a peer and `error(would-block)` otherwise; `remote-address` of an accepted socket
  answers its peer.
* **A socket-option theory** `optTh O` for an option table `O : List OptSpec` (one entry per
  setter, with its getter, whether a set value is read back exactly, and whether `0` is
  rejected), with the tables `tcpOpts2`, `udpOpts2`, `tcpOpts3`, `udpOpts3` read from
  `specs/wasi/0.2.12/sockets/{tcp,udp}.wit` and `specs/wasi/0.3.2/sockets/types.wit`:
  * "If the provided value is 0, an `invalid-argument` error is returned": a setter of a
    nonzero option answered `ok` on the value `0` is rejected (`set-listen-backlog-size`,
    `set-keep-alive-idle-time`, `-interval`, `-count`, `set-hop-limit`,
    `set-unicast-hop-limit`, `set-receive-buffer-size`, `set-send-buffer-size`);
  * a getter answered `ok(v)` after a successful set of `n` on the same socket returns `n` (read
    at the getter's type, `OptTy.norm`, which is `n` for a typed argument), for
    the options the WIT does not allow to round (`keep-alive-enabled`, `hop-limit`,
    `unicast-hop-limit`). The others "might be silently clamped and/or rounded. I.e. after
    setting a value, reading the same setting back may return a different value": unconstrained.
  `optImpl O` answers `error(invalid-argument)` to a zero for a nonzero option, records the
  rest, and reads back the last value set (or the option's default).

Values are compared through their numbers (`numOf`: `bool` as `0`/`1`, unsigned integers),
since `Val` has no lawful decidable equality.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.SockMore

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net

/-! ## Name lookup hosts -/

/-- A lookup table: the addresses of each name. -/
abbrev Lookup : Type := Val → List Val

/-- The table is admitted by the resolver `R`. -/
def LookupOk (R : Resolver) (L : Lookup) : Prop := ∀ n a, a ∈ L n → R n a = true

/-- The event is a `resolve-next-address` on the stream `st`. -/
def isNextOn (st : BitVec 32) : WEv → Bool
  | .imp f (.u32 s :: _) _ => decide (f = resolveNext) && s == st
  | _ => false

/-- The answer of the `k`-th `resolve-next-address` on a stream of a name with addresses `l`. -/
def nextAns (l : List Val) (k : Nat) : Option (List Val) :=
  match l[k]? with
  | some a => some [okV (some (.variant 1 (some a)))]
  | none => some [okV (some (.variant 0 none))]

/-- **The concrete 0.2 name-lookup host of the table `L`.** -/
def dnsImpl (L : Lookup) : Impl := fun p f a =>
  if f = resolve2 then some [okV (some (.u32 (BitVec.ofNat 32 p.length)))]
  else if f = resolveNext then
    (match lookup (selfH a) (p.foldl dnsNext []) with
     | some name => nextAns (L name) (p.filter (isNextOn (selfH a))).length
     | none => errAnsN eInvalidState)
  else none

/-- **The concrete 0.3 name-lookup host of the table `L`.** -/
def dnsImpl3 (L : Lookup) : Impl := fun _ f a =>
  if f = resolve3 then
    (match a with
     | name :: _ => some [okV (some (.record (L name)))]
     | [] => some [okV (some (.record []))])
  else none

/-! ## The accept host -/

/-- Connections: the peer connecting to each local address, if any. -/
abbrev Conn : Type := Val → Option Val

/-- The connections are admitted by the peers `P`. -/
def ConnOk (P : Peers) (C : Conn) : Prop :=
  ∀ a r, C a = some r → P.connects a = true ∧ P.peer a r = true

/-- **The concrete 0.2 accept host of the connections `C`.** -/
def accImpl (C : Conn) : Impl := fun p f a =>
  let q := p.foldl accNext {}
  let n := p.length
  if f = tcpBind ∨ f = tcpListen then some [okV none]
  else if f = tcpAccept then
    (match lookup (selfH a) q.bound with
     | some addr =>
       (match C addr with
        | some _ => some [okV (some (.record [.u32 (BitVec.ofNat 32 n),
            .u32 (BitVec.ofNat 32 (n + 1)), .u32 (BitVec.ofNat 32 (n + 2))]))]
        | none => errAnsN eWouldBlock)
     | none => errAnsN eInvalidState)
  else if f = tcpRemote then
    (match lookup (selfH a) q.acc with
     | some addr =>
       (match C addr with
        | some r => some [okV (some r)]
        | none => errAnsN eInvalidState)
     | none => errAnsN eInvalidState)
  else none

/-! ## Socket options -/

/-- The number of an option value. -/
def numOf : Val → Option Nat
  | .bool b => some (if b then 1 else 0)
  | .u8 x => some x.toNat
  | .u32 x => some x.toNat
  | .u64 x => some x.toNat
  | _ => none

/-- The type of an option value. -/
inductive OptTy where
  | bool | u8 | u32 | u64

/-- The value of a number at an option type. -/
def OptTy.enc : OptTy → Nat → Val
  | .bool, n => .bool (n != 0)
  | .u8, n => .u8 (BitVec.ofNat 8 n)
  | .u32, n => .u32 (BitVec.ofNat 32 n)
  | .u64, n => .u64 (BitVec.ofNat 64 n)

/-- A number read at an option type (what `numOf ∘ enc` gives back). -/
def OptTy.norm : OptTy → Nat → Nat
  | .bool, n => if n != 0 then 1 else 0
  | .u8, n => n % 2 ^ 8
  | .u32, n => n % 2 ^ 32
  | .u64, n => n % 2 ^ 64

/-- One option: its setter and getter, its type, whether a set value is read back exactly,
whether `0` is rejected, and the host's default. -/
structure OptSpec where
  set : FnName
  get : Option FnName
  ty : OptTy
  exact : Bool
  nonzero : Bool
  dflt : Nat

/-- The option state: the last value set, per socket and setter. -/
abbrev OptSt : Type := List ((BitVec 32 × FnName) × Nat)

/-- The option whose setter is `f`. -/
def setterOf (O : List OptSpec) (f : FnName) : Option OptSpec := O.find? (·.set == f)

/-- The option whose getter is `f`. -/
def getterOf (O : List OptSpec) (f : FnName) : Option OptSpec := O.find? (·.get == some f)

/-- The answer `ok` of a `result<_, error-code>`. -/
def isOkUnit : Option (List Val) → Bool
  | some [.variant 0 none] => true
  | _ => false

/-- The check of a setter's answer on the value `v`. -/
def setChk (o : OptSpec) (v : Val) (r : Option (List Val)) : Bool :=
  !(o.nonzero && numOf v == some 0) || !isOkUnit r

/-- The check of an exact getter's answer, after the value `x` was set (if any). -/
def getChk (o : OptSpec) : Option Nat → Option (List Val) → Bool
  | some n, some [.variant 0 (some v)] => numOf v == some (o.ty.norm n)
  | _, _ => true

/-- The check of an option answer. -/
def optOk (O : List OptSpec) (q : OptSt) : WEv → Bool
  | .imp f (.u32 s :: rest) r =>
    match setterOf O f with
    | some o =>
      (match rest with
       | v :: _ => setChk o v r
       | [] => true)
    | none =>
      match getterOf O f with
      | some o => if o.exact then getChk o (q.lookup (s, o.set)) r else true
      | none => true
  | _ => true

/-- The next option state. -/
def optNext (O : List OptSpec) (q : OptSt) : WEv → OptSt
  | .imp f (.u32 s :: v :: _) (some [.variant 0 none]) =>
    match setterOf O f, numOf v with
    | some _, some n => ((s, f), n) :: q
    | _, _ => q
  | _ => q

/-- **The socket-option theory** of the option table `O`. -/
def optTh (O : List OptSpec) : Protocol OptSt WEv := gated [] (optNext O) (optOk O)

/-- The host's answer to a setter on the value `v`. -/
def setAns (o : OptSpec) (inval : Nat) (v : Val) : Option (List Val) :=
  if o.nonzero && numOf v == some 0 then errAnsN inval else some [okV none]

/-- **The concrete option host** of the table `O`; `inval` is `error-code.invalid-argument`. -/
def optImpl (O : List OptSpec) (inval : Nat) : Impl := fun p f a =>
  let q := p.foldl (optNext O) []
  match setterOf O f with
  | some o =>
    (match a with
     | _ :: v :: _ => setAns o inval v
     | _ => some [okV none])
  | none =>
    match getterOf O f with
    | some o => some [okV (some (o.ty.enc ((q.lookup (selfH a, o.set)).getD o.dflt)))]
    | none => none

/-! ## The option tables -/

/-- A 0.2 `tcp-socket` method. -/
def tcp2 (m : String) : FnName := ⟨"wasi:sockets/tcp", m⟩
/-- A 0.2 `udp-socket` method. -/
def udp2 (m : String) : FnName := ⟨"wasi:sockets/udp", m⟩
/-- A 0.3 socket method. -/
def sock3 (m : String) : FnName := ⟨"wasi:sockets/types@0.3.2", m⟩

/-- The 0.2 TCP options (`specs/wasi/0.2.12/sockets/tcp.wit`). -/
def tcpOpts2 : List OptSpec :=
  [⟨tcp2 "[method]tcp-socket.set-listen-backlog-size", none, .u64, false, true, 128⟩,
   ⟨tcp2 "[method]tcp-socket.set-keep-alive-enabled",
     some (tcp2 "[method]tcp-socket.keep-alive-enabled"), .bool, true, false, 0⟩,
   ⟨tcp2 "[method]tcp-socket.set-keep-alive-idle-time",
     some (tcp2 "[method]tcp-socket.keep-alive-idle-time"), .u64, false, true, 7200000000000⟩,
   ⟨tcp2 "[method]tcp-socket.set-keep-alive-interval",
     some (tcp2 "[method]tcp-socket.keep-alive-interval"), .u64, false, true, 75000000000⟩,
   ⟨tcp2 "[method]tcp-socket.set-keep-alive-count",
     some (tcp2 "[method]tcp-socket.keep-alive-count"), .u32, false, true, 9⟩,
   ⟨tcp2 "[method]tcp-socket.set-hop-limit",
     some (tcp2 "[method]tcp-socket.hop-limit"), .u8, true, true, 64⟩,
   ⟨tcp2 "[method]tcp-socket.set-receive-buffer-size",
     some (tcp2 "[method]tcp-socket.receive-buffer-size"), .u64, false, true, 65536⟩,
   ⟨tcp2 "[method]tcp-socket.set-send-buffer-size",
     some (tcp2 "[method]tcp-socket.send-buffer-size"), .u64, false, true, 65536⟩]

/-- The 0.2 UDP options (`specs/wasi/0.2.12/sockets/udp.wit`). -/
def udpOpts2 : List OptSpec :=
  [⟨udp2 "[method]udp-socket.set-unicast-hop-limit",
     some (udp2 "[method]udp-socket.unicast-hop-limit"), .u8, true, true, 64⟩,
   ⟨udp2 "[method]udp-socket.set-receive-buffer-size",
     some (udp2 "[method]udp-socket.receive-buffer-size"), .u64, false, true, 65536⟩,
   ⟨udp2 "[method]udp-socket.set-send-buffer-size",
     some (udp2 "[method]udp-socket.send-buffer-size"), .u64, false, true, 65536⟩]

/-- The 0.3 TCP options (`specs/wasi/0.3.2/sockets/types.wit`, resource `tcp-socket`). -/
def tcpOpts3 : List OptSpec :=
  [⟨sock3 "[method]tcp-socket.set-listen-backlog-size", none, .u64, false, true, 128⟩,
   ⟨sock3 "[method]tcp-socket.set-keep-alive-enabled",
     some (sock3 "[method]tcp-socket.get-keep-alive-enabled"), .bool, true, false, 0⟩,
   ⟨sock3 "[method]tcp-socket.set-keep-alive-idle-time",
     some (sock3 "[method]tcp-socket.get-keep-alive-idle-time"), .u64, false, true,
     7200000000000⟩,
   ⟨sock3 "[method]tcp-socket.set-keep-alive-interval",
     some (sock3 "[method]tcp-socket.get-keep-alive-interval"), .u64, false, true, 75000000000⟩,
   ⟨sock3 "[method]tcp-socket.set-keep-alive-count",
     some (sock3 "[method]tcp-socket.get-keep-alive-count"), .u32, false, true, 9⟩,
   ⟨sock3 "[method]tcp-socket.set-hop-limit",
     some (sock3 "[method]tcp-socket.get-hop-limit"), .u8, true, true, 64⟩,
   ⟨sock3 "[method]tcp-socket.set-receive-buffer-size",
     some (sock3 "[method]tcp-socket.get-receive-buffer-size"), .u64, false, true, 65536⟩,
   ⟨sock3 "[method]tcp-socket.set-send-buffer-size",
     some (sock3 "[method]tcp-socket.get-send-buffer-size"), .u64, false, true, 65536⟩]

/-- The 0.3 UDP options (`specs/wasi/0.3.2/sockets/types.wit`, resource `udp-socket`). -/
def udpOpts3 : List OptSpec :=
  [⟨sock3 "[method]udp-socket.set-unicast-hop-limit",
     some (sock3 "[method]udp-socket.get-unicast-hop-limit"), .u8, true, true, 64⟩,
   ⟨sock3 "[method]udp-socket.set-receive-buffer-size",
     some (sock3 "[method]udp-socket.get-receive-buffer-size"), .u64, false, true, 65536⟩,
   ⟨sock3 "[method]udp-socket.set-send-buffer-size",
     some (sock3 "[method]udp-socket.get-send-buffer-size"), .u64, false, true, 65536⟩]

/-! ## UDP send through an `outgoing-datagram-stream` (0.2) -/

def checkSend : FnName := ⟨"wasi:sockets/udp", "[method]outgoing-datagram-stream.check-send"⟩
def udpSend : FnName := ⟨"wasi:sockets/udp", "[method]outgoing-datagram-stream.send"⟩

/-- The send state: the number of datagrams the last `check-send` of each stream permitted (not
yet used by a `send`). -/
abbrev SendSt : Type := List (BitVec 32 × Option Nat)

/-- The number of datagrams of a `list<outgoing-datagram>`. -/
def countOf : Val → Option Nat
  | .record ds => some ds.length
  | _ => none

/-- The answer `error(would-block)`. -/
def isWouldBlockA : Option (List Val) → Bool
  | some [.variant 1 (some (.variant 8 none))] => true
  | _ => false

/-- The check of a `send` of `n` datagrams with the permit `pm`. -/
def sendChk (pm : Option Nat) (n : Nat) : Option (List Val) → Bool
  | none => true
  | some [.variant 0 (some (.u64 k))] =>
    pm.any (n ≤ ·) && decide (k.toNat ≤ n) && (n != 0 || k.toNat == 0)
  | r => pm.any (n ≤ ·) && !isWouldBlockA r

/-- The check of a UDP send answer: `check-send` never answers `would-block`; a `send` beyond its
permit (or without one) traps; otherwise it answers at most the number of datagrams, `0` for
none, and never `would-block`. -/
def sendOk (q : SendSt) : WEv → Bool
  | .imp f (.u32 s :: rest) r =>
    if f = checkSend then !isWouldBlockA r
    else if f = udpSend then
      (match rest with
       | d :: _ => (match countOf d with
         | some n => sendChk ((lookup s q).getD none) n r
         | none => true)
       | [] => true)
    else true
  | _ => true

/-- The next send state. -/
def sendNext (q : SendSt) : WEv → SendSt
  | .imp f (.u32 s :: _) r =>
    if f = checkSend then
      (match r with
       | some [.variant 0 (some (.u64 n))] => (s, some n.toNat) :: q
       | _ => q)
    else if f = udpSend then (s, none) :: q
    else q
  | _ => q

/-- **The 0.2 UDP send theory.** -/
def sendTh : Protocol SendSt WEv := gated [] sendNext sendOk

/-- The permit `check-send` answers. -/
abbrev permit : Nat := 16

/-- **The concrete UDP send host**: `check-send` permits `16`; a permitted `send` sends every
datagram; any other `send` traps. -/
def sendImpl : Impl := fun p f a =>
  let q := p.foldl sendNext []
  if f = checkSend then some [okV (some (.u64 (BitVec.ofNat 64 permit)))]
  else if f = udpSend then
    (match a with
     | .u32 s :: d :: _ => (match countOf d with
       | some n => if ((lookup s q).getD none).any (n ≤ ·) then
           some [okV (some (.u64 (BitVec.ofNat 64 n)))] else none
       | none => none)
     | _ => none)
  else none

/-- `error-code.invalid-argument` in 0.2 and 0.3 (`eInval_wit`: the WIT case numbers). -/
abbrev eInval2 : Nat := 3
abbrev eInval3 : Nat := 2

/-- The literals are the case numbers of `invalid-argument` in the `error-code`s of the WIT. -/
theorem eInval_wit : eInval2 = WitImport.caseIdx Net.codes2 "invalid-argument" ∧
    eInval3 = WitImport.caseIdx Net.codes3 "invalid-argument" := by
  decide +kernel

end Silmaril.Wasi.Versions.SockMore

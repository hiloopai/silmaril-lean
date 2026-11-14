module

public import Silmaril.Machine.Process.IoSpecNet.Defs
public import Silmaril.Wasi.Versions.Udp.Defs
public import Silmaril.Wasi.Versions.P3.Defs
public import Silmaril.Wasi.Os.Defs

@[expose] public section

/-!
# The OS image of WASI sockets, over the extended events of `IoSpecNet`

`Silmaril.Wasi.Os` and `Silmaril.Wasi.Versions.P3` give the OS image of the stdout slice as LPS
events (`osEv`, `osStep3`). LPS has no socket events, so the socket slices had no image. With
`Silmaril.Machine.Process.IoSpecNet` (socket events `SockEv`, extended events `XEvent`, the network
`NetEnv`) they have one:

* **Socket images** (`List (SockEv Val)`), stateful along the theory states:
  - 0.2 TCP connect (`evTcp2`, state `TcpSt`): `finish-connect(s)` of a pending socket answered
    `ok(_)` or `error(k)` is `connect s addr none` / `connect s addr (some k)`;
  - 0.3 TCP connect (`evTcp3`): a `connect(s, addr)` that does not trap, the same;
  - 0.2 UDP (`evUdp2`, state `UdpSt`): `start-bind(s, _, addr)` answered `ok` is `bind s addr`;
    `receive` on a tied stream answered `ok(l)` is `recv addr d` for each datagram `d ∈ l`;
  - 0.3 UDP (`evUdp3`, state `Udp3St`): `bind`, and `receive` on a bound socket answered `ok(d)`;
  - name lookup: 0.2 `resolve-next-address` of a stream of `name` answered `ok(some a)`, and 0.3
    `resolve-addresses(name)` answered `ok(l)`, are `resolve name a` (`evDns2`, `evDns3`);
  - accept (`evAcc`, state `AccSt`): `remote-address` of an accepted socket of `local` answered
    `ok(peer)` is `accept c local peer` (`acceptTh` sees the peer only there).
  `imgRun next ev q t` runs an image along the theory state.
* **The network of the WASI environments**: `netOf N U P R` is the `NetEnv Val` with the
  connection outcomes `N`, the inbox `U`, the peers `P.peer` and the resolver `R`.
  `SockOk N l`: every socket event of `l` is admitted.
* **The extended image** (`xRun`): each WASI event emits its LPS events (embedded) followed by its
  socket events. `xImg2 ch` combines the stdout image `Os.osEv ch` with the 0.2 TCP and UDP
  images; `xImg3 ch` combines the 0.3 stdout image `osStep3 ch` with the 0.3 TCP and UDP images.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.SockOs

open Silmaril.Wasi
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasm.Component (Val)
open Silmaril.Machine.Process.IoSpecNet

/-- Extended events with WASI values. -/
abbrev XEv : Type := XEvent Val

/-- A WASI handle as an OS word. -/
def hw (s : BitVec 32) : Silmaril.Process.LPS.Word := s.setWidth 64

/-! ## Socket images -/

/-- The image of a theory run along the theory state. -/
def imgRun {S X : Type} (next : S → WEv → S) (ev : S → WEv → List X) : S → List WEv → List X
  | _, [] => []
  | q, e :: t => ev q e ++ imgRun next ev (next q e) t

/-- The outcome of a 0.2 `finish-connect` answer (`would-block` has none). -/
def outcome2Of : Option (List Val) → Option (Option Nat)
  | some [.variant 1 (some (.variant 8 none))] => none
  | some [.variant 0 (some (.record [.u32 _, .u32 _]))] => some none
  | some [.variant 1 (some (.variant k none))] => some (some k)
  | _ => none

/-- The outcome of a 0.3 `connect` answer. -/
def outcome3Of : Option (List Val) → Option (Option Nat)
  | some [.variant 0 none] => some none
  | some [.variant 1 (some (.variant k _))] => some (some k)
  | _ => none

/-- The socket events of a 0.2 TCP answer. -/
def evTcp2 (q : TcpSt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 s :: _) r =>
    if f = finishConnect then
      (match lookup s q, outcome2Of r with
       | some addr, some o => [.connect (hw s) addr o]
       | _, _ => [])
    else []
  | _ => []

/-- The socket events of a 0.3 TCP answer. -/
def evTcp3 (_ : Unit) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (sv :: addr :: _) r =>
    if f = connect3 then
      (match outcome3Of r with
       | some o => [.connect (hw (selfH [sv])) addr o]
       | none => [])
    else []
  | _ => []

/-- The socket events of a 0.2 UDP answer. -/
def evUdp2 (q : UdpSt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 s :: _ :: addr :: _) (some [.variant 0 none]) =>
    if f = udpBind then [.bind (hw s) addr] else []
  | .imp f (.u32 i :: _) (some [.variant 0 (some (.record l))]) =>
    if f = udpReceive then
      (match lookup i q.ins with
       | some addr => l.map (.recv addr)
       | none => [])
    else []
  | _ => []

/-- The socket events of a 0.3 UDP answer. -/
def evUdp3 (q : Udp3St) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 s :: addr :: _) (some [.variant 0 none]) =>
    if f = udpBind3 then [.bind (hw s) addr] else []
  | .imp f (.u32 s :: _) (some [.variant 0 (some d)]) =>
    if f = udpReceive3 then
      (match lookup s q with
       | some addr => [.recv addr d]
       | none => [])
    else []
  | _ => []

/-- The socket events of a 0.2 name lookup answer. -/
def evDns2 (q : DnsSt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 st :: _) (some [.variant 0 (some (.variant 1 (some a)))]) =>
    if f = resolveNext then
      (match lookup st q with
       | some name => [.resolve name a]
       | none => [])
    else []
  | _ => []

/-- The socket events of a 0.3 name lookup answer. -/
def evDns3 (_ : Unit) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (name :: _) (some [.variant 0 (some (.record l))]) =>
    if f = resolve3 then l.map (.resolve name) else []
  | _ => []

/-- The socket events of an accept answer. -/
def evAcc (q : AccSt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 c :: _) (some [.variant 0 (some a)]) =>
    if f = tcpRemote then
      (match lookup c q.acc with
       | some loc => [.accept (hw c) loc a]
       | none => [])
    else []
  | _ => []

/-! ## The network -/

/-- **The network of the WASI environments**: connection outcomes `N`, inbox `U`, peers `P`,
resolver `R`. -/
def netOf (N : Network) (U : Inbox) (P : Peers) (R : Resolver) : NetEnv Val := ⟨N, U, P.peer, R⟩

/-- Every socket event of the list is admitted by the network. -/
def SockOk (N : NetEnv Val) (l : List (SockEv Val)) : Prop := ∀ e ∈ l, e.Admits N

/-! ## The extended image -/

/-- **The extended image of a run**: per WASI event, its LPS events (embedded), then its socket
events. `stepA` is an LPS image with state `A`, `nextB`/`evB` a socket image with state `B`. -/
def xRun {A B : Type} (stepA : A → WEv → A × List Silmaril.Process.LPS.Event)
    (nextB : B → WEv → B) (evB : B → WEv → List (SockEv Val)) :
    A → B → List WEv → List XEv
  | _, _, [] => []
  | a, b, e :: t =>
    liftT (stepA a e).2 ++ (evB b e).map .sock ++ xRun stepA nextB evB (stepA a e).1 (nextB b e) t

/-- The LPS image of a run, with state. -/
def runA {A : Type} (stepA : A → WEv → A × List Silmaril.Process.LPS.Event) :
    A → List WEv → List Silmaril.Process.LPS.Event
  | _, [] => []
  | a, e :: t => (stepA a e).2 ++ runA stepA (stepA a e).1 t

/-- The 0.2 socket state: TCP and UDP. -/
abbrev Sock2St : Type := TcpSt × UdpSt

/-- The next 0.2 socket state. -/
def next2 (q : Sock2St) (e : WEv) : Sock2St := (tcpNext q.1 e, udpNext q.2 e)

/-- The 0.2 socket events: TCP, then UDP. -/
def ev2 (q : Sock2St) (e : WEv) : List (SockEv Val) := evTcp2 q.1 e ++ evUdp2 q.2 e

/-- The 0.3 socket state: UDP (the TCP slice has no state). -/
abbrev Sock3St : Type := Udp3St

/-- The 0.3 socket events: TCP, then UDP. -/
def ev3 (q : Sock3St) (e : WEv) : List (SockEv Val) := evTcp3 () e ++ evUdp3 q e

/-- **The extended OS image of a 0.2 run**: stdout on `ch`, TCP and UDP. -/
def xImg2 (ch : Silmaril.Process.LPS.Word) (t : List WEv) : List XEv :=
  xRun (fun (_ : Unit) e => ((), Silmaril.Wasi.Os.osEv ch e)) next2 ev2 () ([], {}) t

/-- **The extended OS image of a 0.3 run**: stdout on `ch` (`osStep3`), TCP and UDP. -/
def xImg3 (ch : Silmaril.Process.LPS.Word) (t : List WEv) : List XEv :=
  xRun (P3.osStep3 ch) udpNext3 ev3 {} [] t

end Silmaril.Wasi.Versions.SockOs

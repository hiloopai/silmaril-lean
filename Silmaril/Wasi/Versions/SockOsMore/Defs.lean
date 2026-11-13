module

public import Silmaril.Wasi.Versions.SockOs.Defs
public import Silmaril.Wasi.Versions.Accept3.Defs
public import Silmaril.Wasi.Versions.Udp3Conn.Defs

@[expose] public section

/-!
# The OS image of the pass-2/3 socket theories, over `IoSpecNet`

`Silmaril.Wasi.Versions.SockOs` gives socket images (`SockEv`, `imgRun`) of the TCP connect, UDP,
name lookup and 0.2 accept theories. This module adds images of:

* **0.3 accept** (`acc3Th P`, `Accept3`): `get-remote-address(c)` of a socket read from the
  listening stream of `local`, answered `ok(peer)`, is `accept c local peer`, as `evAcc` for
  0.2. The network admits it when `peer` is a peer of `local`.
* **0.2 UDP send** (`SockMore.sendTh`): `send(s, datagrams)` answered `ok(n)` is `send s d` for
  each of the first `n` datagrams.
* **0.3 UDP send** (`Udp3Conn.udpConnTh3`): `send(s, data, remote)` answered `ok` is
  `send s (data, remote)`.

`SockEv.Admits` admits every `send` (sending does not observe the network), so the two send
images are admitted for any network: they say which datagrams leave, not whether they arrive.
The TCP `send`/`receive` streams of 0.3 (`Tcp3Stream`) have no image: `SockEv` has no event for
stream data (only datagrams), and adding one would change `IoSpecNet`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.SockOsMore

open Silmaril.Wasi
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.SockOs (hw)
open Silmaril.Wasm.Component (Val)
open Silmaril.Machine.Process.IoSpecNet

/-- The socket events of a 0.3 accept answer. -/
def evAcc3 (q : Accept3.Acc3St) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 c :: _) (some [.variant 0 (some a)]) =>
    if f = Accept3.tcpRemote3 then
      (match lookup c q.acc with
       | some loc => [.accept (hw c) loc a]
       | none => [])
    else []
  | _ => []

/-- The socket events of a 0.2 UDP send answer. -/
def evSend2 (_ : SockMore.SendSt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 s :: .record ds :: _) (some [.variant 0 (some (.u64 n))]) =>
    if f = SockMore.udpSend then (ds.take n.toNat).map (.send (hw s)) else []
  | _ => []

/-- The socket events of a 0.3 UDP send answer. -/
def evSend3 (_ : Udp3Conn.UCSt) (e : WEv) : List (SockEv Val) :=
  match e with
  | .imp f (.u32 s :: data :: remote :: _) (some [.variant 0 none]) =>
    if f = udpSend3 then [.send (hw s) (.record [data, remote])] else []
  | _ => []

end Silmaril.Wasi.Versions.SockOsMore

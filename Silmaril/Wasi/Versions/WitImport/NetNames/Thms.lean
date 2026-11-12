module

public import Silmaril.Wasi.Versions.WitImport.NetTables.Defs
public import Silmaril.Wasi.Versions.Net.Defs
public import Silmaril.Wasi.Versions.Net3.Defs
public import Silmaril.Wasi.Versions.NetMore.Defs

/-!
# The hand-written `wasi:sockets` and `wasi:http` names are imported names

* `sock2_mem`: the 0.2 socket functions of `Silmaril.Wasi.Versions.Net` and `NetMore` (TCP
  connect, bind/listen/accept, UDP, name lookup) are functions of the imported
  `wasi:sockets@0.2.12`;
* `sock3_mem`: the 0.3 socket functions of `Net3` and `NetMore` (`[static]tcp-socket.create`,
  `connect`, `resolve-addresses`) are functions of the imported `wasi:sockets@0.3.2`;
  `sock3_async`: `connect` and `resolve-addresses` are the async ones (observed sync-lowered);
* `http2_mem`: the 0.2 HTTP functions of `Net` are functions of the imported `wasi:http@0.2.12`.

The 0.3 HTTP functions (`Silmaril.Wasi.Versions.Http3`) are not compared: `wasi:http@0.3.2` is not
imported (see `Silmaril.Wasi.Versions.WitImport.NetTables`).
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasi.Versions.Net

/-- The 0.2 socket functions of the hand-written theories are imported functions. -/
theorem sock2_mem : ∀ f ∈ [instanceNetwork, createTcp, startConnect, finishConnect, tcpBind,
    tcpListen, tcpAccept, tcpRemote, createUdp, udpBind, udpStream, udpReceive, resolve2,
    resolveNext], f ∈ names sock2T := by
  decide +kernel

/-- The 0.3 socket functions of the hand-written theories are imported functions. -/
theorem sock3_mem : ∀ f ∈ [create3, connect3, resolve3], f ∈ names sock3T := by
  decide +kernel

/-- Of these, `connect` and `resolve-addresses` are `async` in the WIT. -/
theorem sock3_async : [create3, connect3, resolve3].filter
    (fun f => (sock3T.lookup f).any (·.async)) = [connect3, resolve3] := by
  decide +kernel

/-- The 0.2 HTTP functions of the hand-written theory are imported functions. -/
theorem http2_mem : ∀ f ∈ [httpHandle, setAuthority, setPath, futGet, respStatus],
    f ∈ names http2T := by
  decide +kernel

end Silmaril.Wasi.Versions.WitImport

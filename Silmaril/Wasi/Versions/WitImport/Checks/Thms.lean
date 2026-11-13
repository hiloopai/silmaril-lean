module

public import Silmaril.Wasi.Versions.WitImport.Pick.Defs
public import Silmaril.Wasi.Versions.WitImport.NetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.Derived.Defs
public import Silmaril.Wasi.Versions.P2.World.Defs
public import Silmaril.Wasi.Versions.P3.Defs
public import Silmaril.Wasi.Versions.Net3.Thms
public import Silmaril.Wasi.Versions.NetMore.Defs

/-!
# Checks of the switched WASI definitions against the WIT import

Most hand-written WASI definitions are now *defined* from the imported WIT tables (tracks
`wf-p1-switch`, `wf-p2-switch`): `P2.cliImports`, `P2.fsImports`, `P3.wasiFns3`,
`P3.asyncFns3`, `P2.cliOk`, `P2.streamErrOk`, `P3.ok3`, `Random.ok2`/`ok3`, `Net.codes2`,
`Net.codes3`, `Net.e2to3`, `Net.e3to2`, `Net.ecV3`, `Net.webDown`, … Their member lists are
checked where they are defined (`P2.cliImports_eq`, `P3.wasiFns3_eq`, `P3.asyncFns3_eq`,
`Net.dns2Fns_eq`, `Net.udpImports_eq`, …) and the typing against the hand-written normal forms
(`P2.cliOk_eq_hand`, `P3.ok3_eq_hand`, `streamErr_eq`, …). The literal case numbers are checked
in `Silmaril.Wasi.Versions.Net3` (`Net.eWouldBlock_wit`, `Net.eConnRefused_wit`, …).

This module keeps the remaining checks that are not stated anywhere else, on the primary
definitions:

* `cliRun_wit`, `p2Command_wit`: the export `wasi:cli/run.run` of the 0.2 command slice is the
  imported one; `run3_wit`, `p3World_wit`: the same for 0.3.
* `udpFns_wit`, `acceptFns_wit`: the 0.2 UDP and bind/listen/accept functions of `NetMore`
  are the imported functions with these interface and function names.
* `isWouldBlock_wit`: `Net.isWouldBlock` (which matches the literal `8`) matches the case of
  `would-block` in the imported `error-code`.
* `httpCodes_len`, `eDnsTimeout_eq`: the HTTP `error-code` has 39 cases in both versions and
  `DNS-timeout` is case `0` (`Net.webDown` reads it from the WIT).

The `…W` wrapper definitions and the `…_eq_imported` theorems that used to live here and in
the former modules `WitImport.Alias` and `WitImport.Switch2` were removed in the cleanup round
(`docs/projects/wasm-wasi.md`, *wit: cleanup*). This module was `WitImport.Switch` until
An earlier step of that round, renamed since it holds only checks.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions

/-! ## The `run` exports -/

/-- The export `wasi:cli/run.run` (0.2) is the imported one. -/
theorem cliRun_wit : pick (names cli2T) [("wasi:cli/run", "run")] = [cliRun] := by
  decide +kernel

/-- **The WASI 0.2 command slice, with the imported export.** -/
theorem p2Command_wit :
    P2.p2Command = ⟨P2.p2Imports, {f | f ∈ pick (names cli2T) [("wasi:cli/run", "run")]}⟩ := by
  rw [cliRun_wit]
  simp only [P2.p2Command, World.mk.injEq, true_and]
  ext f; simp

/-- The export `wasi:cli/run@0.3.2.run` is the imported one. -/
theorem run3_wit : pick (names cli3T) [("wasi:cli/run", "run")] = [P3.run3] := by
  decide +kernel

/-- **The WASI 0.3 command slice, with the imported export.** -/
theorem p3World_wit :
    P3.p3World =
      ⟨P3.wasiFns3 ∪ P3.canonFns, {f | f ∈ pick (names cli3T) [("wasi:cli/run", "run")]}⟩ := by
  rw [run3_wit]
  simp only [P3.p3World, World.mk.injEq, true_and]
  ext f; simp

/-! ## The `NetMore` slices -/

/-- The 0.2 UDP functions of `NetMore` are the imported ones. -/
theorem udpFns_wit :
    (pick (names sock2T)
      [("wasi:sockets/udp-create-socket", "create-udp-socket"),
       ("wasi:sockets/udp", "[method]udp-socket.start-bind"),
       ("wasi:sockets/udp", "[method]udp-socket.stream"),
       ("wasi:sockets/udp", "[method]incoming-datagram-stream.receive")]).Perm
      [Net.createUdp, Net.udpBind, Net.udpStream, Net.udpReceive] := by
  decide +kernel

/-- The 0.2 bind/listen/accept functions of `NetMore` are the imported ones. -/
theorem acceptFns_wit :
    (pick (names sock2T)
      [("wasi:sockets/tcp", "[method]tcp-socket.start-bind"),
       ("wasi:sockets/tcp", "[method]tcp-socket.start-listen"),
       ("wasi:sockets/tcp", "[method]tcp-socket.accept"),
       ("wasi:sockets/tcp", "[method]tcp-socket.remote-address")]).Perm
      [Net.tcpBind, Net.tcpListen, Net.tcpAccept, Net.tcpRemote] := by
  decide +kernel

/-! ## `would-block` -/

theorem isWouldBlock_iff (r : Option (List Val)) :
    Net.isWouldBlock r = true ↔ r = some [.variant 1 (some (.variant 8 none))] := by
  unfold Net.isWouldBlock
  split <;> simp_all

/-- **`Net.isWouldBlock` matches the imported `would-block` case.** -/
theorem isWouldBlock_wit (r : Option (List Val)) :
    Net.isWouldBlock r = true ↔
      r = some [.variant 1 (some (.variant (caseIdx Net.codes2 "would-block") none))] := by
  rw [← Net.eWouldBlock_wit]
  exact isWouldBlock_iff r

/-! ## HTTP `error-code` -/

/-- The HTTP `error-code` has 39 cases in both versions (so `caseIdx` finds a case). -/
theorem httpCodes_len :
    (caseNames (findTy http2P.2 ⟨⟨"wasi", "http", some "0.2.12"⟩, "types"⟩
      ⟨.local, "error-code"⟩)).length = 39 ∧
    (caseNames (findTy http3P.2 ⟨⟨"wasi", "http", some "0.3.2"⟩, "types"⟩
      ⟨.local, "error-code"⟩)).length = 39 := by
  decide +kernel

/-- `DNS-timeout` is case `0` of the HTTP `error-code` in both versions. -/
theorem eDnsTimeout_eq : eDnsTimeout2W = 0 ∧ eDnsTimeout3W = 0 := by decide +kernel

end Silmaril.Wasi.Versions.WitImport

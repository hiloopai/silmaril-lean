module

public import Silmaril.Wasi.Versions.WitImport.KCert.Tokens.V2.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Tokens.V3.Thms
public import Silmaril.Wasi.Versions.WitImport.PickRest.Defs
public import Silmaril.Wasi.Versions.DnsOver.Defs
public import Silmaril.Wasi.Versions.HttpReqBody.Defs
public import Silmaril.Wasi.Versions.HttpBody3.Defs
public import Silmaril.Wasi.Versions.Random.Defs
public import Silmaril.Wasi.Versions.P2.World.Defs

@[expose] public section

/-!
# The switched socket, HTTP, `wasi:io` and `wasi:random` definitions, kernel-checked

`KSlices` ties `p2P`/`p3P` (the packages of the switched `cli`, `clocks` and `filesystem`
checks) to the kernel importer. This module does the same for every other definition of the
hand-written modules that the switch reads from the import: each theorem says that the
definition used by the downstream proofs is what the **kernel importer** (`kTableTok`,
`kDropsTok`, `kRPkgTok` of `KTokens`) computes from the tokens of the vendored files.

* **Function sets** (read from tables with `pick`): `P2.ioImports`, `P2.cliImports`,
  `P2.clockImports`, `P2.fsImports`, `P3.wasiFns3` with `P3.asyncFns3`, `Net.tcpImports`,
  `Net.httpImports`, `Net.tcp3Fns`, `Net.http3Fns`, `Net.udpImports`, `Net.udp3Fns`,
  `Net.dns2Fns`, `Net.dns3Fns`, `Net.bodyFns2`, `Net.bodyFns3`, `Net.req2Fns`, `Net.req3Fns`,
  `Random.rand2Fns`, `Random.rand3Fns`.
* **Definitions read from resolved packages**: the socket code lists `Net.codes2`,
  `Net.codes3`, the 0.3 name lookup codes `Net.dnsCodes3`, the 0.2 `stream-error` check
  `P2.streamErrOk`, the `wasi:io` result check `P2.ioResR`, the typing checks
  `Random.ok2`/`ok3`, and `DNS-timeout` of `Net.webDown`.
  Each is stated as a function of the package (`codes2Of`, …), equal by `rfl` to the
  definition on the evaluator's package, and applied to the kernel importer's package.

Each proof rewrites with the kernel track's `<x>_kernel_tokens` and closes by `rfl`.

What stays trusted is what `KTokens` states: the text glue `withHeader`/`demoteParamDocs`
inside `wit_src%`, and that dropping doc-comment tokens before parsing does not change a
package (not proved).

A Silmaril addition (track `wf-p3-switch-rest` of the WASI full workflow).
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)

/-! ## The vendored files of each package -/

/-- The files of `wasi:io` 0.2.12. -/
noncomputable abbrev io2Files : List (List Char) := [KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full]

/-- The files of `wasi:sockets` 0.2.12 with its dependencies. -/
noncomputable abbrev sock2Files : List (List Char) :=
  [KF.v2.sock.network.full, KF.v2.sock.instance_network.full, KF.v2.sock.tcp.full,
    KF.v2.sock.tcp_create_socket.full, KF.v2.sock.udp.full, KF.v2.sock.udp_create_socket.full,
    KF.v2.sock.ip_name_lookup.full, KF.v2.clocks.monotonic_clock.full,
    KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full,
    KF.v2.io.poll.full, KF.v2.io.streams.full]

/-- The files of `wasi:http` 0.2.12 with its dependencies. -/
noncomputable abbrev http2Files : List (List Char) :=
  [KF.v2.http.types.full, KF.v2.http.handler.full, KF.v2.clocks.monotonic_clock.full,
    KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full,
    KF.v2.io.poll.full, KF.v2.io.streams.full]

/-- The files of `wasi:random` 0.2.12. -/
noncomputable abbrev rand2Files : List (List Char) :=
  [KF.v2.rand.insecure_seed.full, KF.v2.rand.insecure.full, KF.v2.rand.random.full]

/-- The files of `wasi:sockets` 0.3.2 with its dependencies. -/
noncomputable abbrev sock3Files : List (List Char) :=
  [KF.v3.sock.types.full, KF.v3.sock.ip_name_lookup.full, KF.v3.clocks.monotonic_clock.full,
    KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full]

/-- The files of `wasi:http` 0.3.2 with its dependencies. -/
noncomputable abbrev http3Files : List (List Char) :=
  [KF.v3.http.worlds.full, KF.v3.http.types.full, KF.v3.clocks.monotonic_clock.full,
    KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full]

/-- The files of `wasi:random` 0.3.2. -/
noncomputable abbrev rand3Files : List (List Char) :=
  [KF.v3.rand.insecure_seed.full, KF.v3.rand.insecure.full, KF.v3.rand.random.full]

/-! ## Function sets from kernel-checked tables -/

/-- The set of the functions of `T` with the keys `keys`. -/
def pickSet (T : Table) (keys : List (String × String)) : Set FnName := {f | f ∈ pick (names T) keys}

theorem ioImports_kernel :
    (do
      let T ← kTableTok false false io2Files
      let D ← kDropsTok false io2Files
      pure ({f | f ∈ names T ++ D} : Set FnName)) = some P2.ioImports := by
  rw [io2T_kernel_tokens, io2D_kernel_tokens]; rfl

theorem tcpImports_kernel :
    (kTableTok false false sock2Files).map (pickSet · tcpKeys) = some Net.tcpImports := by
  rw [sock2T_kernel_tokens]; rfl

theorem udpImports_kernel :
    (kTableTok false false sock2Files).map (pickSet · udpKeys) = some Net.udpImports := by
  rw [sock2T_kernel_tokens]; rfl

theorem dns2Fns_kernel :
    (kTableTok false false sock2Files).map (pickSet · dns2Keys) = some Net.dns2Fns := by
  rw [sock2T_kernel_tokens]; rfl

theorem httpImports_kernel :
    (kTableTok false false http2Files).map (pickSet · httpKeys) = some Net.httpImports := by
  rw [http2T_kernel_tokens]; rfl

theorem bodyFns2_kernel :
    (do
      let H ← kTableTok false false http2Files
      let I ← kTableTok false false io2Files
      pure ({f | f ∈ pick (names H ++ names I) body2Keys} : Set FnName)) = some Net.bodyFns2 := by
  rw [http2T_kernel_tokens, io2T_kernel_tokens]; rfl

theorem req2Fns_kernel :
    (do
      let H ← kTableTok false false http2Files
      let I ← kTableTok false false io2Files
      pure (pickSet H httpKeys ∪ {f | f ∈ pick (names H ++ names I) req2Keys})) =
      some Net.req2Fns := by
  rw [http2T_kernel_tokens, io2T_kernel_tokens]; rfl

theorem tcp3Fns_kernel :
    (kTableTok true false sock3Files).map (pickSet · tcp3Keys) = some Net.tcp3Fns := by
  rw [sock3T_kernel_tokens]; rfl

theorem udp3Fns_kernel :
    (kTableTok true false sock3Files).map (pickSet · udp3Keys) = some Net.udp3Fns := by
  rw [sock3T_kernel_tokens]; rfl

theorem dns3Fns_kernel :
    (kTableTok true false sock3Files).map (pickSet · dns3Keys) = some Net.dns3Fns := by
  rw [sock3T_kernel_tokens]; rfl

theorem http3Fns_kernel :
    (kTableTok true true http3Files).map (pickSet · http3Keys) = some Net.http3Fns := by
  rw [http3T_kernel_tokens]; rfl

/-- The canonical built-ins of `bodyFns3` are appended by hand (they are not WIT functions). -/
theorem bodyFns3_kernel :
    (kTableTok true true http3Files).map
      (fun T => ({f | f ∈ pick (names T) body3Keys ++ [P3.cStreamRead, P3.cFutureRead]} :
        Set FnName)) = some Net.bodyFns3 := by
  rw [http3T_kernel_tokens]; rfl

/-- The canonical built-ins of `req3Fns` are appended by hand (they are not WIT functions). -/
theorem req3Fns_kernel :
    (kTableTok true true http3Files).map
      (fun T => pickSet T http3Keys ∪ {f | f ∈ pick (names T) req3Keys ++
        [P3.cStreamNew, P3.cStreamWrite, P3.cStreamDropW]}) = some Net.req3Fns := by
  rw [http3T_kernel_tokens]; rfl

theorem rand2Fns_kernel :
    (kTableTok false false rand2Files).map (fun T => ({f | f ∈ names T} : Set FnName)) =
      some Random.rand2Fns := by
  rw [rand2T_kernel_tokens]; rfl

theorem rand3Fns_kernel :
    (kTableTok true false rand3Files).map (fun T => ({f | f ∈ names T} : Set FnName)) =
      some Random.rand3Fns := by
  rw [rand3T_kernel_tokens]; rfl

/-! ### The `cli`, `clocks` and `filesystem` function sets (switched ) -/

/-- The files of `wasi:cli` 0.2.12 with `wasi:io`. -/
noncomputable abbrev cli2Files : List (List Char) :=
  [KF.v2.cli.environment.full, KF.v2.cli.exit.full, KF.v2.cli.run.full, KF.v2.cli.stdio.full,
    KF.v2.cli.terminal.full, KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full]

/-- The files of `wasi:clocks` 0.2.12 with `wasi:io`. -/
noncomputable abbrev clocks2Files : List (List Char) :=
  [KF.v2.clocks.monotonic_clock.full, KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full,
    KF.v2.io.error.full, KF.v2.io.poll.full, KF.v2.io.streams.full]

/-- The files of `wasi:filesystem` 0.2.12 with its dependencies. -/
noncomputable abbrev fs2Files : List (List Char) :=
  [KF.v2.fs.types.full, KF.v2.fs.preopens.full, KF.v2.clocks.monotonic_clock.full,
    KF.v2.clocks.wall_clock.full, KF.v2.clocks.timezone.full, KF.v2.io.error.full,
    KF.v2.io.poll.full, KF.v2.io.streams.full]

/-- The files of `wasi:cli` 0.3.2. -/
noncomputable abbrev cli3Files : List (List Char) :=
  [KF.v3.cli.environment.full, KF.v3.cli.exit.full, KF.v3.cli.run.full, KF.v3.cli.stdio.full,
    KF.v3.cli.terminal.full]

/-- The files of `wasi:clocks` 0.3.2. -/
noncomputable abbrev clocks3Files : List (List Char) :=
  [KF.v3.clocks.monotonic_clock.full, KF.v3.clocks.system_clock.full,
    KF.v3.clocks.timezone.full, KF.v3.clocks.types.full]

/-- The files of `wasi:filesystem` 0.3.2 with `wasi:clocks`. -/
noncomputable abbrev fs3Files : List (List Char) :=
  [KF.v3.fs.types.full, KF.v3.fs.preopens.full, KF.v3.clocks.monotonic_clock.full,
    KF.v3.clocks.system_clock.full, KF.v3.clocks.timezone.full, KF.v3.clocks.types.full]

theorem cliImports_kernel :
    (kTableTok false false cli2Files).map (pickSet · cliKeys) = some P2.cliImports := by
  rw [cli2T_kernel_tokens]; rfl

theorem clockImports_kernel :
    (kTableTok false false clocks2Files).map (fun T => ({f | f ∈ names T} : Set FnName)) =
      some P2.clockImports := by
  rw [clocks2T_kernel_tokens]; rfl

theorem fsImports_kernel :
    (do
      let T ← kTableTok false false fs2Files
      let D ← kDropsTok false fs2Files
      pure ({f | f ∈ pick (names T ++ D) fsKeys} : Set FnName)) = some P2.fsImports := by
  rw [fs2T_kernel_tokens, fs2D_kernel_tokens]; rfl

/-- The 0.3 slice and its `async` marks, from the three kernel-checked 0.3.2 tables. -/
theorem wasiFns3_kernel :
    (do
      let c ← kTableTok true false cli3Files
      let k ← kTableTok true false clocks3Files
      let f ← kTableTok true false fs3Files
      let T := c ++ k ++ f
      pure (pickSet T keys3,
        ({g | g ∈ (pick (names T) keys3).filter fun g => (T.lookup g).any (·.async)} :
          Set FnName))) = some (P3.wasiFns3, P3.asyncFns3) := by
  rw [cli3T_kernel_tokens, clocks3T_kernel_tokens, fs3T_kernel_tokens]; rfl

/-! ## Definitions from kernel-checked resolved packages -/

/-- The cases of 0.2 `wasi:sockets/network.error-code` in the package `P`. -/
def codes2Of (P : RPkg) : List String :=
  caseNames (findTy P.2 ⟨⟨"wasi", "sockets", some "0.2.12"⟩, "network"⟩ ⟨.local, "error-code"⟩)

/-- The cases of 0.3 `wasi:sockets/types.error-code` in the package `P`. -/
def codes3Of (P : RPkg) : List String :=
  caseNames (findTy P.2 ⟨⟨"wasi", "sockets", some "0.3.2"⟩, "types"⟩ ⟨.local, "error-code"⟩)

/-- The cases of 0.3 `ip-name-lookup.error-code` in the package `P`. -/
def dnsCodes3Of (P : RPkg) : List String := caseNames (findTy P.2 dnsI3 ⟨.local, "error-code"⟩)

/-- `stream-error` of `wasi:io/streams@0.2.12` in the package `P`. -/
def streamErrOf (P : RPkg) : Val → Bool :=
  tyOkR P.2 fuel ⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩ (.ref ⟨.local, "stream-error"⟩)

/-- The 0.2 `wasi:random` check in the package `P`. -/
def rand2OkOf (P : RPkg) (e : WEv) : Bool := witROk P e && len2 e

/-- The 0.3 `wasi:random` check in the package `P`. -/
def rand3OkOf (P : RPkg) (e : WEv) : Bool := witROk P e && len3 e

/-- `DNS-timeout` in the 0.3 HTTP `error-code` of the package `P`. -/
def dnsTimeout3Of (P : RPkg) : Nat :=
  caseIdx (caseNames (findTy P.2 ⟨⟨"wasi", "http", some "0.3.2"⟩, "types"⟩
    ⟨.local, "error-code"⟩)) "DNS-timeout"

theorem codes2_kernel : (kRPkgTok false false sock2Files).map codes2Of = some Net.codes2 := by
  rw [sock2P_kernel_tokens]; rfl

theorem codes3_kernel : (kRPkgTok true false sock3Files).map codes3Of = some Net.codes3 := by
  rw [sock3P_kernel_tokens]; rfl

theorem dnsCodes3_kernel :
    (kRPkgTok true false sock3Files).map dnsCodes3Of = some Net.dnsCodes3 := by
  rw [sock3P_kernel_tokens]; rfl

theorem streamErrOk_kernel :
    (kRPkgTok false false io2Files).map streamErrOf = some P2.streamErrOk := by
  rw [io2P_kernel_tokens]; rfl

/-- The resolved `wasi:io` result check of `P2.ioResR` (behind `handleAns`, `readyAns`,
`blockAns`, `unitAns`) in the package `P`. -/
def ioResOf (P : RPkg) (f : FnName) (r : Option (List Val)) : Bool :=
  match P.1.lookup f with
  | some (i, s) => resOkR P.2 i s r
  | none => false

theorem ioResR_kernel : (kRPkgTok false false io2Files).map ioResOf = some P2.ioResR := by
  rw [io2P_kernel_tokens]; rfl

theorem rand2Ok_kernel : (kRPkgTok false false rand2Files).map rand2OkOf = some Random.ok2 := by
  rw [rand2P_kernel_tokens]; rfl

theorem rand3Ok_kernel : (kRPkgTok true false rand3Files).map rand3OkOf = some Random.ok3 := by
  rw [rand3P_kernel_tokens]; rfl

/-- `Net.webDown` fails with the `DNS-timeout` of the kernel importer's 0.3 HTTP package. -/
theorem webDown_kernel :
    (kRPkgTok true true http3Files).map (fun P => (fun _ _ => .error (dnsTimeout3Of P) : Net.Web)) =
      some Net.webDown := by
  rw [http3P_kernel_tokens]; rfl

end Silmaril.Wasi.Versions.WitImport

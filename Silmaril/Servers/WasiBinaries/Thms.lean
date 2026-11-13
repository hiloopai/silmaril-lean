module

public import Silmaril.Servers.WasiBinaries.Defs
public import Silmaril.Servers.WasiCore.Thms
public import Silmaril.Servers.WasiExamples.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs
import Silmaril.Proofs.Servers.WasiBinaries.Hello

@[expose] public section

/-!
# The example `wasi:http` components as core modules: theorems

**Hello, proved.** `hello_runsTy`: the denotation of the core module of `hello` (built from
`tests/servers/wasi-http/{common,hello}.wat`) runs the body `hello` over typed hosts
(`Silmaril.Proofs.Servers.WasiBinaries.Hello`). Hence `helloBin_sat`: every exchange of the
module, read as a server over typed hosts, is `200 hello` with `content-type: text/plain`;
`helloBin_fresh`: with a fresh instance per request it refines the core's function server.
`helloBin_serveRef`, `helloBin_answers`: over the reference host it answers every request
`200 hello` (kernel evaluation with the request as a variable), so the specification is not
vacuous; `helloBin_live`: through `Machine.fresh_total`, every fair run of a host serving the
module answers every request, and its prefixes are traces of the function server.

**Checked over the reference host** (kernel evaluation of the denotations): `hello` on `/`,
`route` on `/`, `/hello` and `/missing`, `echo` on a `POST` of `abc`. These run the modules'
code, including `cabi_realloc` for the strings and lists the host answers.

**Open**: `Task.binRuns`, that the modules of `route` and `echo` run their bodies over typed
hosts; `binRuns_sat` gives their specifications under it. Unlike `hello`, their code branches on
host data of unbounded size (the bytes of the path, the chunks of the body), so the kernel
evaluation used for `hello` does not cover them.
-/

namespace Silmaril.Servers.WasiBinaries

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Exchange
open Silmaril.Servers.WasiHttp Silmaril.Servers.WasiCore Silmaril.Servers.WasiExamples
open Silmaril.Net.Http (Request Response)

/-- The denotation of a core module, as a strategy. -/
abbrev den (m : Silmaril.Wasm.Module) : Strategy (nsig proxyImports) (nsig proxyWorld.exports) :=
  ofBody (coreBody m binFuel)

/-! ## Hello -/

/-- **The core module of `hello` runs the body `hello`** over typed hosts. -/
theorem hello_runsTy : RunsTy (den helloCore) hello :=
  sim_runsTy Proofs.Servers.WasiBinaries.hello_sim

/-- **The module of `hello` answers `200 hello`**, over every typed host. -/
theorem helloBin_sat : Sat (wasiServerTy (den helloCore)) (each fun _ resp => resp = helloResp) :=
  (runsTy_refines hello_runsTy).sat hello_sat

/-- The module of `hello` refines the server of the constant function `200 hello`. -/
theorem helloBin_refines : Refines (wasiServerTy (den helloCore)) (ofFun fun _ => helloResp) :=
  fun _ ht => helloBin_sat _ ht

/-- **The module of `hello`, with a fresh instance per request, refines the core's function
server** of `200 hello`, however requests overlap. -/
theorem helloBin_fresh : (Exchange.fresh (wasiServerTy (den helloCore))).Refines
    (Servers.Model.ofFun fun _ => helloResp) :=
  Exchange.fresh_ofFun_refines helloBin_refines

/-! ## Liveness -/

/-- The module of `hello` over the reference host answers every request `200 hello`. -/
theorem helloBin_serveRef (q : Request) :
    serveRef (coreBody helloCore binFuel) q = some helloResp := by
  kernel_rfl

/-- **The module of `hello` is not vacuous**: every request answered `200 hello` is a trace over
typed hosts. -/
theorem helloBin_answers (q : Request) : [(q, helloResp)] ∈ wasiServerTy (den helloCore) :=
  serve_memTy (helloBin_serveRef q)

theorem helloBin_total : (freshM (wasiServerTy (den helloCore))).Total :=
  Machine.fresh_total fun r => ⟨helloResp, (), helloBin_answers r⟩

/-- **The module of `hello` is live**: a fair run of a host serving it with a fresh instance per
request answers every request it receives, and every prefix of the run is a trace of the
function server `200 hello`. -/
theorem helloBin_live (ρ : (freshM (wasiServerTy (den helloCore))).IRun ()) (hF : ρ.Fair) :
    ISen.answered ρ.obs ∧
      ∀ n, (Servers.Model.ofFun fun _ => helloResp).Tr (ρ.obs.prefix n) :=
  ⟨ρ.answered helloBin_total hF, fun n =>
    helloBin_fresh _ (by rw [Exchange.fresh_eq_perRequest]; exact ρ.prefix_tr n)⟩

/-! ## Checked over the reference host -/

theorem helloBin_ref : serveRef (coreBody helloCore binFuel) (getAt none (some (ascii "/"))) =
    some helloResp := by
  decide +kernel

theorem routeBin_ref_root : serveRef (coreBody routeCore binFuel) (getAt none (some (ascii "/"))) =
    some (Response.simple 200 (ascii "home")) := by
  decide +kernel

theorem routeBin_ref_hello :
    serveRef (coreBody routeCore binFuel) (getAt none (some (ascii "/hello"))) =
      some (Response.simple 200 (ascii "hello")) := by
  decide +kernel

theorem routeBin_ref_missing :
    serveRef (coreBody routeCore binFuel) (getAt none (some (ascii "/missing"))) =
      some (Response.simple 404 (ascii "not found")) := by
  decide +kernel

theorem echoBin_ref : serveRef (coreBody echoCore binFuel)
    ⟨⟨.post, ⟨none, none, some (ascii "/")⟩⟩, [], ascii "abc", []⟩ =
      some (Response.simple 200 (ascii "abc")) := by
  decide +kernel

/-! ## Route and echo -/

/-- **Open**: the core modules of `route` and `echo` run their bodies over typed hosts. -/
def Task.binRuns : Prop := RunsTy (den routeCore) route ∧ RunsTy (den echoCore) echo

/-- **Given `Task.binRuns`**, the modules of `route` and `echo` satisfy the examples'
specifications over typed hosts. -/
theorem binRuns_sat (ht : Task.binRuns) :
    Sat (wasiServerTy (den routeCore)) (each fun q resp => resp = routeResp q.target.pathWithQuery) ∧
      Sat (wasiServerTyB (den echoCore))
        (each fun q resp => resp = Response.simple 200 q.content ∨ resp = failResp) :=
  ⟨(runsTy_refines ht.1).sat route_sat, (runsTy_refinesB ht.2).sat echo_sat⟩

end Silmaril.Servers.WasiBinaries

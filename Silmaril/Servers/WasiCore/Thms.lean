module

public import Silmaril.Servers.WasiCore.Defs
public import Silmaril.Servers.WasiHttp.Thms
import Silmaril.Proofs.Servers.WasiCore.Sim

@[expose] public section

/-!
# Core modules of `wasi:http` components: theorems

* **`sim_runsTy`**: a body whose programs simulate those of `h` on typed answers runs `h` over
  typed hosts (`RunsTy`). This is how a core module's denotation `coreBody m fuel` is shown to
  run an example body (`Silmaril.Servers.WasiBinaries`).
* `sim_step`, `sim_pure`: a simulation, one import call at a time.
* `runs_runsTy`: running a body over every host is running it over typed hosts.
* `wasiServerTy_refines`: the reading over typed hosts refines the reading over every host.
* **`runsTy_refines`**, `runsTy_refinesB`: a strategy that runs `h` over typed hosts refines
  `h` read as a server, so every specification proved of the body (for every host) holds of the
  strategy over typed hosts.

Proofs in `Silmaril.Proofs.Servers.WasiCore.Sim`.
-/

namespace Silmaril.Servers.WasiCore

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.Exchange
open Silmaril.Wasm.Component (Val)

variable {X : Set FnName}

/-- **Simulation on typed answers gives runs over typed hosts.** -/
theorem sim_runsTy {d h : Body proxyImports X} (hs : ∀ q, Sim AnsTy (d q) (h q)) :
    RunsTy (ofBody d) h :=
  Proofs.Servers.WasiCore.sim_runsTy hs

/-- One import call of a simulation, by the next calls and the continuations, so that each side
can be computed on its own. -/
theorem sim_step {I : Set FnName} {T : FnName → Option (List Val) → Prop} {p p' : BProg I}
    {m : (nsig I).Op} (hp : next p = some m) (hp' : next p' = some m)
    (h : ∀ n, T m.1.1 n → Sim T (cont p n) (cont p' n)) : Sim T p p' :=
  Proofs.Servers.WasiCore.sim_step hp hp' h

/-- The end of a simulation. -/
theorem sim_pure {I : Set FnName} {T : FnName → Option (List Val) → Prop} {p p' : BProg I}
    {r : Option (List Val)} (hp : p = .pure r) (hp' : p' = .pure r) : Sim T p p' := by
  subst hp hp'; exact .pure r

theorem runs_runsTy {σ : Strategy (nsig proxyImports) (nsig X)} {h : Body proxyImports X}
    (hr : Runs σ h) : RunsTy σ h :=
  fun s hs _ => hr s hs

/-- The reading over typed hosts refines the reading over every host. -/
theorem wasiServerTy_refines (σ : Strategy (nsig proxyImports) (nsig X)) :
    Refines (wasiServerTy σ) (wasiServer σ) :=
  fun _ ⟨s, hs, _, hF⟩ => ⟨s, hs, fun _ _ => trivial, hF⟩

/-- **A strategy that runs a body over typed hosts refines it** as a server. -/
theorem runsTy_refines {σ : Strategy (nsig proxyImports) (nsig X)} {h : Body proxyImports X}
    (hr : RunsTy σ h) : Refines (wasiServerTy σ) (wasiServer (ofBody h)) :=
  fun _ ⟨s, hs, hT, hF⟩ => ⟨s, hr s hs hT, fun _ _ => trivial, hF⟩

/-- The same, reading request bodies. -/
theorem runsTy_refinesB {σ : Strategy (nsig proxyImports) (nsig X)} {h : Body proxyImports X}
    (hr : RunsTy σ h) : Refines (wasiServerTyB σ) (wasiServerB (ofBody h)) :=
  fun _ ⟨s, hs, hT, hF⟩ => ⟨s, hr s hs hT, fun _ _ => trivial, hF⟩

end Silmaril.Servers.WasiCore

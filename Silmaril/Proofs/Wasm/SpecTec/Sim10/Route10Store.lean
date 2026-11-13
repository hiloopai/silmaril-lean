module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Thms
public import Silmaril.Wasm.SpecTec.Sim10.Route.Defs

/-!
# `Fwd20` fails on storing configurations

`Task.composite10` is conditional on `Fwd20 hn tgt B Good`, the forward obligation of the
corrected wasm-2.0 script `simEnv20S B` on a set `Good` of V2 configurations. Round 3 discharged
it on `Good20C` (`fwd20_good20C`), which excludes stores. This module shows that the exclusion
is forced, at every builtins:

* **`not_fwd20_storeFn`**: if `Good` contains a configuration whose store has a storing function
  (`Sim20.StoreFix.StoreFn20`) and from which V2 steps, then `Fwd20 hn tgt B Good` is false. The
  image has no `simEnv20S` step at all (`Sim20.StoreFix.stuck_configV_storeFn20S`), so no
  non-empty run starts from it.
* `step_storeFnCfg`, `not_fwd20_storeFnCfg`: the hypothesis is satisfiable (`Sim20.StoreFix.storeFnCfg`). A store
  with one function whose body is `i32.store`, and code `nop`, steps in V2, and `Fwd20` fails on
  the singleton of that configuration.

So `composite10`'s condition cannot be discharged on any set that contains a reachable storing
configuration, for any V1 program that stores. The restatement is a 2.0 script whose `STORE`
case binds `Inn` (`Sim20.StoreFix.simEnv20T`, the `STORE` erratum).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (StoreFn20 IsStoreI stuck_configV_storeFn20S storeFnStore storeFnCfg
  storeFn_storeFnCfg)

variable {H : Type}

/-- **`Fwd20` fails on every set containing a storing configuration that V2 steps**, at every
builtins. -/
theorem not_fwd20_storeFn {hn : H → String} {host : V2.Execution.HostSemantics H} {B : Builtins}
    {Good : V2.Execution.Config H → Prop} {c c' : V2.Execution.Config H} (hg : Good c)
    (hs : StoreFn20 c.store) (h : V2.Execution.Step v2Profile host c c') :
    ¬ Fwd20 hn host B Good := by
  intro hF
  obtain ⟨w, hw, -⟩ := Relation.TransGen.head'_iff.1 (hF c c' hg h)
  exact stuck_configV_storeFn20S hs w hw

/-- V2 steps from it, by `nop`. -/
theorem step_storeFnCfg (host : V2.Execution.HostSemantics H) :
    V2.Execution.Step v2Profile host storeFnCfg ⟨storeFnStore, {}, []⟩ :=
  .pure .nop

/-- **`Fwd20` fails on the singleton of the storing configuration**, at every builtins. -/
theorem not_fwd20_storeFnCfg (hn : H → String) (host : V2.Execution.HostSemantics H)
    (B : Builtins) : ¬ Fwd20 hn host B (· = storeFnCfg) :=
  not_fwd20_storeFn rfl storeFn_storeFnCfg (step_storeFnCfg host)

end Silmaril.Wasm.SpecTec.Sim10

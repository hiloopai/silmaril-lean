module

public import Silmaril.Proofs.Wasm.FX.Logic.Host.Split

/-!
# Host calls in the every-run WasmFX logic: statements

Proofs in `Silmaril.Proofs.Wasm.FX.Logic.Host.Split`.

* **`stepFX'_split_host`**: every `StepFX' P host fx` step is a host-free step
  (`StepFX' P noHost fx`) or a host-call step (`HostStep`), through silmaril-lean's
  `Step.split_host`;
* **`TSafe.toH`**: a proof in the host-free logic holds under any host relation for code that
  reaches no host call (`NoHostCall`);
* **`noHostCall_of_allFX`**: code whose store has only FX functions (`AllFX`) reaches no host
  call, since host-free steps keep the store's functions;
* **`TSafe.behaviours_eq_host`**: exact behaviours under **every** host relation from a host-free
  proof, a store with only FX functions and one run.

Open: a rule for a call of a non-FX host function (its outcomes continuing in the evaluation
context), which needs the inversion of `decompose?` at FX code.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.Host

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX)
open Silmaril.Wasm.FX.Logic.EveryRun (TSafe)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {Q : PostFX H}

/-- **Every step is host-free or a host call.** -/
theorem stepFX'_split_host {c c' : ConfigFX H} (h : StepFX' P host fx c c') :
    StepFX' P noHost fx c c' ∨ HostStep P host fx c c' :=
  Silmaril.Proofs.Wasm.FX.Logic.Host.stepFX'_split_host h

/-- **A host-free proof holds with any host relation**, for code that reaches no host call. -/
theorem TSafe.toH {c : ConfigFX H} (h : TSafe P fx Q c) (hn : NoHostCall P host fx c) :
    TSafeH P host fx Q c :=
  Silmaril.Proofs.Wasm.FX.Logic.Host.tsafeH_of_tsafe h hn

/-- **A store with only FX functions makes no host call.** -/
theorem noHostCall_of_allFX {c : ConfigFX H} (hs : AllFX fx c.store) : NoHostCall P host fx c :=
  Silmaril.Proofs.Wasm.FX.Logic.Host.noHostCall_of_allFX hs

/-- **Exact behaviours under every host relation.** -/
theorem TSafe.behaviours_eq_host {c : ConfigFX H} {r₀ : Result} (h : TSafe P fx Q c)
    (hs : AllFX fx c.store) (hQ : ∀ s K f o, Q s K f o → o = OutcomeFX.ofResult r₀)
    (hm : r₀.toBehaviour ∈ behavioursFX' P host fx c) :
    behavioursFX' P host fx c = {r₀.toBehaviour} :=
  Silmaril.Proofs.Wasm.FX.Logic.Host.tsafe_behaviours_eq_host h hs hQ hm

/-- info: 'Silmaril.Wasm.FX.Logic.Host.stepFX'_split_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepFX'_split_host

end Silmaril.Wasm.FX.Logic.Host

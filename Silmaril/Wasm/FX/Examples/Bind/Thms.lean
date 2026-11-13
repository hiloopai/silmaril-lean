module

public import Silmaril.Proofs.Wasm.FX.Examples.Bind.Run
public import Silmaril.Proofs.Wasm.FX.Examples.Bind.Mem
public import Silmaril.Wasm.FX.Logic.Typed.Thms
public import Silmaril.Wasm.FX.Logic.Host.Thms

/-!
# The `cont.bind` program: exact behaviours

`bindProg` (`Silmaril.Wasm.FX.Examples.Bind.Defs`: bind the argument `2` to a continuation of
`add40`, resume it) is proved totally safe by the every-run logic with a function specification
of `add40` (`Silmaril.Proofs.Wasm.FX.Examples.Bind.Run`), and one run returns `42` (the existential
calculus, `Silmaril.Proofs.Wasm.FX.Examples.Bind.Mem`):

* **`bind_beh`**: at every profile, without host calls, exactly `{returns [42]}` under `StepFX'`;
* **`bind_beh_host`**: the same under **every** host relation (every function of the store is an
  FX function, so no run makes a host call: `Silmaril.Wasm.FX.Logic.Host`);
* `bind_behR_sub`: under typed `resume` (`StepFXR`) every behaviour returns `42` (an inclusion:
  the typed run is not constructed).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.Bind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXResumeT (behavioursFXR)
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

/-- **The `cont.bind` program**: at every profile, exactly one behaviour, returning `42`. -/
theorem bind_beh (P : Profile) :
    behavioursFX' P noHost bdFx bindProg = {.returns [Val.i32 42]} :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_behaviours_eq
    Silmaril.Proofs.Wasm.FX.Examples.Bind.bind_tsafe (fun _ _ _ _ h => h)
    Silmaril.Proofs.Wasm.FX.Examples.Bind.bind_mem

/-- The store of the `cont.bind` program has only FX functions. -/
theorem bd_allFX : Silmaril.Wasm.FX.Logic.Host.AllFX bdFx bdStore := by
  intro a fi hh hf hc
  rcases a with _ | _ | a
  · obtain rfl : fi = ⟨kitTypes.head!, bdM, .host 0⟩ := (Option.some.inj hf).symm
    obtain rfl : hh = 0 := by simpa using hc.symm
    simp [bdFx]
  · obtain rfl : fi = ⟨bdT, bdM, .host 1⟩ := (Option.some.inj hf).symm
    obtain rfl : hh = 1 := by simpa using hc.symm
    simp [bdFx]
  · simp [bdStore] at hf

/-- **The `cont.bind` program under every host relation**: exactly one behaviour, `42`. -/
theorem bind_beh_host (P : Profile) (host : HostSemantics Nat) :
    behavioursFX' P host bdFx bindProg = {.returns [Val.i32 42]} :=
  Silmaril.Wasm.FX.Logic.Host.TSafe.behaviours_eq_host (r₀ := .values [Val.i32 42])
    Silmaril.Proofs.Wasm.FX.Examples.Bind.bind_tsafe bd_allFX (fun _ _ _ _ h => h)
    Silmaril.Proofs.Wasm.FX.Examples.Bind.bind_mem

/-- Under typed `resume`, every behaviour of the `cont.bind` program returns `42`. -/
theorem bind_behR_sub (P : Profile) :
    behavioursFXR P noHost bdFx bindProg ⊆ {.returns [Val.i32 42]} :=
  Silmaril.Wasm.FX.Logic.Typed.TSafe.behavioursR_sub (r₀ := .values [Val.i32 42])
    Silmaril.Proofs.Wasm.FX.Examples.Bind.bind_tsafe (fun _ _ _ _ h => h)

/-- info: 'Silmaril.Wasm.FX.Examples.Bind.bind_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_beh

/-- info: 'Silmaril.Wasm.FX.Examples.Bind.bind_beh_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_beh_host

end Silmaril.Wasm.FX.Examples.Bind

module

public import Silmaril.Wasm.FX.Examples.EveryRun.Thms
public import Silmaril.Wasm.FX.Logic.Host.Thms

/-!
# The switch example under every host relation

`switch_beh` (`Silmaril.Wasm.FX.Examples.EveryRun`) is proved without host calls. Every function of
its store is an FX function, so no run calls the host (`Silmaril.Wasm.FX.Logic.Host`), and the
host-free proof gives the exact behaviour set under **every** host relation.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.Host

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.Numerics (Profile)

/-- The store of the switch example has only FX functions. -/
theorem sw_allFX : Silmaril.Wasm.FX.Logic.Host.AllFX swFx swStore := by
  intro a fi hh hf hc
  have ha : a < 3 := by
    have := (List.getElem?_eq_some_iff.mp hf).1
    simpa [swStore] using this
  simp only [swStore, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.some.injEq] at hf
  subst hf
  obtain rfl : hh = a := by simpa using hc.symm
  simp [swFx, ha]

/-- **Switching between two coroutines, under every host relation**: exactly `42`. -/
theorem switch_beh_host (P : Profile) (host : HostSemantics Nat) :
    behavioursFX' P host swFx switchProg = {.returns [Val.i32 42]} :=
  Silmaril.Wasm.FX.Logic.Host.TSafe.behaviours_eq_host (r₀ := .values [Val.i32 42])
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.switch_tsafe sw_allFX (fun _ _ _ _ h => h)
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.switch_mem

end Silmaril.Wasm.FX.Examples.Host

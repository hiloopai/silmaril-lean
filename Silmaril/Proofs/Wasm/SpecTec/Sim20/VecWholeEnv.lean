module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeEntry
public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecWhole.Core

/-!
# The shared integer library in `simEnv20V B` (kernel lookups)

The 24 definitions of `Equiv.NumEnvCore` are wasm-3.0's verbatim in the corrected script too,
looked up by `rfl`. Split from `VecWholePrims` for build time.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

variable {B : Builtins}

set_option maxRecDepth 100000 in
/-- **The 24 shared definitions of the integer library are those of `simEnv20V B`.** -/
theorem numEnvCore_simEnv20V : Equiv.NumEnvCore (simEnv20V B) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecWhole

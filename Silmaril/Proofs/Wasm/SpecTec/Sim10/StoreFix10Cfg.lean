module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreFix10Typed

/-!
# A storing 1.0 configuration is typed under the `STORE` erratum

`typed10T_storeFnCfg`: the configuration `storeFnCfg10` (a store holding one function whose body
is `i32.store`, empty frame, code `nop`) has an IL-typed image in `simEnv10T`, at every builtins
(kernel evaluation of the type checker).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config)
open Silmaril.Wasm.SpecTec.Sim (TypedV)

variable (B : Builtins)

/-! ## A storing configuration -/

/-- A store with one function, whose body is `i32.store` at offset 0. -/
def storeFnStore10 (H : Type) : Store H :=
  { funcs := [.wasm ⟨[], []⟩ {} ⟨⟨0⟩, [], [.intStore .i32 none ⟨0, 0⟩]⟩] }

/-- **A storing configuration**: that store, the empty frame, and code `nop`. -/
def storeFnCfg10 (H : Type) : Config H := ⟨storeFnStore10 H, ⟨[], {}⟩, [.source .nop]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The storing configuration is typed in the corrected script.** -/
theorem typed10T_storeFnCfg {H : Type} (hn : H → String) :
    Typed10 (simEnv10T B) hn (storeFnCfg10 H) :=
  ⟨300, by with_unfolding_all rfl⟩

end Silmaril.Wasm.SpecTec.Sim10.StoreFix

module

public import Silmaril.Wasm.Component.FXRes.ContValid.Defs
public import Silmaril.Wasm.Verify.Kernel.Defs
import Silmaril.Raw.Wasm.Component.Reference

/-!
# Validating the `cont` component: results

* `contShadow_valid` (kernel evaluation): the Core shadow of `contModule` passes the Core 3.0
  validator `validate?`;
* **`contComp_valid`**: the reference component validator accepts `contComp`
  (`ValidComponent` at the Component Model 2 feature gates, `core3Profile`), with the module type
  of `contModule` taken from its shadow (`contModuleTypeC?`; the component has a single core
  module). This checks the component's definitions, its canonical built-ins
  (`resource.new`/`rep`/`drop` of `cont`), the core instantiation wiring, the aliases of the FX
  exports `make` and `run` and the types of the lifts `make() -> own<cont>` and
  `run(own<cont>) -> u32` against the declared types of the FX functions. The FX bodies are
  not type-checked;
* `contCheckBad?_error`: with `make` declared at the wrong type the validator rejects the
  component, so the check is not vacuous.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContValid

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Component.FXRes.ContComp

theorem contShadow_valid : (Silmaril.Wasm.Validation.validate? contShadow).isSome = true := by
  decide +kernel

theorem contCheck?_ok : ∃ ct, contCheck? = .ok ct := by
  have h : (match contCheck? with | .ok _ => true | .error _ => false) = true := by
    decide +kernel
  revert h
  cases contCheck? with
  | ok ct => exact fun _ => ⟨ct, rfl⟩
  | error e => exact fun h => (Bool.false_ne_true h).elim

/-- **The reference validator accepts `contComp`.** -/
theorem contComp_valid :
    ∃ ct, ValidComponent Features.p2 core3Profile contModuleTypeC? contComp ct :=
  contCheck?_ok.imp fun _ h => check?_sound h

/-- **Negative check**: with `make` declared at `[i32] → [i32]`, the lift
`make() -> own<cont>` is rejected. -/
theorem contCheckBad?_error : ∃ e, contCheckBad? = .error e := by
  have h : (match contCheckBad? with | .ok _ => false | .error _ => true) = true := by
    decide +kernel
  revert h
  cases contCheckBad? with
  | ok ct => exact fun h => (Bool.false_ne_true h).elim
  | error e => exact fun _ => ⟨e, rfl⟩

end Silmaril.Wasm.Component.FXRes.ContValid

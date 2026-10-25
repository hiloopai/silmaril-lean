module

public import Silmaril.Wasm.Validation.Check.ValidateAssembly
public import Silmaril.Wasm.Validation.Check.AtomComplete
public import Silmaril.Wasm.Validation.Check.AtomicBBot
public import Silmaril.Wasm.Validation.Check.TyOkComplete
public import Silmaril.Wasm.Validation.Check.WfElems

@[expose] public section

/-! # Final assembly of `validate?` completeness

Discharges `hT` with `TyOk.check_complete` and `AtomicBBotComplete` with
`atomicB?_complete_bot`, leaving only `hE : ∀ C, C.Wf → ElemsOk C`.
-/

namespace Silmaril.Wasm.Validation

theorem tyOk_check_complete_all : ∀ Δ : TypeCtx, Δ.Ok → Δ.recs = [] → TyOkComplete Δ :=
  fun _ hΔ hr => TyOk.check_complete hΔ hr

theorem atomicBBotComplete : AtomicBBotComplete :=
  @fun _ _ hC hr htyOk htab helem _ _ _ _ _ h hlen hs hstk =>
    atomicB?_complete_bot hC hr htyOk htab helem h hlen hs hstk

section ValidateFinal

variable (hE : ∀ C : Context, C.Wf → ElemsOk C)

include hE in
theorem atomC_complete_of_elems : StepComplete.AtomComplete atomC :=
  atomC_complete_of tyOk_check_complete_all atomicBBotComplete hE

include hE in
theorem validate?_complete_of_elems {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    validate? m = some mt :=
  validate?_complete_of_atom tyOk_check_complete_all (atomC_complete_of_elems hE) h

include hE in
theorem validate?_isSome_iff_of_elems {m : Module} : (validate? m).isSome ↔ ModuleValid m :=
  validate?_isSome_iff_of_atom tyOk_check_complete_all (atomC_complete_of_elems hE)

/-- Decidability of module validity via `validate?`, relative to `hE`. -/
def decidableModuleValid_of_elems (m : Module) : Decidable (ModuleValid m) :=
  decidableModuleValid_of_atom tyOk_check_complete_all (atomC_complete_of_elems hE) m

end ValidateFinal

/-! ## Unconditional versions (`hE` discharged by `Context.wf_elemsOk`) -/

theorem atomC_complete : StepComplete.AtomComplete atomC :=
  atomC_complete_of_elems Context.wf_elemsOk

/-- **Completeness** of `validate?`. -/
theorem validate?_complete {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    validate? m = some mt :=
  validate?_complete_of_elems Context.wf_elemsOk h

theorem validate?_isSome_iff {m : Module} : (validate? m).isSome ↔ ModuleValid m :=
  validate?_isSome_iff_of_elems Context.wf_elemsOk

/-- Decidability of module validity via `validate?`. -/
def decidableModuleValid_validate (m : Module) : Decidable (ModuleValid m) :=
  decidableModuleValid_of_elems Context.wf_elemsOk m

instance (m : Module) : Decidable (ModuleValid m) := decidableModuleValid_validate m

end Silmaril.Wasm.Validation

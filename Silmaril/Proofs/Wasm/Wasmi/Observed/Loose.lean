module

public import Silmaril.Wasm.Wasmi.Observed.Defs
public import Silmaril.Wasm.Atlas.Variant.Thms

/-!
# The loose models contain the variants (proofs)

* `Ctx.mono`: the context closure is monotone in the quirk relation;
* `step_le`: a wasmi 0.40.0 step is a loose step (its Core steps are Core steps, its quirk
  steps are quirk steps in a context);
* `loose_le_all`, `loose200_le_all`: both per-version loose relations are contained in
  `LooseAll`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas Silmaril.Wasm.Atlas.Variant Silmaril.Wasm.Wasmi.Observed

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The context closure is monotone in the quirk relation. -/
theorem Ctx.mono {Q Q' : Config H → Config H → Prop} (hQ : ∀ c c', Q c c' → Q' c c')
    {c c' : Config H} (h : Ctx Q c c') : Ctx Q' c c' := by
  induction h with
  | base h => exact .base (hQ _ _ h)
  | instrs _ ih => exact .instrs ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

/-- A loose relation is monotone in the quirk relation. -/
theorem loose_mono_quirk {R Q Q' : Config H → Config H → Prop}
    (hQ : ∀ c c', Q c c' → Q' c c') {c c' : Config H} (h : loose R Q c c') :
    loose R Q' c c' :=
  h.imp id (Ctx.mono hQ)

/-- **A wasmi 0.40.0 step is a loose step.** -/
theorem step_le {c c' : Config H} (h : Silmaril.Wasm.Wasmi.Observed.Step P host c c') :
    Silmaril.Wasm.Wasmi.Observed.Loose.Step P host c c' :=
  h.imp (fun h => h.2) id

/-- The loose relation of wasmi 0.40.0 is contained in `LooseAll`. -/
theorem loose_le_all {c c' : Config H} (h : Silmaril.Wasm.Wasmi.Observed.Loose.Step P host c c') :
    LooseAll.Step P host c c' :=
  loose_mono_quirk (fun _ _ h => AnyQuirk.round h) h

/-- The loose relation of wasmi 2.0.0 is contained in `LooseAll`. -/
theorem loose200_le_all {c c' : Config H} (h : Silmaril.Wasm.Wasmi.Loose.Step P host c c') :
    LooseAll.Step P host c c' :=
  loose_mono_quirk (fun _ _ h => AnyQuirk.select h) h

end Silmaril.Proofs.Wasm.Wasmi.Observed

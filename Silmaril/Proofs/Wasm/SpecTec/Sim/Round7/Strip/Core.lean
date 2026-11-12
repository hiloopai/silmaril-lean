module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Strip.Step
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Strip.Pres

/-!
# Round 7: the Core stripping lemmas

For an export-blind host (`HostExportBlind`), Core's `Step` commutes with removing every export
(`stripConfig`):

* `step_strip`: `c → c'` gives `stripConfig c → stripConfig c'`;
* `step_of_strip`: every step from `stripConfig c` is the image of a step from `c`.

They combine `exRel_step` (export-equivalence is a simulation) with `stripped_step` (steps from
export-free configurations stay export-free), both in `Raw/…/Round7/Strip/`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}


/-- **Forward stripping**: for an export-blind host, a step `c → c'` gives the step
`stripConfig c → stripConfig c'`. -/
theorem step_strip {P : Profile} {host : HostSemantics H} (hb : HostExportBlind host)
    {c c' : Config H} (h : Step P host c c') : Step P host (stripConfig c) (stripConfig c') := by
  obtain ⟨d', hd', hrel⟩ := exRel_step hb h _ (exRel_stripConfig c)
  have hst : Stripped d' := stripped_step hb hd' (stripped_stripConfig c)
  have heq : stripConfig c' = d' := hrel.trans hst
  exact heq ▸ hd'

/-- **Backward stripping**: for an export-blind host, every step from `stripConfig c` is the
image of a step from `c`. -/
theorem step_of_strip {P : Profile} {host : HostSemantics H} (hb : HostExportBlind host)
    {c d' : Config H} (h : Step P host (stripConfig c) d') :
    ∃ c', Step P host c c' ∧ stripConfig c' = d' := by
  obtain ⟨c', hc', hrel⟩ := exRel_step hb h c (exRel_symm (exRel_stripConfig c))
  have hst : Stripped d' := stripped_step hb h (stripped_stripConfig c)
  exact ⟨c', hc', hrel.symm.trans hst⟩

end Silmaril.Wasm.SpecTec.Sim.Round7

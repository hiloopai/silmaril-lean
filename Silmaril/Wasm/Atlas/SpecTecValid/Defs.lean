module

public import Silmaril.Wasm.Atlas.SpecTec.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# The step charts on valid configurations

The SpecTec transition of `Atlas.SpecTec` is conditional on the two simulation conjuncts on a
fragment `D`. froze a satisfiable target over valid configurations,
`Round4.Task.wholeStepValid`; this module fixes the matching fragment.

* `SpecTecValid.Dom P host c`: `c` is valid and bounded (`Round4Int.Valid`) and every Core
  successor of `c` is bounded. The last clause is the forward conjunct's `Bounded c'` premise:
  `Bounded` is not preserved by Core (`Round4.not_bounded_preserved`), so the chart's domain
  excludes configurations whose next step leaves SpecTec's syntax (for example a memory growing
  to `2 ^ 32` bytes).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecValid

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec

/-- **The domain of the valid step chart**: valid, bounded, with bounded Core successors. -/
def Dom (P : Profile) {H : Type} (host : HostSemantics H) (c : Config H) : Prop :=
  Sim.Round4Int.Valid c ∧ ∀ c', Step P host c c' → Sim.Round4.Bounded c'

end Silmaril.Wasm.Atlas.SpecTecValid

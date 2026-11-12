module

public import Silmaril.Wasm.SpecTec.Sim.Round3.Defs

/-!
# Round 3 integration: the assembled reduction, and why it is vacuous

* `wholeStepBounded_of_open`: `Integrate.Task.wholeStepBounded` from `Round3.Open` at every
  injective encoding and finite host. It combines track fwd-mem's wider forward fragment
  (`FwdMem.wholeStepBounded_of_concrete3`, now on `Covered3 true`: loads and stores, with U2
  applied by its proof, bitwise SIMD and four more aggregate instructions from track
  fwd-simd-agg, `return_call_ref`), `instReftype` and `grow`, track configok's
  `result`, `funcinst`, `MemTyping`, `InstTyping` and `exnFields`, and the backward rules of
  tracks bwd-pure-step and bwd-read (already removed from `RemainingW`).
* `not_open`, `not_open_hyp`: `Open` is uninhabited for every encoding, host and profile, because
  `RefOk.ResidueCore` is (`RefOk.not_residueCore`, from track configok's
  `ConfigOk.not_typeTyping`). So the premise of `wholeStepBounded_of_open` is false and the
  theorem is vacuous; it records the shape of the reduction, not progress towards the target.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round3

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-- **`Integrate.Task.wholeStepBounded`, reduced to what round 3 leaves open.** -/
theorem wholeStepBounded_of_open
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Open hn host nd r) :
    Integrate.Task.wholeStepBounded :=
  FwdMem.wholeStepBounded_of_concrete3 fun H hn hinj host hfin nd r =>
    let ⟨hr, R, A, Rw, hrest⟩ := h H hn hinj host hfin nd r
    ⟨hr, RefOk.residue_builtins (RefOk.residueRest_of_core R),
      RefOk.extra_builtins (RefOk.extraRest_of_agg A), RefOk.bwdOpen_of_remaining Rw, hrest⟩

/-- **`Open` is uninhabited**: its `ResidueCore` conjunct is refuted. -/
theorem not_open {H : Type} (hn : H → String) (host : HostSemantics H) (nd : Bool)
    (r : RelaxedChoice) : ¬ Open hn host nd r :=
  fun h => RefOk.not_residueCore _ h.2.1

/-- **The premise of `wholeStepBounded_of_open` is false** (at the empty host type). -/
theorem not_open_hyp :
    ¬ (∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Open hn host nd r) := fun h =>
  not_open _ _ false {} (h Empty (fun e => e.elim) (fun e => e.elim) Integrate.emptyHost
    Integrate.hostFinite_emptyHost false {})

end Silmaril.Wasm.SpecTec.Sim.Round3

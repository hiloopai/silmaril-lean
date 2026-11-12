module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict.Defs

/-!
# Round 7: what separates REH from what is proved (round 6, pass 1)

`Round7.Task.wholeStepValidREH` differs from the proved `Round7.HostMods.StepValidREM` by two
hypotheses: `StripInj c` on the source, and `HostModsSub` on the host. This topic shows that
both gaps are real, and that they are linked.

* **`StripInj` is a real restriction on REH's domain.** `collideCfg` (in the proofs) is valid,
  in `BoundedSelE`, takes a step, and has two module instances that differ only in their
  export lists. So REM and REI say nothing there, while REH does.
* **Dropping `HostModsSub` alone does not give a run theorem.** `stripCloneHost` is finite,
  `HostOk` and export-blind. A call appends a copy of one of the calling store's function
  instances with its module's exports removed. Called at a store with one function instance
  whose module exports something (so `StripInj` holds for its modules), it returns a store
  whose modules collide. So a host that invents modules can break `StripInj` in one step, and
  a run theorem for such hosts needs REH without `StripInj` at the successors.

Definitions only; the proofs are in `Round7/REGap/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.REGap

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The stripped-cloning host**: a call diverges, or appends again one of the calling store's
function instances with its module's exports removed, and returns `trap`. -/
def stripCloneHost : HostSemantics H := fun _ s _ o =>
  o = .diverged ∨ ∃ fi ∈ s.funcs, o = .returned (HostStrict.cloneStore s (stripFI fi)) .trap

/-- **The modules of a store collide**: two module instances of its function instances differ
only in their export lists. A configuration over such a store fails `StripInj`
(`Round7.REGap.not_stripInj_of_collide`). -/
def StoreCollides (s : Store H) : Prop :=
  ∃ m₁ ∈ s.funcs.map FuncInst.module, ∃ m₂ ∈ s.funcs.map FuncInst.module,
    m₁ ≠ m₂ ∧ stripModule m₁ = stripModule m₂

end Silmaril.Wasm.SpecTec.Sim.Round7.REGap

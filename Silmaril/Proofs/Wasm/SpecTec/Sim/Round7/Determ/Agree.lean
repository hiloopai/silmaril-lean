module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Else
public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Determ.Prims
public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Thms

/-!
# Round 7, determination: `Round7.Task.envAgreeNE` from primitives that preserve `ExpFree`

On round 6's domain the image `configV hn c` is `ExpFree` (`Round7.ExpEnc.expFree_configV`, from
the `NoExports` part of `Round5.Target.BoundedSel`), and round 6's primitives leave `$utf8` to the
erratum (`Round7.BI_utf8`). So `Round7.Determ.sStepB_utf8Env_iff` gives the leaf as soon as the
primitives preserve `ExpFree` (`envAgreeNE_of_builtinsEF`), which they do at an export-blind host
(`Round7.Determ.builtinsEF_BI`). So the leaf holds (`envAgreeNE`), and
`Round7.Task.wholeStepValidREI` now follows from `Round7.Task.swapEquiv` alone
(`wholeStepValidREI_of_swapEquiv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **`Round7.Task.envAgreeNE`, given that round 6's primitives preserve `ExpFree` for
export-blind hosts.** -/
theorem envAgreeNE_of_builtinsEF
    (hEF : ∀ (H : Type) (hn : H → String) (host : HostSemantics H), HostExportBlind host →
      ∀ P : Profile, BuiltinsEF (Round4Int.BI P hn host)) : Task.envAgreeNE := by
  intro H hn _ host _ _ hb nd r c ts _ hsel w
  have hc : TypAgree.ExpFree (configV hn c) := ExpEnc.expFree_configV hn hsel.1.2
  exact sStepB_utf8Env_iff (hEF H hn host hb _) (Round7.BI_utf8 _ hn host) hc

/-- **`Round7.Task.envAgreeNE` holds**: on round 6's domain, at an export-blind host, SpecTec's
`Step` reads alike in `utf8Env B` and `simEnv B`, `otherwise` premises included. -/
theorem envAgreeNE : Task.envAgreeNE :=
  envAgreeNE_of_builtinsEF fun _ hn _ hb P => builtinsEF_BI P hn hb

/-- **`Round7.Task.wholeStepValidREI` from the other leaf alone.** -/
theorem wholeStepValidREI_of_swapEquiv (hS : Task.swapEquiv) : Task.wholeStepValidREI :=
  wholeStepValidREI_of_leaves hS envAgreeNE

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ

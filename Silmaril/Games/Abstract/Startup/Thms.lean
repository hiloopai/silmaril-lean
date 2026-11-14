module

public import Silmaril.Games.Abstract.Startup.Defs
public import Silmaril.Games.Abstract.Hiding.Thms
import Silmaril.Proofs.Games.Abstract.Startup.Basic
import Silmaril.Proofs.Games.Abstract.Startup.Counterexample

/-!
# Startup-sensitive and startup-erased observations: theorems

* `eq_iff_startPart_erased`: for startup-independent models (run behaviour
  after `ready` does not depend on the startup history), the model is
  determined by its startup part (what startup does, including failure)
  together with its startup-erased observation (run moves only).
* `erased_eq_of_eq`: the erased observation is coarser than the model.
* `exists_erased_eq_startPart_ne`: erasure forgets startup failure. `⊤`
  against the model without failures: both are startup-independent with
  equal erased observations, but their startup parts differ. An HTTP reading
  therefore has to keep failure separately, for example as
  `Servers.Observe.Obs.initFail`.
* `exists_erased_eq_startPart_eq_ne`: erasure forgets how runs depend on
  startup inputs. Two components that output their startup input, or its
  negation, have equal startup parts and equal erased observations but are
  different models. Neither is startup-independent, so that hypothesis cannot
  be dropped.
-/

public section

namespace Silmaril.Games.Abstract.Startup

universe u

variable {S G : Game.{u}} {R : Type u}

/-- Equal models have equal erased observations. -/
theorem erased_eq_of_eq {T U : TraceModel (Game.phased S G R)} (h : T = U) :
    erased T = erased U := h ▸ rfl

/-- For startup-independent models, the startup part and the erased
observation determine the model. -/
theorem eq_iff_startPart_erased {T U : TraceModel (Game.phased S G R)} (hT : StartupIndep T)
    (hU : StartupIndep U) : T = U ↔ startPart T = startPart U ∧ erased T = erased U :=
  Silmaril.Proofs.Games.Abstract.Startup.eq_iff hT hU

/-- Erasure forgets startup failure. -/
theorem exists_erased_eq_startPart_ne :
    ∃ (S G : Game.{0}) (R : Type) (T U : TraceModel (Game.phased S G R)),
      StartupIndep T ∧ StartupIndep U ∧ erased T = erased U ∧ startPart T ≠ startPart U :=
  open Silmaril.Proofs.Games.Abstract.Startup.Counterexample in
  ⟨S, G, Unit, ⊤, noFail, top_indep, noFail_indep, erased_top_eq, startPart_ne⟩

/-- Erasure forgets how runs depend on startup inputs. -/
theorem exists_erased_eq_startPart_eq_ne :
    ∃ (S G : Game.{0}) (R : Type) (T U : TraceModel (Game.phased S G R)),
      startPart T = startPart U ∧ erased T = erased U ∧ T ≠ U :=
  open Silmaril.Proofs.Games.Abstract.Startup.Counterexample in
  ⟨S, G, Unit, outF id, outF not, by rw [startPart_outF, startPart_outF], erased_outF_eq, outF_ne⟩

end Silmaril.Games.Abstract.Startup

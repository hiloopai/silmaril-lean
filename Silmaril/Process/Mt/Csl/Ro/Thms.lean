module

public import Silmaril.Process.Mt.Csl.Ro.Defs
import Silmaril.Proofs.Process.Mt.Csl.Ro

/-!
# Read-only sharing keeps the decomposition sound: what is proved

PROVED with no axioms beyond Lean's core (proofs in `Silmaril/Proofs/Process/Mt/Csl/Ro.lean`):

* `ro_agrees`: the runs of `roT U RO` keep agreeing with `RO`;
* `ro_reach`: from a start agreeing with `RO` and decomposed for `roT U RO` (`GInv`), every run
  of `U` is a run of `roT U RO`;
* **`ro_adequacy`**: from such a start, every run of `U` ends in a configuration that is `Good`
  for `roT U RO` (no fault, no race outside `RO`, the invariant, the postconditions), has no
  fault of `U`, and still agrees with `RO`.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Csl

variable {M A V : Type} {S : Store M A V} {U : TIsa S} {RO : Heap A V} {I : HProp A V}
  {Q : Nat → U.St → Heap A V → Prop}

/-- The runs of `roT U RO` keep agreeing with `RO`. -/
theorem ro_agrees {C C' : Cfg (roT U RO)} (r : Reach (roT U RO) C C') :
    S.Agrees RO C.mem → S.Agrees RO C'.mem :=
  Silmaril.Proofs.Process.Mt.Csl.ro_agrees r

/-- **Every run of `U` is a run of `roT U RO`** from a start agreeing with `RO` and decomposed
for `roT U RO`. -/
theorem ro_reach {C₀ C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (h0 : S.Agrees RO C₀.mem) (g : GInv (roT U RO) I Q (cfgRo RO C₀) hs hI)
    (r : Reach U C₀ C) : Reach (roT U RO) (cfgRo RO C₀) (cfgRo RO C) :=
  Silmaril.Proofs.Process.Mt.Csl.ro_reach h0 g r

/-- **Adequacy with read-only sharing.** -/
theorem ro_adequacy {C₀ C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (h0 : S.Agrees RO C₀.mem) (g : GInv (roT U RO) I Q (cfgRo RO C₀) hs hI)
    (r : Reach U C₀ C) :
    Good (roT U RO) I Q (cfgRo RO C) ∧ ¬ Fault U C ∧ S.Agrees RO C.mem :=
  Silmaril.Proofs.Process.Mt.Csl.ro_adequacy h0 g r

end Silmaril.Process.Mt.Csl

module

public import Silmaril.SSA.Peggy.Optimizer.Cyclic.Defs
public import Silmaril.SSA.Peggy.EPEG.Selection.Thms
import Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic.Admission
import Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic.Sound

public section

namespace Silmaril.SSA.Peggy.Optimizer.Cyclic

open PEG
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n : Nat}

theorem Admission.demandWellFounded {g : Graph P params results n 1}
    (admitted : Admission g) : WellFounded g.Demand :=
  g.demandWellFounded_of_check (demandRank admitted.phase) admitted.demands

/-- The independent structural checks establish the stronger paper guard. -/
theorem Admission.wellFormed {g : Graph P params results n 1}
    (admitted : Admission g) : g.WellFormed :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic.wellFormed admitted

variable {g : Graph P params results (n + 1) 1} {site : Fin (n + 1)}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}

theorem Match.rule_holds (found : Match g site) (wf : WellFounded g.Demand) :
    found.rule.Holds (g.denote m env wf) :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic.rule_holds found wf

theorem Match.classes_valid (found : Match g site) (wf : WellFounded g.Demand) :
    found.classes.Valid (g.denote m env wf) :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.Cyclic.classes_valid found wf

/-- The compacted candidate preserves every ordered partial result at every index.
The row certificate derives the candidate's equations from class-labelled edges. -/
theorem Result.sound (result : Result g) (m : Interpretation.{u,v,x} P)
    (env : Tuple m.Value params) (i : Index 1) :
    g.observe m (g.denote m env result.source.demandWellFounded) i =
      result.matched.extract.observe m
        (result.matched.extract.denote m env result.target.demandWellFounded) i :=
  EPEG.Selection.observe_sound_of_rows result.source.demandWellFounded
    (result.matched.classes_valid result.source.demandWellFounded) result.boundary
    (result.matched.rows result.target.phase) result.edges i

end Silmaril.SSA.Peggy.Optimizer.Cyclic

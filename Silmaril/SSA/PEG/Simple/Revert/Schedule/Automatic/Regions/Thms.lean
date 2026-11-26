module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Regions.Defs
public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Regions

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {roles : Roles P} {rank : DemandRank n l}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

/-- Graph-only discovery returns the existing checker equation on the
original table and the witness used by the finite-return theorems. -/
theorem discover_checked {budget : Nat} {found : Found g roles rank}
    (_ran : discover g roles rank budget = .ok found) :
    Schedule.check g found.plan found.inputs rank = some found.gate :=
  found.checked

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Regions

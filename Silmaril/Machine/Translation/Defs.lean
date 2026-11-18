module

public import Mathlib.Order.CompleteLattice.Basic

/-! # Translation relations between artifacts -/

@[expose] public section

namespace Silmaril.Machine.Translation

/-- Which source and target artifacts are related, independently of any
execution model, checker, or refinement claim. Mathlib's pointwise complete
lattice on functions gives inclusion as `≤`, union as join and intersection
as meet, including arbitrary joins and meets. -/
abbrev Relation.{u, v} (Src : Type u) (Tgt : Type v) := Src → Tgt → Prop

end Silmaril.Machine.Translation

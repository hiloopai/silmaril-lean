module

public import Silmaril.Machine.Region.X86.CFG.Defs
public import Silmaril.Semantics.Region.Tree.CFG.Defs

/-! # Optional flat-CFG observation of intrinsic byte rows

All outgoing pairs are retained; edge-list ordering and duplicate serialization
rows disappear. This adapter supplies no dominator tree or primitive tree-region
witness. It adds no graph prerequisite to the intrinsic byte relation.
-/

@[expose] public section
namespace Silmaril.Machine.Region.X86.CFG

def Row.flat (r : Row) : Silmaril.Semantics.Region.Tree.FlatCFG Nat where
  entry := r.entry
  internal := {l | r.Support l}
  exits := {l | l ∈ r.exits}
  successors a := {b | r.Edge a b}

end Silmaril.Machine.Region.X86.CFG

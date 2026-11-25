module

public import Silmaril.Machine.DecodeGraph.Defs
import Silmaril.Proofs.Machine.DecodeGraph.Laws

public section

namespace Silmaril.Machine.DecodeGraph

open scoped SetRel

open Silmaril.Parse.DecodeGraph

variable {Context Buffer Source Block : Type*}

theorem blocks_mono {first second : Graph Context Buffer Source} (h : first ⊆ second)
    (ends : Context → Nat → Source → Prop) (fuel : Nat) : blocks first ends fuel ⊆ blocks second ends fuel :=
  Proofs.blocks_mono h ends fuel

theorem path_bounds {decoder : Graph Context Buffer Source} {ends : Context → Nat → Source → Prop}
    {fuel input code endPos} (path : Path decoder ends fuel input code endPos) :
    0 < code.length ∧ code.length ≤ fuel ∧ input.pos + code.length ≤ endPos ∧ endPos ≤ input.stop :=
  Proofs.path_bounds path

theorem blocks_deterministic {decoder : Graph Context Buffer Source} (unique : Deterministic decoder)
    (ends : Context → Nat → Source → Prop) (fuel : Nat) : Deterministic (blocks decoder ends fuel) :=
  Proofs.blocks_deterministic unique ends fuel

theorem assembleBlocks_mono {first second : Graph Context Buffer (List Source)} (included : first ⊆ second)
    (assemble : IsBasicBlock Context Source Block) : assembleBlocks first assemble ⊆ assembleBlocks second assemble :=
  fun _ ⟨listing, decoded, assembled⟩ => ⟨listing, included decoded, assembled⟩

theorem rebase_comp {Input Base Intermediate Observation : Type*} (first : SetRel Input Intermediate)
    (second : SetRel Intermediate Base) (machine : Observed Base Observation) :
    rebase (first ○ second) machine = rebase first (rebase second machine) := SetRel.comp_assoc ..

/-- Observable refinement by inclusion on a shared base transports to the
new inputs. This statement alone does not imply availability of observations. -/
theorem rebase_mono {Input Base Observation : Type*} {first second : SetRel Input Base}
    {lower upper : Observed Base Observation} (adapters : first ⊆ second) (refines : lower ⊆ upper) :
    rebase first lower ⊆ rebase second upper := SetRel.comp_subset_comp adapters refines

/-- Horizontal composition of comparisons commutes with their vertical
composition. The two composites are equal as proofs of inclusion in the same
relation hom-poset, not as executable witnesses or traces. -/
theorem rebase_interchange {Input Base Observation : Type*} {first middle last : SetRel Input Base}
    {lower mid upper : Observed Base Observation}
    (firstAdapter : first ⊆ middle) (secondAdapter : middle ⊆ last)
    (firstModel : lower ⊆ mid) (secondModel : mid ⊆ upper) :
    (rebase_mono firstAdapter firstModel).trans (rebase_mono secondAdapter secondModel) =
      rebase_mono (firstAdapter.trans secondAdapter) (firstModel.trans secondModel) :=
  Subsingleton.elim _ _

/-- If every possible decoded input has an observation, the rebased machine
has an observation exactly on the domain of the adapter. -/
theorem dom_rebase_of_covered {Input Base Observation : Type*} (adapter : SetRel Input Base)
    (machine : Observed Base Observation) (available : adapter.cod ⊆ machine.dom) :
    (rebase adapter machine).dom = adapter.dom :=
  Proofs.dom_rebase_of_covered adapter machine available

end Silmaril.Machine.DecodeGraph

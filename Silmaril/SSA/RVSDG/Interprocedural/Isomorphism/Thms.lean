module

public import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Isomorphism.Bridge

public section

namespace Silmaril.SSA.RVSDG.Interprocedural

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args args' outs : Ports (Ty V S)} {past past' sigs sigs' : List (Ports (Ty V S))}
variable {fn : Function V S} {value : ValueSort V S} {members : List (Function V S)}

theorem LambdaTerm.renumbered_toGraph_iff (ids : Nat → Nat)
    (left : LambdaTerm Op args past fn) (right : LambdaTerm Op args' past' fn) :
    left.toGraph.Renumbered ids right.toGraph ↔ left.Renumbered ids right :=
  Isomorphism.Proofs.lambda_toGraph ids left right

theorem Lambda.renumbered_toTerm_iff (ids : Nat → Nat)
    (left : Lambda Op args past fn) (right : Lambda Op args' past' fn) :
    left.toTerm.Renumbered ids right.toTerm ↔ left.Renumbered ids right := by
  rw [← LambdaTerm.renumbered_toGraph_iff, left.toGraph_toTerm, right.toGraph_toTerm]

theorem DeltaTerm.renumbered_toGraph_iff (ids : Nat → Nat)
    (left : DeltaTerm Op args past value) (right : DeltaTerm Op args' past' value) :
    left.toGraph.Renumbered ids right.toGraph ↔ left.Renumbered ids right :=
  Isomorphism.Proofs.delta_toGraph ids left right

theorem Delta.renumbered_toTerm_iff (ids : Nat → Nat)
    (left : Delta Op args past value) (right : Delta Op args' past' value) :
    left.toTerm.Renumbered ids right.toTerm ↔ left.Renumbered ids right := by
  rw [← DeltaTerm.renumbered_toGraph_iff, left.toGraph_toTerm, right.toGraph_toTerm]

theorem PhiTerm.renumbered_toGraph_iff (ids : Nat → Nat)
    (left : PhiTerm Op args past members) (right : PhiTerm Op args' past' members) :
    left.toGraph.Renumbered ids right.toGraph ↔ left.Renumbered ids right :=
  Isomorphism.Proofs.phi_toGraph ids left right

theorem Phi.renumbered_toTerm_iff (ids : Nat → Nat)
    (left : Phi Op args past members) (right : Phi Op args' past' members) :
    left.toTerm.Renumbered ids right.toTerm ↔ left.Renumbered ids right := by
  rw [← PhiTerm.renumbered_toGraph_iff, left.toGraph_toTerm, right.toGraph_toTerm]

/-- In the current φ encoding each result reads the physical λ with the
same slot number. Fixing ordered results therefore fixes the member numbering. -/
theorem Phi.member_number_eq (left : Phi Op args past members) (right : Phi Op args' past' members)
    (ids : Fin members.length ≃ Fin members.length)
    (preservesResults : ∀ i, Address.rename (renameVertex ids) (left.resultOrigin i).address =
      (right.resultOrigin i).address) (i : Fin members.length) : ids i = i :=
  Isomorphism.Proofs.phi_number_eq left right ids preservesResults i

/-- Encoding preserves and reflects the proposed ω vertex map. -/
theorem OmegaTerm.renumberedBy_toGraph_iff (left : OmegaTerm Op args outs sigs)
    (right : OmegaTerm Op args outs sigs') (ids : Fin sigs.length ≃ Fin sigs'.length) :
    left.toGraph.RenumberedBy right.toGraph ids ↔ left.RenumberedBy right ids :=
  Isomorphism.Proofs.omega_toGraph left right ids

/-- Linearization preserves and reflects the same ω vertex map. -/
theorem Omega.renumberedBy_toTerm_iff (left : Omega Op args outs sigs) (right : Omega Op args outs sigs')
    (ids : Fin sigs.length ≃ Fin sigs'.length) :
    left.toTerm.RenumberedBy right.toTerm ids ↔ left.RenumberedBy right ids := by
  rw [← OmegaTerm.renumberedBy_toGraph_iff, left.toGraph_toTerm, right.toGraph_toTerm]

theorem OmegaTerm.isomorphic_toGraph_iff (left : OmegaTerm Op args outs sigs)
    (right : OmegaTerm Op args outs sigs') :
    left.toGraph.Isomorphic right.toGraph ↔ left.Isomorphic right :=
  exists_congr fun ids => left.renumberedBy_toGraph_iff right ids

theorem Omega.isomorphic_toTerm_iff (left : Omega Op args outs sigs) (right : Omega Op args outs sigs') :
    left.toTerm.Isomorphic right.toTerm ↔ left.Isomorphic right :=
  exists_congr fun ids => left.renumberedBy_toTerm_iff right ids

end Silmaril.SSA.RVSDG.Interprocedural

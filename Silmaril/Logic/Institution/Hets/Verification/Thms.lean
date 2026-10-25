module

public import Silmaril.Logic.Institution.Hets.Verification.Graph
import Silmaril.Proofs.Logic.Institution.Hets.Verification

@[expose] public section

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

namespace StrSpec

/-- **The verification semantics preserves model classes**: the models of a structured
specification are the models of its node in the development graph.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1
(PDF pages 19–21: "`Mod(SP) = Mod_S(O)`");
`mossakowski-2005-habilitation-hets` in `references.bib`, §5.5, Theorem 5.19 (printed page 137, PDF page 139). -/
theorem models_devGraph {S : Sign} (SP : StrSpec I S) :
    (devGraph I).models ⟨S, SP⟩ = SP.models :=
  Silmaril.Proofs.Logic.Institution.Hets.models_devGraph SP

/-- Entailment of a structured specification is the local implication at its node.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 11 (PDF page 9) and §8.1 (PDF page 19). -/
theorem entails_iff_localImpl {S : Sign} (SP : StrSpec I S) (Γ : Set (I.obj S).Sen) :
    (∀ φ ∈ Γ, SP.Entails φ) ↔ (devGraph I).LocalImpl ⟨S, SP⟩ Γ :=
  Silmaril.Proofs.Logic.Institution.Hets.entails_iff_localImpl SP Γ

/-- Refinement of structured specifications is a global theorem link along the identity
between their nodes.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5 (printed page 137,
PDF page 139: the verification semantics of views, `N₁ ⇢σ N₂`). -/
theorem refines_iff_globalThm {S : Sign} (SP₁ SP₂ : StrSpec I S) :
    SP₁.Refines SP₂ ↔ (devGraph I).GlobalThm ⟨S, SP₁⟩ ⟨S, SP₂⟩ (𝟙 S) :=
  Silmaril.Proofs.Logic.Institution.Hets.refines_iff_globalThm SP₁ SP₂


end StrSpec

end Silmaril.Logic.Institution

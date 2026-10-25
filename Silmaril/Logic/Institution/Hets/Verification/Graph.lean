module

public import Silmaril.Logic.Institution.Hets.Verification.Defs
import Silmaril.Proofs.Logic.Institution.Hets.VerificationLinks

@[expose] public section

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}

namespace StrSpec

/-- Links of the verification graph only come from immediate subterms, so the link relation is
well-founded. -/
theorem nodeLink_wf : WellFounded fun M N : Node I =>
    (nodeGlobalDef M N).Nonempty ∨ (∅ : Set (M.1 ⟶ N.1)).Nonempty ∨
      (nodeHidingDef M N).Nonempty := Silmaril.Proofs.Logic.Institution.Hets.nodeLink_wf

/-- Reduct along an identity. -/
theorem mod_obj_id {S : Sign} (n : (I.obj S).Mod) : (I.map (𝟙 S)).mod.obj n = n := by
  simp

/-- Reduct along `eqToHom` of a loop. -/
theorem mod_obj_eqToHom {S : Sign} (h : S = S) (n : (I.obj S).Mod) :
    (I.map (eqToHom h)).mod.obj n = n := by
  simp

theorem mod_obj_eqToHom_comp {S S' : Sign} (h : S = S) (τ : S ⟶ S') (n : (I.obj S').Mod) :
    (I.map (eqToHom h ≫ τ)).mod.obj n = (I.map τ).mod.obj n := by
  simp

theorem mod_obj_comp_eqToHom {S S' : Sign} (τ : S ⟶ S') (h : S' = S') (k : (I.obj S').Mod) :
    (I.map (τ ≫ eqToHom h)).mod.obj k = (I.map τ).mod.obj k := by
  simp

variable (I) in
/-- The development graph of all structured specifications over `I`.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1
(PDF pages 19–21); `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5 (printed
pages 136–137, PDF pages 138–139). -/
def devGraph : DevGraph I where
  Node := Node I
  sig N := N.1
  axioms := nodeAxioms
  globalDef := nodeGlobalDef
  localDef _ _ := ∅
  hidingDef := nodeHidingDef
  wf := nodeLink_wf


end StrSpec

end Silmaril.Logic.Institution

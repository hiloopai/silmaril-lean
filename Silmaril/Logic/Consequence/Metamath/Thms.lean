module

public import Silmaril.Logic.Consequence.Metamath.Defs
public import Silmaril.Logic.Consequence.Theory.Thms
import Silmaril.Proofs.Logic.Consequence.Metamath.Basic

/-!
# Metamath as consequence systems: laws, soundness and the theories

**Laws.** `derives_closed`, `theory_closed`, `entails_closed`, `theoryEntails_closed`: identity,
weakening and cut (`Structural.tarskiRules`).

**Substitution.** `derives_rewrite`: a syntax rewrite `f : X ⟶ Y` (a typecode map, an injective
variable renaming and a template for each syntax rule) maps derivable consequences to derivable
consequences. With `X = Y` this is the substitution law (`derives_substitutive`).
`theory_rewrite`: between theories, it is enough that `f` maps each axiom to a theorem (a
presentation morphism, as in `Metatheory.Metamath.gaxSetHom_iff`), so `theory X T` is
substitutive along the rewrites that map `T` into its theorems (`theory_substitutive`).

**Soundness, never completeness.** `derives_le_entails` and `theory_le_theoryEntails`:
derivability is below semantic consequence in Carneiro's models.

**The theories.** `zfTheory_le_zfcTheory`: ZF's consequences are ZFC's.
`setMMZFCTheory_sound_zfSet`: every theorem of set.mm's ZFC holds in the `ZFSet` model.
-/

@[expose] public section

namespace Silmaril.Consequence.Metamath

open Silmaril.Logic Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Metatheory (MMSig)

universe u w

theorem derives_closed (X : MMSig.{u}) :
    Structural.Closed Structural.tarskiRules (derives X) :=
  listSys_closed (Metatheory.Metamath.er X)

theorem theory_closed (X : MMSig.{u}) (T : Set (Sen X)) :
    Structural.Closed Structural.tarskiRules (theory X T) :=
  theorySys_closed (Metatheory.Metamath.er X) T

theorem entails_closed (X : MMSig.{u}) :
    Structural.Closed Structural.tarskiRules (entails.{u, w} X) :=
  roomSeq_closed (Metatheory.Metamath.room.{u, w} X)

theorem theoryEntails_closed (X : MMSig.{u}) (T : Set (Sen X)) :
    Structural.Closed Structural.tarskiRules (theoryEntails.{u, w} X T) :=
  roomTheorySeq_closed (Metatheory.Metamath.room.{u, w} X) T

theorem theory_empty (X : MMSig.{u}) : theory X ∅ = derives X :=
  theorySys_empty (Metatheory.Metamath.er X)

/-- **Soundness of Metamath derivability** for Carneiro's models. -/
theorem theory_le_theoryEntails (X : MMSig.{u}) (T : Set (Sen X)) :
    theory X T ≤ theoryEntails.{u, w} X T :=
  theoryOf_le_of_sound (Metatheory.Metamath.sound.{u, w} X) T

theorem derives_le_entails (X : MMSig.{u}) : derives X ≤ entails.{u, w} X :=
  fun Γ A d => (roomSeq_iff_entails (Metatheory.Metamath.room.{u, w} X) Γ A).2
    (Metatheory.Metamath.sound.{u, w} X _ A d)

/-- **Rewrites preserve derivability.** -/
theorem derives_rewrite {X Y : MMSig.{u}} (f : X ⟶ Y) {Γ : List (Sen X)} {A : Sen X}
    (h : derives X Γ A) :
    derives Y (Γ.map (Metatheory.Metamath.senMap f)) (Metatheory.Metamath.senMap f A) :=
  Proofs.Logic.Consequence.Metamath.derives_rewrite f h

/-- **Substitution law** of Metamath derivability, along syntax rewrites of a grammar. -/
theorem derives_substitutive (X : MMSig.{u}) :
    Structural.Substitutive (fun f : X ⟶ X => Metatheory.Metamath.senMap f) (derives X) :=
  fun f _ _ h => derives_rewrite f h

/-- **Rewrites between theories.** If `f` maps every axiom of `T` to a theorem of `T'`, it maps
consequences of `T` to consequences of `T'`. -/
theorem theory_rewrite {X Y : MMSig.{u}} (f : X ⟶ Y) {T : Set (Sen X)} {T' : Set (Sen Y)}
    (hT : ∀ t ∈ T, theory Y T' [] (Metatheory.Metamath.senMap f t))
    {Γ : List (Sen X)} {A : Sen X} (h : theory X T Γ A) :
    theory Y T' (Γ.map (Metatheory.Metamath.senMap f)) (Metatheory.Metamath.senMap f A) :=
  Proofs.Logic.Consequence.Metamath.theory_rewrite f hT h

/-- **Substitution law of a theory**, along the rewrites that map its axioms to its theorems. -/
theorem theory_substitutive (X : MMSig.{u}) (T : Set (Sen X)) :
    Structural.Substitutive
      (fun f : {f : X ⟶ X // ∀ t ∈ T, theory X T [] (Metatheory.Metamath.senMap f t)} =>
        Metatheory.Metamath.senMap f.1) (theory X T) :=
  fun f _ _ h => theory_rewrite f.1 f.2 h

/-- ZF's consequences are ZFC's. -/
theorem zfTheory_le_zfcTheory : zfTheory ≤ zfcTheory :=
  theorySys_mono_theory _ fun _ h => Logic.Metamath.Peano.ZF.ZF0_subset_ZFC h

/-- **The `ZFSet` model of set.mm's ZFC**: every theorem of `setMMZFCTheory` holds in it. -/
theorem setMMZFCTheory_sound_zfSet {N : Type (w + 1)} [DecidableEq N] [Infinite N]
    {A : Sen Metatheory.Metamath.setMM} (h : setMMZFCTheory [] A) :
    (Logic.Metamath.SetMM.model ZFSet.{w} N).Satisfies A.1 :=
  Metatheory.Metamath.zfc_sound A <| (Metatheory.Metamath.er Metatheory.Metamath.setMM).mono
    (Γ := Metatheory.Metamath.zfc ∪ {x | x ∈ ([] : List (Sen Metatheory.Metamath.setMM))})
    (Γ' := Metatheory.Metamath.zfc) (fun _ hx => Or.elim hx id fun h => by cases h) h

end Silmaril.Consequence.Metamath

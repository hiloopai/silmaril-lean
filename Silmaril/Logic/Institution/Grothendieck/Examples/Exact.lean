module

public import Silmaril.Logic.Institution.Grothendieck.Amalgamation
public import Silmaril.Logic.Institution.Examples.Comorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

/-!
# Exactness of the comorphisms `PL → FOL` and `EQ → FOL`

The model translations are isomorphisms of model categories (a first-order structure over a
translated signature is exactly a valuation, respectively an algebra), so every naturality
square is a pullback.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory Limits Examples

universe u₁ v₁ u₂ v₂ w m₁ m₂

/-! ### Exactness from invertible model translations -/

/-- A functor with a strict two-sided inverse is an isomorphism in `Cat`. -/
theorem Cat.isIso_ofFunctor_of_inverse {C D : Cat.{m₁, m₂}} (F : C ⥤ D) (G : D ⥤ C)
    (h₁ : F ⋙ G = 𝟭 C) (h₂ : G ⋙ F = 𝟭 D) : @IsIso Cat.{m₁, m₂} _ C D (Cat.Hom.ofFunctor F) :=
  ⟨⟨Cat.Hom.ofFunctor G, Cat.Hom.ext h₁, Cat.Hom.ext h₂⟩⟩

/-- A comorphism whose model translations are all isomorphisms of categories is exact: each
naturality square has two parallel isomorphisms, hence is a pullback.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: exactness of a comorphism as a pullback condition on the naturality squares of its model
translation). -/
theorem Inst.CoHom.exact_of_isIso {A : Inst.{u₁, v₁, w, m₁, m₂}} {B : Inst.{u₂, v₂, w, m₁, m₂}}
    (f : Inst.CoHom A B) (h : ∀ S, @IsIso Cat.{m₁, m₂} _ (B.I.obj (f.Φ.obj S)).Mod (A.I.obj S).Mod
      (Cat.Hom.ofFunctor (f.ρ.app S).mod)) : f.Exact := by
  intro S S' σ
  have := h S
  have := h S'
  refine IsPullback.of_vert_isIso ⟨Cat.Hom.ext ?_⟩
  exact (congrArg Corridor.mod (f.ρ.naturality σ)).symm

/-! ### `PL → FOL` -/

namespace Examples.PLtoFOL

/-- Homomorphisms between first-order structures over `sig P` are unique (there are no sorts). -/
instance homSubsingleton (P : Type) (M N : FOL.Structure (sig P)) : Subsingleton (M ⟶ N) :=
  ⟨fun f g => by
    obtain ⟨f₀, _, _⟩ := f
    obtain ⟨g₀, _, _⟩ := g
    obtain rfl : @f₀ = @g₀ := funext fun s => s.elim
    rfl⟩

/-- Every first-order structure over `sig P` is the expansion of its valuation. -/
theorem expansion_valuation {P : Type} (M : FOL.Structure (sig P)) :
    expansion P (valuation M) = M := by
  obtain ⟨⟨c, o⟩, r⟩ := M
  obtain rfl : c = fun s => PEmpty.elim s := funext fun s => s.elim
  obtain rfl : @o = fun {_ _ _} op _ => PEmpty.elim op := by
    funext n w s op
    exact op.elim
  refine congrArg (FOL.Structure.mk _) ?_
  funext n w rr args
  obtain ⟨⟨rfl⟩, p⟩ := rr
  obtain rfl : w = Fin.elim0 := fin0_funext _ _
  obtain rfl : args = fun j => j.elim0 := fin0_funext _ _
  rfl

/-- The inverse of the model translation `FOL(sig P) ⥤ PL(P)`: expand a valuation. -/
def modInv (P : Type) : PL.Model P ⥤ FOL.Structure (sig P) where
  obj v := expansion P v.val
  map h := ⟨fun s => s.elim, fun o _ => o.elim, fun r _ hr => h.down r.2 hr⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Expanding the valuation of a structure gives back the structure. -/
theorem mod_comp_modInv (P : Type) : mod P ⋙ modInv P = 𝟭 _ :=
  CategoryTheory.Functor.ext expansion_valuation (fun _ _ _ => Subsingleton.elim _ _)

/-- The valuation of the expansion of a valuation is that valuation. -/
theorem modInv_comp_mod (P : Type) : modInv P ⋙ mod P = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

end Examples.PLtoFOL

/-! ### `EQ → FOL` -/

namespace Examples.EQtoFOL

/-- Homomorphisms of first-order structures are determined by their carrier maps. -/
theorem structureHom_ext {Sg : FOL.Signature} {M N : FOL.Structure Sg} {f g : M ⟶ N}
    (h : f.map = g.map) : f = g := by
  obtain ⟨f₀, _, _⟩ := f
  obtain ⟨g₀, _, _⟩ := g
  obtain rfl : f₀ = g₀ := h
  rfl

/-- Carrier maps of a homomorphism conjugated by `eqToHom`s are conjugated by casts. -/
theorem eqToHom_comp_map {Sg : FOL.Signature} {M M' N N' : FOL.Structure Sg} (e : M' = M)
    (f : M ⟶ N) (e' : N = N') (s : Sg.S) (x : M'.carrier s) :
    (eqToHom e ≫ f ≫ eqToHom e').map s x =
      cast (congrArg (fun K : FOL.Structure Sg => K.carrier s) e')
        (f.map s (cast (congrArg (fun K : FOL.Structure Sg => K.carrier s) e) x)) := by
  subst e e'
  rfl

/-- Every first-order structure over `sig Sg` is the expansion of its algebra. -/
theorem expansion_toAlgebra {Sg : EQ.Signature} (M : FOL.Structure (sig Sg)) :
    expansion M.toAlgebra = M := by
  obtain ⟨A, r⟩ := M
  refine congrArg (FOL.Structure.mk A) ?_
  funext n w rr
  exact rr.elim

/-- The inverse of the model translation `FOL(sig Sg) ⥤ EQ(Sg)`: expand an algebra. -/
def modInv (Sg : EQ.Signature) : EQ.Algebra Sg ⥤ FOL.Structure (sig Sg) where
  obj A := expansion A
  map h := ⟨h.map, h.map_op, fun r _ _ => r.elim⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Expanding the algebra of a structure gives back the structure. -/
theorem mod_comp_modInv (Sg : EQ.Signature) : mod Sg ⋙ modInv Sg = 𝟭 _ := by
  refine CategoryTheory.Functor.ext expansion_toAlgebra (fun M N h => structureHom_ext ?_)
  funext s x
  exact (eqToHom_comp_map (expansion_toAlgebra M) h (expansion_toAlgebra N).symm s x).symm

/-- The algebra of the expansion of an algebra is that algebra. -/
theorem modInv_comp_mod (Sg : EQ.Signature) : modInv Sg ⋙ mod Sg = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

end Examples.EQtoFOL

/-- The comorphism `PL → FOL` is exact.

Source: exactness of comorphisms as in
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.2,
Definition 4.9 (pullback form). -/
theorem plToFol_exact : plToFol.Exact :=
  plToFol.exact_of_isIso fun P =>
    Cat.isIso_ofFunctor_of_inverse (plToFol.ρ.app P).mod (PLtoFOL.modInv P)
      (PLtoFOL.mod_comp_modInv P) (PLtoFOL.modInv_comp_mod P)

/-- The comorphism `EQ → FOL` is exact.

Source: exactness of comorphisms as in
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.2,
Definition 4.9 (pullback form); the comorphism is Goguen–Roşu's Example 4.3(5),
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §4. -/
theorem eqToFol_exact : eqToFol.Exact :=
  eqToFol.exact_of_isIso fun Sg =>
    Cat.isIso_ofFunctor_of_inverse (eqToFol.ρ.app Sg).mod (EQtoFOL.modInv Sg)
      (EQtoFOL.mod_comp_modInv Sg) (EQtoFOL.modInv_comp_mod Sg)

end Silmaril.Logic.Institution

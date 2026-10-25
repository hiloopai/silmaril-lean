module

public import Silmaril.Logic.Metamath.Category.Basic
public import Silmaril.Logic.Metamath.Category.Lattice
public import Silmaril.Logic.Metamath.Grammar.Correspondence
public import Silmaril.Logic.Metatheory.Conservative

@[expose] public section

/-!
# Grammatical axiom sets as inference systems

Every grammatical axiom set is an inference system whose conclusions are its
well-formed tree assertions.

* `GAxSet.toPropSystems` sends `X` to the proposition-valued system of tree
  derivability and a morphism to its translation of assertions. It is a
  functor because morphisms act as identity and composition on well-formed
  assertions. It is not faithful: templates of rules that no well-formed
  assertion reaches are invisible to it (`GAxSet.not_faithful_toPropSystems`).
* `GAxSet.toInferenceSystemCat` lands in `InferenceSystemCat` through the
  coherent systems (`PropSystems.toCoherent`): one derivation per derivable
  conclusion.
* `GAxSet.proofSystem X` keeps proofs relevant (derivations are tree proofs).
  A morphism maps proofs from the axioms of `X` to proofs from the translated
  axioms node by node (`GAxSet.Hom.proofMap`). A proof-relevant functor
  into `Y`'s own proofs would need a canonical form of cut elimination and is
  not provided.

On the string side, flattening is a morphism of proposition-valued systems
from tree derivability to string derivability from the syntax axioms and the
flattened axioms (`GAxSet.flattenHom`). For an unambiguous grammar it reflects
derivability (`GAxSet.flattenHom_conservative`), so morphisms also transport
string theorems of flattened assertions (`GAxSet.Hom.map_derivable_flatten`).
`Silmaril.Logic.Metamath.Category.Strings` makes string derivability a functor
on objects with unambiguous grammars, naturally isomorphic to tree
derivability.
-/

namespace Silmaril.Logic.Metamath.GAxSet

open CategoryTheory Grammar Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.InferenceSystemCat

universe u v

variable {X Y Z : GAxSet.{u}}

/-- Tree derivability of `X` as a proposition-valued inference system on its
well-formed tree assertions. -/
def propSystem (X : GAxSet.{u}) : PropSystems.{u} where
  Conclusion := TWFAssertion X.G
  Derivation A := TDerivable X.G X.axioms A.1

/-- The translation of well-formed assertions along a morphism. -/
def propMap (f : X ⟶ Y) : propSystem X ⟶ propSystem Y where
  map A := ⟨f.assertion A.1, f.wellFormed A.2⟩
  mapDerivation {A} h := f.map_derivable A.1 A.2 h

@[simp] theorem propMap_map_val (f : X ⟶ Y) (A : TWFAssertion X.G) :
    ((propMap f).map A).1 = f.assertion A.1 := rfl

/-- Grammatical axiom sets as proposition-valued inference systems. -/
def toPropSystems : GAxSet.{u} ⥤ PropSystems.{u} where
  obj := propSystem
  map := propMap
  map_id _ := PropSystems.hom_ext (funext fun A => Subtype.ext (Rewrite.id_assertion A.2))
  map_comp _ _ :=
    PropSystems.hom_ext (funext fun A => Subtype.ext (Rewrite.comp_assertion _ _ A.2))

@[simp] theorem propMap_id (X : GAxSet.{u}) : propMap (𝟙 X) = 𝟙 (propSystem X) :=
  toPropSystems.map_id X

theorem propMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) : propMap (f ≫ g) = propMap f ≫ propMap g :=
  toPropSystems.map_comp f g

@[simp] theorem toPropSystems_derivation (X : GAxSet.{u}) (A : TWFAssertion X.G) :
    (toPropSystems.obj X).Derivation A ↔ TDerivable X.G X.axioms A.1 := Iff.rfl

/-- Grammatical axiom sets in `InferenceSystemCat`, with one derivation of
each derivable conclusion. -/
def toInferenceSystemCat : GAxSet.{u} ⥤ InferenceSystemCat.{u, v} :=
  toPropSystems ⋙ PropSystems.toCoherent.{u, v} ⋙ coherentInclusion

theorem toInferenceSystemCat_provable (X : GAxSet.{u}) (A : TWFAssertion X.G) :
    (toInferenceSystemCat.{u, v}.obj X).Provable A ↔ TDerivable X.G X.axioms A.1 :=
  PropSystems.toCoherent_provable.{u, v} (propSystem X) A

@[simp] theorem toInferenceSystemCat_map_map (f : X ⟶ Y) (A : TWFAssertion X.G) :
    ((toInferenceSystemCat.{u, v}.map f).map A).1 = f.assertion A.1 := rfl

/-- The proof-relevant inference system of `X`: its derivations are tree
proofs from the axioms. -/
def proofSystem (X : GAxSet.{u}) : InferenceSystemCat.{u, u} where
  Conclusion := TWFAssertion X.G
  Derivation A := TProof X.G X.axioms A.1

theorem proofSystem_provable (X : GAxSet.{u}) (A : TWFAssertion X.G) :
    (proofSystem X).Provable A ↔ TDerivable X.G X.axioms A.1 :=
  ⟨fun ⟨d⟩ => ⟨d⟩, fun ⟨d⟩ => ⟨d⟩⟩

/-- The proof-relevant system of the translated axioms of a morphism. -/
def imageProofSystem (f : X ⟶ Y) : InferenceSystemCat.{u, u} where
  Conclusion := TWFAssertion Y.G
  Derivation A := TProof Y.G (f.assertion '' X.axioms) A.1

/-- A morphism maps tree proofs from the axioms of `X` to tree proofs from the
translated axioms. -/
noncomputable def Hom.proofMap (f : X ⟶ Y) : proofSystem X ⟶ imageProofSystem f where
  map A := ⟨f.assertion A.1, f.wellFormed A.2⟩
  mapDerivation {A} p :=
    ⟨f.dummies A.2 p.1, (f.assertion_extend A.2 p.1) ▸ f.mapTDerivation p.2⟩

/-- String derivability of `X`: string assertions derivable from the syntax
axioms and the flattened logical axioms. -/
def stringSystem (X : GAxSet.{u}) : PropSystems.{u} where
  Conclusion := Assertion X.C X.V
  Derivation A := Derivable (X.G.axioms X.axioms) A

/-- Flattening, as a morphism from tree derivability to string derivability. -/
def flattenHom (X : GAxSet.{u}) : propSystem X ⟶ stringSystem X where
  map A := A.1.flatten X.G
  mapDerivation h := TDerivable.flatten h

/-- For an unambiguous grammar, flattening reflects derivability. -/
theorem flattenHom_conservative (hG : X.G.Unambiguous) :
    PropSystems.Conservative (flattenHom X) :=
  fun A h => (tderivable_iff_derivable hG X.wf A.2).2 h

/-- A morphism out of an axiom set with an unambiguous grammar transports string
theorems of flattened well-formed assertions. -/
theorem Hom.map_derivable_flatten (f : X ⟶ Y) (hG : X.G.Unambiguous)
    {A : TAssertion X.L X.C X.V} (hA : A.WellFormed X.G)
    (h : Derivable (X.G.axioms X.axioms) (A.flatten X.G)) :
    Derivable (Y.G.axioms Y.axioms) ((f.assertion A).flatten Y.G) :=
  (f.map_derivable A hA ((tderivable_iff_derivable hG X.wf hA).2 h)).flatten

end Silmaril.Logic.Metamath.GAxSet

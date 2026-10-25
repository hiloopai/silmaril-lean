module

public import Silmaril.Logic.Metatheory.InferenceSystemCat.Fixed
public import Silmaril.Logic.Metatheory.InferenceSystemCat.Soundness
public import Silmaril.Logic.Metatheory.ArithmeticSoundness

@[expose] public section

/-!
# Systems with a chosen arithmetic base

`System B` equips a formal system with an injective interpretation of the
conclusions of a specified base `B`, and an explicit translation of its proofs.
For arithmetic instances `B` is Robinson Q. The generic construction also works
with another specified base; it does not assert that an arbitrary `B` is Q.

Arrows commute with the chosen interpretation on both formulas and proofs.
Arithmetic truth, effective coding, and induction are additional data and properties,
not consequences of merely admitting a base interpretation.
-/

namespace Silmaril.Logic.Metatheory.ArithmeticSystems

open CategoryTheory InferenceSystemCat

universe u v

/-- A formal system containing a specified proof-relevant base interpretation. -/
structure System (B : InferenceSystemCat.{u, v}) where
  inference : InferenceSystemCat.{u, v}
  base : B ⟶ inference
  faithfulSyntax : Function.Injective base.map

namespace System

variable {B : InferenceSystemCat.{u, v}}

/-- An interpretation preserving the chosen arithmetic syntax and base proofs. -/
structure Hom (S T : System B) where
  inference : S.inference ⟶ T.inference
  commutes : S.base ≫ inference = T.base

@[ext] theorem Hom.ext {S T : System B} {f g : Hom S T}
    (h : f.inference = g.inference) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (System B) where
  Hom := Hom
  id S := ⟨𝟙 S.inference, Category.comp_id _⟩
  comp f g := ⟨f.inference ≫ g.inference, by
    rw [← Category.assoc, f.commutes, g.commutes]⟩
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

/-- Forget the chosen arithmetic interpretation. -/
def forget : System B ⥤ InferenceSystemCat.{u, v} where
  obj := System.inference
  map := Hom.inference
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The chosen base proof translations form a natural transformation. -/
def baseInterpretation : (Functor.const (System B)).obj B ⟶ forget where
  app := System.base
  naturality {S T} f := by
    change 𝟙 B ≫ T.base = S.base ≫ f.inference
    rw [Category.id_comp]
    exact f.commutes.symm

instance : (forget (B := B)).Faithful where
  map_injective := Hom.ext

/-- Exactly the base-commuting ambient arrows lift to structured arrows. -/
theorem lift_iff {S T : System B} (f : S.inference ⟶ T.inference) :
    (∃ g : S ⟶ T, forget.map g = f) ↔ S.base ≫ f = T.base := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.commutes
  · intro h
    exact ⟨⟨f, h⟩, rfl⟩

theorem Hom.commutes_map {S T : System B} (f : S ⟶ T) (a : B.Conclusion) :
    f.inference.map (S.base.map a) = T.base.map a :=
  congrArg (fun k : B ⟶ T.inference => k.map a) f.commutes

/-- Commutation remembers which base proof was chosen, not just provability. -/
theorem Hom.commutes_derivation {S T : System B} (f : S ⟶ T)
    (a : B.Conclusion) (d : B.Derivation a) :
    HEq (f.inference.mapDerivation (S.base.mapDerivation d)) (T.base.mapDerivation d) :=
  InferenceSystemCat.hom_congr_derivation f.commutes a d

/-- Even if the ambient interpretation is not injective, its arithmetic restriction is. -/
theorem Hom.arithmetic_injective {S T : System B} (f : S ⟶ T) :
    Function.Injective (f.inference.map ∘ S.base.map) := by
  intro a b h
  apply T.faithfulSyntax
  simpa only [Function.comp_apply, f.commutes_map] using h

private theorem mapDerivation_heq {S T : InferenceSystemCat.{u, v}} (f : S ⟶ T)
    {a b : S.Conclusion} (h : a = b) {d : S.Derivation a} {e : S.Derivation b}
    (hd : HEq d e) : HEq (f.mapDerivation d) (f.mapDerivation e) := by
  cases h
  cases hd
  rfl

/-- The equality of arithmetic conclusions transports the target proof fiber. -/
def Hom.fragmentMap {S T : System B} (f : S ⟶ T) (a : B.Conclusion)
    (d : S.inference.Derivation (S.base.map a)) : T.inference.Derivation (T.base.map a) :=
  cast (congrArg T.inference.Derivation (f.commutes_map a)) (f.inference.mapDerivation d)

theorem Hom.fragmentMap_heq {S T : System B} (f : S ⟶ T) (a : B.Conclusion)
    (d : S.inference.Derivation (S.base.map a)) :
    HEq (f.fragmentMap a d) (f.inference.mapDerivation d) := cast_heq _ _

/-- Restrict proofs to the common arithmetic conclusions of the base. -/
def fragment : System B ⥤ Fixed.{u, v} B.Conclusion where
  obj S := ⟨fun a => S.inference.Derivation (S.base.map a)⟩
  map f := f.fragmentMap
  map_id S := by
    funext a d
    rfl
  map_comp f g := by
    funext a d
    apply eq_of_heq
    exact ((f ≫ g).fragmentMap_heq a d).trans
      ((g.fragmentMap_heq a (f.fragmentMap a d)).trans
        (mapDerivation_heq g.inference (f.commutes_map a).symm
          (f.fragmentMap_heq a d))).symm

/-- The arithmetic fragment embeds naturally into the full inference system. -/
def fragmentInclusion : fragment (B := B) ⋙ Fixed.inclusion ⟶ forget where
  app S := { map := S.base.map, mapDerivation := fun d => d }
  naturality {S T} f := by
    apply InferenceSystemCat.hom_ext
    · intro a
      exact (f.commutes_map a).symm
    · intro a d
      exact f.fragmentMap_heq a d

/-- Restrict further to a selected sentence type or syntactic hierarchy fragment.
The fragment predicate and its classification come from the caller's language. -/
def sentenceFragment (α : Type u) (sentence : α → B.Conclusion) :
    System B ⥤ Fixed.{u, v} α where
  obj S := ⟨fun a => S.inference.Derivation (S.base.map (sentence a))⟩
  map f a := f.fragmentMap (sentence a)
  map_id S := by
    funext a d
    exact congrArg (fun k : fragment.obj S ⟶ fragment.obj S => k (sentence a) d)
      (fragment.map_id S)
  map_comp {S T U} f g := by
    funext a d
    exact congrArg (fun k : fragment.obj S ⟶ fragment.obj U => k (sentence a) d)
      (fragment.map_comp f g)

/-- The base itself, with its identity interpretation. -/
def baseSystem (B : InferenceSystemCat.{u, v}) : System B :=
  ⟨B, 𝟙 B, Function.injective_id⟩

/-- Every base proof has its specified interpretation in every object. -/
def fromBase (S : System B) : baseSystem B ⟶ S := ⟨S.base, Category.id_comp _⟩

theorem fromBase_unique (S : System B) (f : baseSystem B ⟶ S) :
    f = fromBase S := by
  apply Hom.ext
  simpa [baseSystem, fromBase] using f.commutes

/-- The base object is initial, including uniqueness on proof translations. -/
def baseIsInitial : CategoryTheory.Limits.IsInitial (baseSystem B) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom fromBase fromBase_unique

instance : CategoryTheory.Limits.HasInitial (System B) := baseIsInitial.hasInitial

/-- Change the specified base along an injective, proof-preserving embedding. -/
def rebase {C : InferenceSystemCat.{u, v}} (e : B ⟶ C)
    (he : Function.Injective e.map) : System C ⥤ System B where
  obj S := ⟨S.inference, e ≫ S.base, S.faithfulSyntax.comp he⟩
  map f := ⟨f.inference, by rw [Category.assoc, f.commutes]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Changing the chosen base leaves the full proof translation unchanged. -/
theorem rebase_forget {C : InferenceSystemCat.{u, v}} (e : B ⟶ C)
    (he : Function.Injective e.map) : rebase e he ⋙ forget = forget := rfl

/-- Inclusion of common arithmetic derivability, independent of an ambient map. -/
def ArithmeticExtension (S T : System B) : Prop :=
  ∀ a, S.inference.Provable (S.base.map a) → T.inference.Provable (T.base.map a)

theorem arithmeticExtension_refl (S : System B) : ArithmeticExtension S S :=
  fun _ h => h

theorem ArithmeticExtension.trans {S T U : System B}
    (hST : ArithmeticExtension S T) (hTU : ArithmeticExtension T U) :
    ArithmeticExtension S U := fun a h => hTU a (hST a h)

theorem transport {S T : System B} (f : S ⟶ T) {a : B.Conclusion}
    (h : S.inference.Provable (S.base.map a)) : T.inference.Provable (T.base.map a) := by
  rw [← f.commutes_map a]
  exact map_provable f.inference h

theorem arithmeticExtension_of_hom {S T : System B} (f : S ⟶ T) :
    ArithmeticExtension S T := fun _ => transport f

/-- Arithmetic extension supplies proof translations on the common fragment;
choice does not make them canonical or recover the full ambient interpretation. -/
theorem arithmeticExtension_iff_fragment_hom (S T : System B) :
    ArithmeticExtension S T ↔ Nonempty (fragment.obj S ⟶ fragment.obj T) := by
  constructor
  · intro h
    exact ⟨fun a d => Classical.choice (h a ⟨d⟩)⟩
  · rintro ⟨f⟩ a ⟨d⟩
    exact ⟨f a d⟩

/-- Relative interpretability respects the specified arithmetic base. -/
def Interpretable (S T : System B) : Prop := Nonempty (S ⟶ T)

theorem interpretable_refl (S : System B) : Interpretable S S := ⟨𝟙 S⟩

theorem Interpretable.trans {S T U : System B}
    (hST : Interpretable S T) (hTU : Interpretable T U) : Interpretable S U := by
  obtain ⟨f⟩ := hST
  obtain ⟨g⟩ := hTU
  exact ⟨f ≫ g⟩

/-- Conservativity reflects derivability along the full conclusion translation. -/
def Conservative {S T : System B} (f : S ⟶ T) : Prop :=
  Complete S.inference T.inference f.inference.map

theorem Conservative.comp {S T U : System B} {f : S ⟶ T} {g : T ⟶ U}
    (hf : Conservative f) (hg : Conservative g) : Conservative (f ≫ g) :=
  fun a h => hf a (hg (f.inference.map a) h)

theorem Conservative.arithmetic_iff {S T : System B} {f : S ⟶ T}
    (hf : Conservative f) (a : B.Conclusion) :
    S.inference.Provable (S.base.map a) ↔ T.inference.Provable (T.base.map a) := by
  constructor
  · exact transport f
  · intro h
    apply hf (S.base.map a)
    rwa [f.commutes_map a]

/-- Standard arithmetic truth is supplied by a genuine arithmetic semantics. -/
def ArithmeticSound (A : ArithLanguage.{u}) (sentence : A.Sentence → B.Conclusion)
    (S : System B) : Prop := A.ArithSound S.inference.Provable (S.base.map ∘ sentence)

theorem ArithmeticSound.pullback {A : ArithLanguage.{u}}
    {sentence : A.Sentence → B.Conclusion} {S T : System B} (f : S ⟶ T)
    (h : ArithmeticSound A sentence T) : ArithmeticSound A sentence S :=
  fun a ha => h a (transport f ha)

end System

end Silmaril.Logic.Metatheory.ArithmeticSystems

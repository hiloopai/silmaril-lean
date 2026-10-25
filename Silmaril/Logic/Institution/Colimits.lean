module

public import Silmaril.Logic.Institution.Theory
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

@[expose] public section

/-!
# Colimits of theories

"Putting theories together": colimits in `Th(I)` exist whenever the corresponding colimits of
signatures exist. Given a diagram `K : J ⥤ Th(I)` with theories `(Σⱼ, Eⱼ)` and a colimit cocone
`ιⱼ : Σⱼ ⟶ Σ` of the underlying signatures, the theory

  `(Σ, (⋃ⱼ ιⱼ(Eⱼ))•)`

with the same injections is a colimit of `K` (Goguen–Burstall, Theorem 11).

Terminology. Goguen and Burstall's Definition 10 says a functor "reflects colimits" when every
colimit of the image diagram lifts to a colimit upstairs. In Mathlib that is *lifting*
(`LiftsToColimit`), not `ReflectsColimit`. The forgetful functor `Th(I) ⥤ Sign` does lift
colimits (`Theory.liftsToColimit`) but does not reflect them in Mathlib's sense: a cocone of
theories whose apex carries more sentences than the closure above has a colimiting image in
`Sign` without being a colimit. `Theory.isColimit_iff` characterizes exactly which cocones
over a colimit of signatures are colimits of theories.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory Limits

universe u v w m₁ m₂ j₁ j₂

variable {Sign : Type u} [Category.{v} Sign] {I : Sign ⥤ Room.{w, m₁, m₂}}
variable {J : Type j₁} [Category.{j₂} J] (K : J ⥤ Theory I)

namespace Theory

omit [Category J] in
/-- Translation along an identity signature morphism is the identity on sentences. -/
private theorem sen_id (X : Sign) (φ : (I.obj X).Sen) : (I.map (𝟙 X)).sen φ = φ := by
  rw [I.map_id]; rfl

/-- The sentences of the lifted apex: the closure of the union of the translated sentences of the
diagram.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, proof of Theorem 11
(`E = (⋃ₙ αₙ(Eₙ))•`); `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3.1,
Proposition 3.5 (the pushout case). -/
def liftedSentences (c : Cocone (K ⋙ Theory.forget I)) : Set (I.obj c.pt).Sen :=
  (I.obj c.pt).closure (⋃ j, (I.map (c.ι.app j)).sen '' (K.obj j).sentences)

/-- Each injection of the signature cocone is a theory morphism into the lifted apex. -/
theorem mapsTo_liftedSentences (c : Cocone (K ⋙ Theory.forget I)) (j : J) :
    Set.MapsTo (I.map (c.ι.app j)).sen (K.obj j).sentences (liftedSentences K c) :=
  fun φ hφ => (I.obj c.pt).subset_closure _ (Set.mem_iUnion.2 ⟨j, φ, hφ, rfl⟩)

/-- The lifted cocone: apex `(Σ, (⋃ⱼ ιⱼ(Eⱼ))•)`, injections `ιⱼ`.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, proof of Theorem 11. -/
def liftedCocone (c : Cocone (K ⋙ Theory.forget I)) : Cocone K where
  pt := ⟨⟨c.pt, liftedSentences K c⟩, (I.obj c.pt).closure_isClosed _⟩
  ι :=
    { app j := Theory.homMk (c.ι.app j) (mapsTo_liftedSentences K c j)
      naturality j j' f := by
        exact Theory.hom_ext (c.ι.naturality f) }

/-- The key step of Theorem 11: the mediating signature morphism out of a colimit is a theory
morphism out of the lifted apex.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, proof of Theorem 11
(using the Closure Lemma, Lemma 7). -/
theorem desc_mapsTo (c : Cocone (K ⋙ Theory.forget I)) (hc : IsColimit c) (s : Cocone K) :
    Set.MapsTo (I.map (hc.desc ((Theory.forget I).mapCocone s))).sen (liftedSentences K c)
      s.pt.sentences := by
  intro φ hφ
  set d := hc.desc ((Theory.forget I).mapCocone s)
  have hU : (I.map d).sen '' (⋃ j, (I.map (c.ι.app j)).sen '' (K.obj j).sentences) ⊆
      s.pt.sentences := by
    rintro _ ⟨_, hu, rfl⟩
    obtain ⟨j, ψ, hψ, rfl⟩ := Set.mem_iUnion.1 hu
    have hfac : c.ι.app j ≫ d = (s.ι.app j).hom.sig := hc.fac ((Theory.forget I).mapCocone s) j
    have h1 : (I.map d).sen ((I.map (c.ι.app j)).sen ψ) = (I.map (c.ι.app j ≫ d)).sen ψ := by
      rw [I.map_comp]; rfl
    rw [h1, hfac]
    exact (s.ι.app j).hom.mapsTo hψ
  have h2 := (I.map d).image_closure_subset _ ⟨φ, hφ, rfl⟩
  have h3 := (I.obj s.pt.sig).closure_mono hU h2
  rwa [s.pt.isClosed] at h3

/-- The lifted cocone is a colimit.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, Theorem 11. -/
def liftedCoconeIsColimit (c : Cocone (K ⋙ Theory.forget I)) (hc : IsColimit c) :
    IsColimit (liftedCocone K c) where
  desc s := Theory.homMk (hc.desc ((Theory.forget I).mapCocone s)) (desc_mapsTo K c hc s)
  fac s j := by
    exact Theory.hom_ext (hc.fac ((Theory.forget I).mapCocone s) j)
  uniq s m hm := by
    exact Theory.hom_ext (hc.uniq ((Theory.forget I).mapCocone s) m.hom.sig
        (fun j => congrArg (fun g => g.hom.sig) (hm j)))

/-- The forgetful functor `Th(I) ⥤ Sign` lifts every colimit: Goguen–Burstall's "Sign: Th → Sign
reflects colimits" in the sense of their Definition 10.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, Definition 10 and
Theorem 11. -/
def liftsToColimit (c : Cocone (K ⋙ Theory.forget I)) (hc : IsColimit c) :
    LiftsToColimit K (Theory.forget I) c hc where
  liftedCocone := liftedCocone K c
  validLift := Cocone.ext (Iso.refl _) (fun _ => by exact Category.comp_id _)
  makesColimit := liftedCoconeIsColimit K c hc

/-- The lift is unique: a cocone over `K` whose image is a colimit of signatures is a colimit of
theories exactly when its apex carries the lifted sentences. In particular a colimit of theories
over a given colimit of signatures is unique (Goguen–Burstall: "Sign creates colimits").

Source: `goguen-burstall-1992` in `references.bib`, §2.4, Definition 10 and the
remark after Theorem 11 ("Actually, the stronger result holds, that Sign creates colimits"). -/
theorem isColimit_iff (s : Cocone K) (hs : IsColimit ((Theory.forget I).mapCocone s)) :
    Nonempty (IsColimit s) ↔ s.pt.sentences = liftedSentences K ((Theory.forget I).mapCocone s) := by
  have hid : hs.desc ((Theory.forget I).mapCocone s) = 𝟙 _ :=
    hs.hom_ext fun j => by rw [hs.fac, Category.comp_id]
  have hsup : liftedSentences K ((Theory.forget I).mapCocone s) ⊆ s.pt.sentences := by
    intro φ hφ
    have h := desc_mapsTo K _ hs s hφ
    rwa [hid, I.map_id] at h
  constructor
  · rintro ⟨h⟩
    refine subset_antisymm ?_ hsup
    let L := liftedCocone K ((Theory.forget I).mapCocone s)
    have hsig : (h.desc L).hom.sig = 𝟙 _ :=
      hs.hom_ext fun j => by
        have := congrArg (fun g => g.hom.sig) (h.fac L j)
        exact this.trans (Category.comp_id _).symm
    intro φ hφ
    have h' := (h.desc L).hom.mapsTo hφ
    rw [hsig] at h'
    exact (congrArg (· ∈ L.pt.sentences) (sen_id s.pt.sig φ)).mp h'
  · intro heq
    let L := liftedCocone K ((Theory.forget I).mapCocone s)
    have hsub : s.pt.sentences ⊆ L.pt.sentences := heq.le
    let e : L.pt ≅ s.pt :=
      { hom := Theory.homMk (T := L.pt) (T' := s.pt) (𝟙 _) (by
          intro φ hφ
          exact (congrArg (· ∈ s.pt.sentences) (sen_id L.pt.sig φ)).mpr (hsup hφ))
        inv := Theory.homMk (T := s.pt) (T' := L.pt) (𝟙 _) (by
          intro φ hφ
          exact (congrArg (· ∈ L.pt.sentences) (sen_id s.pt.sig φ)).mpr (hsub hφ))
        hom_inv_id := Theory.hom_ext (Category.comp_id _)
        inv_hom_id := Theory.hom_ext (Category.comp_id _) }
    exact ⟨IsColimit.ofIsoColimit (liftedCoconeIsColimit K _ hs)
      (Cocone.ext e fun j => Theory.hom_ext (Category.comp_id _))⟩

/-- A diagram of theories has a colimit whenever its diagram of signatures does.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, Theorem 11. -/
theorem hasColimit [HasColimit (K ⋙ Theory.forget I)] : HasColimit K :=
  HasColimit.mk ⟨_, liftedCoconeIsColimit K _ (colimit.isColimit (K ⋙ Theory.forget I))⟩

/-- `Th(I)` has all colimits of shape `J` that `Sign` has.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, Theorem 11. -/
theorem hasColimitsOfShape [HasColimitsOfShape J Sign] : HasColimitsOfShape J (Theory I) :=
  ⟨fun K => hasColimit K⟩

/-- `Th(I)` is finitely cocomplete if `Sign` is.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, after Theorem 11
("the category Th of theories in an institution is finitely cocomplete if its category Sign of
signatures is finitely cocomplete"). -/
theorem hasFiniteColimits [HasFiniteColimits Sign] : HasFiniteColimits (Theory I) :=
  ⟨fun _ _ _ => hasColimitsOfShape⟩

/-- `Th(I)` is cocomplete if `Sign` is.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, after Theorem 11;
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §3.1 ("Th is cocomplete
whenever Sign is cocomplete"). -/
theorem hasColimitsOfSize [HasColimitsOfSize.{j₂, j₁} Sign] :
    HasColimitsOfSize.{j₂, j₁} (Theory I) :=
  ⟨fun _ _ => hasColimitsOfShape⟩

/-- The forgetful functor `Th(I) ⥤ Sign` preserves the colimits of every shape that `Sign`
has: a colimit of theories sits over a colimit of signatures.

Source: `goguen-burstall-1992` in `references.bib`, §2.4, Theorem 11 and its
proof (colimits of theories are computed over colimits of signatures);
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §3.1, Proposition 3.5. -/
theorem preservesColimitsOfShape [HasColimitsOfShape J Sign] :
    PreservesColimitsOfShape J (Theory.forget I) where
  preservesColimit {K} :=
    let c := colimit.cocone (K ⋙ Theory.forget I)
    let hc := colimit.isColimit (K ⋙ Theory.forget I)
    preservesColimit_of_preserves_colimit_cocone (liftedCoconeIsColimit K c hc)
      (IsColimit.ofIsoColimit hc (liftsToColimit K c hc).validLift.symm)

end Theory

end Silmaril.Logic.Institution

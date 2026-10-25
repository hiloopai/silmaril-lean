module

public import Silmaril.Logic.Metatheory.InferenceSystemCat.FixedSoundness
public import Silmaril.Logic.Metatheory.InferenceSystemCat.PropSystems
public import Mathlib.Order.Closure

@[expose] public section

/-!
# Conservative extensions

An extension is conservative over a language when it proves nothing new in
that language. Three forms share this file.

* For sets of derivable conclusions, `ConservativeOver L P Q` says that every
  conclusion of `L` in `Q` already lies in `P`. `ConservativeExtension L P Q`
  adds `P ⊆ Q`. Adding conclusions already derivable, in the sense of a
  closure operator, is conservative.
* For morphisms of `InferenceSystemCat`, conservativity is reflection of
  provability along the conclusion map: `Conservative f` is
  `Complete S T f.map`. `ConservativeOver L f` restricts reflection to the
  source conclusions in `L`. For identity-on-conclusions maps of `Fixed`
  systems these agree with the set-level notion on supports.
* For `PropSystems`, the same notions with propositional judgments.

In each case conservative maps are closed under identities and composition,
satisfy left cancellation, and are detected by a provability-preserving map
back that fixes the language: the retraction criterion.
-/

namespace Silmaril.Logic.Metatheory

open CategoryTheory

universe u v

section Sets

variable {α : Type u} {L L' P P' Q Q' R X : Set α}

/-- `Q` is conservative over `P` for the language `L`: every conclusion in `L`
that lies in `Q` already lies in `P`. -/
def ConservativeOver (L P Q : Set α) : Prop := ∀ a ∈ L, a ∈ Q → a ∈ P

/-- `Q` extends `P` and adds nothing in the language `L`. -/
def ConservativeExtension (L P Q : Set α) : Prop := P ⊆ Q ∧ ConservativeOver L P Q

namespace ConservativeOver

theorem iff_inter_subset : ConservativeOver L P Q ↔ Q ∩ L ⊆ P :=
  ⟨fun h a ha => h a ha.2 ha.1, fun h _ hL hQ => h ⟨hQ, hL⟩⟩

theorem univ_iff : ConservativeOver Set.univ P Q ↔ Q ⊆ P :=
  ⟨fun h a ha => h a trivial ha, fun h _ _ ha => h ha⟩

theorem refl (L P : Set α) : ConservativeOver L P P := fun _ _ h => h

theorem of_subset (h : Q ⊆ P) : ConservativeOver L P Q := fun _ _ ha => h ha

theorem trans (h₁ : ConservativeOver L P Q) (h₂ : ConservativeOver L Q R) :
    ConservativeOver L P R :=
  fun a ha hR => h₁ a ha (h₂ a ha hR)

/-- Conservativity over a language implies conservativity over a sublanguage. -/
theorem anti (h : ConservativeOver L P Q) (hL : L' ⊆ L) : ConservativeOver L' P Q :=
  fun a ha => h a (hL ha)

theorem union (h : ConservativeOver L P Q) (h' : ConservativeOver L' P Q) :
    ConservativeOver (L ∪ L') P Q :=
  fun a ha => ha.elim (h a) (h' a)

theorem iUnion {ι : Sort*} {L : ι → Set α} (h : ∀ i, ConservativeOver (L i) P Q) :
    ConservativeOver (⋃ i, L i) P Q := by
  intro a ha
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
  exact h i a hi

theorem mono_left (h : ConservativeOver L P Q) (hP : P ⊆ P') : ConservativeOver L P' Q :=
  fun a ha hQ => hP (h a ha hQ)

theorem anti_right (h : ConservativeOver L P Q) (hQ : Q' ⊆ Q) : ConservativeOver L P Q' :=
  fun a ha hQ' => h a ha (hQ hQ')

/-- Left cancellation: a conservative composite has a conservative first step. -/
theorem left_of_trans (hQR : Q ⊆ R) (h : ConservativeOver L P R) : ConservativeOver L P Q :=
  h.anti_right hQR

/-- Right cancellation: a conservative composite has a conservative second step. -/
theorem right_of_trans (hPQ : P ⊆ Q) (h : ConservativeOver L P R) : ConservativeOver L Q R :=
  h.mono_left hPQ

/-- The retraction criterion: a map carrying `Q` into `P` that fixes the
conclusions of `L` up to membership in `P`. -/
theorem of_retraction (r : α → α) (hr : Set.MapsTo r Q P) (hfix : ∀ a ∈ L, r a ∈ P → a ∈ P) :
    ConservativeOver L P Q :=
  fun a ha hQ => hfix a ha (hr hQ)

/-- The retraction criterion for a map fixing `L` pointwise. -/
theorem of_retraction_eq (r : α → α) (hr : Set.MapsTo r Q P) (hfix : ∀ a ∈ L, r a = a) :
    ConservativeOver L P Q :=
  of_retraction r hr fun a ha h => hfix a ha ▸ h

/-- Adding derivable conclusions is conservative. -/
theorem closure_union (c : ClosureOperator (Set α)) (h : X ⊆ c P) (L : Set α) :
    ConservativeOver L (c P) (c (P ∪ X)) :=
  of_subset (c.closure_min (Set.union_subset (c.le_closure P) h) (c.isClosed_closure P))

end ConservativeOver

namespace ConservativeExtension

theorem iff_inter_eq : ConservativeExtension L P Q ↔ P ⊆ Q ∧ Q ∩ L = P ∩ L := by
  refine ⟨fun ⟨hPQ, h⟩ => ⟨hPQ, ?_⟩, fun ⟨hPQ, h⟩ => ⟨hPQ, ?_⟩⟩
  · exact Set.Subset.antisymm (fun a ha => ⟨h a ha.2 ha.1, ha.2⟩)
      (Set.inter_subset_inter_left _ hPQ)
  · exact ConservativeOver.iff_inter_subset.2 (h ▸ Set.inter_subset_left)

theorem refl (L P : Set α) : ConservativeExtension L P P := ⟨subset_rfl, .refl L P⟩

theorem trans (h₁ : ConservativeExtension L P Q) (h₂ : ConservativeExtension L Q R) :
    ConservativeExtension L P R :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem anti (h : ConservativeExtension L P Q) (hL : L' ⊆ L) : ConservativeExtension L' P Q :=
  ⟨h.1, h.2.anti hL⟩

theorem left_of_trans (hPQ : P ⊆ Q) (hQR : Q ⊆ R) (h : ConservativeExtension L P R) :
    ConservativeExtension L P Q :=
  ⟨hPQ, h.2.left_of_trans hQR⟩

theorem right_of_trans (hPQ : P ⊆ Q) (hQR : Q ⊆ R) (h : ConservativeExtension L P R) :
    ConservativeExtension L Q R :=
  ⟨hQR, h.2.right_of_trans hPQ⟩

/-- Adding derivable conclusions gives a conservative extension over every
language; in fact the closure does not change. -/
theorem closure_union (c : ClosureOperator (Set α)) (h : X ⊆ c P) (L : Set α) :
    ConservativeExtension L (c P) (c (P ∪ X)) :=
  ⟨c.monotone Set.subset_union_left, ConservativeOver.closure_union c h L⟩

end ConservativeExtension

end Sets

namespace InferenceSystemCat

variable {S T U : InferenceSystemCat.{u, v}}

/-- `f` is conservative over the source conclusions `L`: it reflects
provability at each of them. -/
def ConservativeOver (L : Set S.Conclusion) (f : S ⟶ T) : Prop :=
  ∀ a ∈ L, T.Provable (f.map a) → S.Provable a

/-- A conservative morphism reflects provability: it is complete along its own
conclusion map. -/
def Conservative (f : S ⟶ T) : Prop := Complete S T f.map

theorem conservative_iff_conservativeOver_univ (f : S ⟶ T) :
    Conservative f ↔ ConservativeOver Set.univ f :=
  ⟨fun h a _ => h a, fun h a => h a (Set.mem_univ a)⟩

theorem conservative_id (S : InferenceSystemCat.{u, v}) : Conservative (𝟙 S) := complete_id S

theorem Conservative.comp {f : S ⟶ T} {g : T ⟶ U} (hf : Conservative f)
    (hg : Conservative g) : Conservative (f ≫ g) :=
  Complete.comp (f := f.map) (g := g.map) hg hf

/-- Left cancellation: if `f ≫ g` reflects provability, so does `f`. -/
theorem Conservative.of_comp {f : S ⟶ T} {g : T ⟶ U} (h : Conservative (f ≫ g)) :
    Conservative f :=
  fun a ha => h a (map_provable g ha)

/-- Right cancellation along a surjective conclusion map. -/
theorem Conservative.of_comp_of_surjective {f : S ⟶ T} {g : T ⟶ U}
    (h : Conservative (f ≫ g)) (hf : Function.Surjective f.map) : Conservative g := by
  intro b hb
  obtain ⟨a, rfl⟩ := hf b
  exact map_provable f (h a hb)

theorem ConservativeOver.anti {L L' : Set S.Conclusion} {f : S ⟶ T}
    (h : ConservativeOver L f) (hL : L' ⊆ L) : ConservativeOver L' f :=
  fun a ha => h a (hL ha)

theorem Conservative.conservativeOver {f : S ⟶ T} (h : Conservative f) (L : Set S.Conclusion) :
    ConservativeOver L f :=
  fun a _ => h a

theorem conservativeOver_id (L : Set S.Conclusion) : ConservativeOver L (𝟙 S) :=
  (conservative_id S).conservativeOver L

theorem ConservativeOver.comp {L : Set S.Conclusion} {L' : Set T.Conclusion} {f : S ⟶ T}
    {g : T ⟶ U} (hf : ConservativeOver L f) (hg : ConservativeOver L' g)
    (hL : Set.MapsTo f.map L L') : ConservativeOver L (f ≫ g) :=
  fun a ha h => hf a ha (hg (f.map a) (hL ha) h)

theorem ConservativeOver.of_comp {L : Set S.Conclusion} {f : S ⟶ T} {g : T ⟶ U}
    (h : ConservativeOver L (f ≫ g)) : ConservativeOver L f :=
  fun a ha h' => h a ha (map_provable g h')

/-- The retraction criterion: a provability-preserving interpretation back
that fixes the conclusions of `L` up to provability. -/
theorem conservativeOver_of_retraction {L : Set S.Conclusion} (f : S ⟶ T)
    (r : T.Conclusion → S.Conclusion) (hr : Sound T S r)
    (hfix : ∀ a ∈ L, S.Provable (r (f.map a)) → S.Provable a) : ConservativeOver L f :=
  fun a ha h => hfix a ha (hr _ h)

/-- The retraction criterion for a morphism back fixing `L` pointwise. -/
theorem conservativeOver_of_retraction_eq {L : Set S.Conclusion} (f : S ⟶ T) (r : T ⟶ S)
    (hfix : ∀ a ∈ L, r.map (f.map a) = a) : ConservativeOver L f :=
  conservativeOver_of_retraction f r.map (sound_of_morphism r) fun a ha h => hfix a ha ▸ h

/-- A morphism with a left inverse on conclusions is conservative. -/
theorem conservative_of_retraction (f : S ⟶ T) (r : T ⟶ S) (h : ∀ a, r.map (f.map a) = a) :
    Conservative f :=
  (conservative_iff_conservativeOver_univ f).2
    (conservativeOver_of_retraction_eq f r fun a _ => h a)

/-- Split monomorphisms are conservative. -/
theorem conservative_of_comp_eq_id (f : S ⟶ T) (r : T ⟶ S) (h : f ≫ r = 𝟙 S) :
    Conservative f :=
  conservative_of_retraction f r fun a => congrArg (fun k : S ⟶ S => k.map a) h

theorem conservative_of_isIso (f : S ⟶ T) [IsIso f] : Conservative f :=
  conservative_of_comp_eq_id f (inv f) (IsIso.hom_inv_id f)

end InferenceSystemCat

namespace InferenceSystemCat.Fixed

variable {α : Type u}

/-- `T` is conservative over `S` for the language `L`: supports agree on `L`
where `T` derives. -/
def ConservativeOver (L : Set α) (S T : Fixed.{u, v} α) : Prop :=
  Metatheory.ConservativeOver L (support S) (support T)

theorem conservativeOver_iff_inclusion {L : Set α} {S T : Fixed.{u, v} α} (f : S ⟶ T) :
    ConservativeOver L S T ↔ InferenceSystemCat.ConservativeOver L (inclusion.map f) :=
  Iff.rfl

/-- Over the full language, conservativity is completeness. -/
theorem conservativeOver_univ_iff {S T : Fixed.{u, v} α} :
    ConservativeOver Set.univ S T ↔ Complete S T :=
  Metatheory.ConservativeOver.univ_iff

theorem conservative_inclusion_iff {S T : Fixed.{u, v} α} (f : S ⟶ T) :
    InferenceSystemCat.Conservative (inclusion.map f) ↔ Complete S T :=
  Iff.rfl

/-- In the derivability lattice, conservativity compares the classes below `L`. -/
theorem conservativeOver_iff_toSet {L : Set α} {S T : Fixed.{u, v} α} :
    ConservativeOver L S T ↔
      (DerivabilityOrder.ofSystem T).toSet ∩ L ⊆ (DerivabilityOrder.ofSystem S).toSet :=
  Metatheory.ConservativeOver.iff_inter_subset

end InferenceSystemCat.Fixed

namespace InferenceSystemCat.PropSystems

variable {S T U : PropSystems.{u}}

/-- `f` reflects judgments at the source conclusions in `L`. -/
def ConservativeOver (L : Set S.Conclusion) (f : S ⟶ T) : Prop :=
  ∀ a ∈ L, T.Derivation (f.map a) → S.Derivation a

/-- `f` reflects every judgment. -/
def Conservative (f : S ⟶ T) : Prop := ∀ a, T.Derivation (f.map a) → S.Derivation a

theorem conservative_iff_conservativeOver_univ (f : S ⟶ T) :
    Conservative f ↔ ConservativeOver Set.univ f :=
  ⟨fun h a _ => h a, fun h a => h a (Set.mem_univ a)⟩

theorem conservative_id (S : PropSystems.{u}) : Conservative (𝟙 S) := fun _ h => h

theorem Conservative.comp {f : S ⟶ T} {g : T ⟶ U} (hf : Conservative f)
    (hg : Conservative g) : Conservative (f ≫ g) :=
  fun a h => hf a (hg (f.map a) h)

theorem Conservative.of_comp {f : S ⟶ T} {g : T ⟶ U} (h : Conservative (f ≫ g)) :
    Conservative f :=
  fun a ha => h a (g.mapDerivation ha)

theorem Conservative.of_comp_of_surjective {f : S ⟶ T} {g : T ⟶ U}
    (h : Conservative (f ≫ g)) (hf : Function.Surjective f.map) : Conservative g := by
  intro b hb
  obtain ⟨a, rfl⟩ := hf b
  exact f.mapDerivation (h a hb)

theorem ConservativeOver.comp {L : Set S.Conclusion} {L' : Set T.Conclusion} {f : S ⟶ T}
    {g : T ⟶ U} (hf : ConservativeOver L f) (hg : ConservativeOver L' g)
    (hL : Set.MapsTo f.map L L') : ConservativeOver L (f ≫ g) :=
  fun a ha h => hf a ha (hg (f.map a) (hL ha) h)

theorem ConservativeOver.of_comp {L : Set S.Conclusion} {f : S ⟶ T} {g : T ⟶ U}
    (h : ConservativeOver L (f ≫ g)) : ConservativeOver L f :=
  fun a ha h' => h a ha (g.mapDerivation h')

/-- The retraction criterion for propositional systems. -/
theorem conservativeOver_of_retraction {L : Set S.Conclusion} (f : S ⟶ T) (r : T ⟶ S)
    (hfix : ∀ a ∈ L, S.Derivation (r.map (f.map a)) → S.Derivation a) :
    ConservativeOver L f :=
  fun a ha h => hfix a ha (r.mapDerivation h)

theorem conservativeOver_of_retraction_eq {L : Set S.Conclusion} (f : S ⟶ T) (r : T ⟶ S)
    (hfix : ∀ a ∈ L, r.map (f.map a) = a) : ConservativeOver L f :=
  conservativeOver_of_retraction f r fun a ha h => hfix a ha ▸ h

/-- Conservativity is preserved and reflected by lifting to coherent systems. -/
theorem conservative_toCoherent_iff (f : S ⟶ T) :
    InferenceSystemCat.Conservative (toCoherent.{u, v}.map f).hom ↔ Conservative f :=
  forall_congr' fun a =>
    imp_congr (toCoherent_provable T (f.map a)) (toCoherent_provable S a)

end InferenceSystemCat.PropSystems

end Silmaril.Logic.Metatheory

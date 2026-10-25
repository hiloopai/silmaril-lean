module

public import Silmaril.Logic.Institution.Grothendieck.SemiExact
public import Silmaril.Logic.Institution.Grothendieck.Examples.PLEQ
public import Silmaril.Logic.Institution.Grothendieck.Examples.FOL
public import Silmaril.Logic.Institution.Grothendieck.Examples.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

/-!
# The logic graph `PL → FOL ← EQ` and its Grothendieck institution

* `hetLogic` is the logic graph `PL → FOL ← EQ` as an indexed coinstitution over Mathlib's
  `WalkingCospan`, and `hetInst` its Grothendieck institution: the semantic basis of
  heterogeneous specification over these three logics, which is semi-exact
  (`hetInst_semiExact`).
* `PL.entails_iff_het`: propositional consequence is consequence in the heterogeneous logic.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory Limits Examples

/-- The logic graph `PL → FOL ← EQ` as an indexed coinstitution over `WalkingCospan`.

Source: `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4:
"Heterogeneous specification is based on some graph of logics and logic translations,
formalized as institutions and comorphisms") and Fig. 2 (the Hets logic graph). -/
def hetLogic : IndexedCoInst.{0, 0, 1, 0, 0, 0, 1} WalkingCospan :=
  cospan (C := CoIns.{1, 0, 0, 0, 1}) (X := PL.inst) (Y := EQ.inst) (Z := FOL.inst) plToFol eqToFol

/-- The Grothendieck institution of `PL → FOL ← EQ`.

Source: `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4:
"This institution is basically a flattening, or disjoint union, of the logic graph"). -/
def hetInst : Inst := IndexedCoInst.flatInst hetLogic

/-! ### Auxiliary facts for the logic graph `PL → FOL ← EQ` -/

namespace Het

/-- A functor with a two-sided inverse (as an equality of functors) is an isomorphism in `Cat`. -/
theorem isIso_ofFunctor {C D : Cat} (F : C ⥤ D) (G : D ⥤ C) (h₁ : F ⋙ G = 𝟭 C)
    (h₂ : G ⋙ F = 𝟭 D) : IsIso (X := C) (Y := D) (Cat.Hom.ofFunctor F) :=
  ⟨⟨Cat.Hom.ofFunctor G, Cat.ext h₁, Cat.ext h₂⟩⟩

/-- An isomorphism of signatures has an isomorphism of model categories as its reduct. -/
theorem isIso_modHom {Sign : Type*} [Category Sign] (I : Sign ⥤ Room.{0, 0, 1}) {S S' : Sign}
    (σ : S ⟶ S') (hσ : IsIso σ) : IsIso (modHom I σ) := by
  have := hσ
  change IsIso (Room.modFunctor.map (I.map σ)).unop
  infer_instance

/-- A commuting square of signatures whose two reducts along `g₁` and `f₂` are isomorphisms of
model categories amalgamates. -/
theorem amalgamates_of_isIso {Sign : Type*} [Category Sign] (I : Sign ⥤ Room.{0, 0, 1})
    {S S₁ S₂ S' : Sign} {f₁ : S ⟶ S₁} {f₂ : S ⟶ S₂} {g₁ : S₁ ⟶ S'} {g₂ : S₂ ⟶ S'}
    (w : f₁ ≫ g₁ = f₂ ≫ g₂) (h₁ : IsIso (modHom I g₁)) (h₂ : IsIso (modHom I f₂)) :
    Amalgamates I f₁ f₂ g₁ g₂ := by
  have key : ∀ {A B C : Sign} (a : A ⟶ B) (b : B ⟶ C),
      modHom I (a ≫ b) = modHom I b ≫ modHom I a := by
    intro A B C a b
    simp only [modHom, Functor.map_comp]
    rfl
  exact IsPullback.of_horiz_isIso ⟨by rw [← key, ← key, w]⟩

/-- First-order structures over the signature of a set of propositional variables have at most
one homomorphism between any two of them (there are no sorts). -/
instance plStructureHom_subsingleton (P : Type) (M N : FOL.Structure (PLtoFOL.sig P)) :
    Subsingleton (M ⟶ N) :=
  ⟨fun f g => by
    obtain ⟨f, _, _⟩ := f
    obtain ⟨g, _, _⟩ := g
    obtain rfl : f = g := funext fun s => PEmpty.elim s
    rfl⟩

/-- The inverse of the model translation of `PL → FOL`: a valuation as a first-order structure.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6 (the expansion witnessing model expansiveness), §4.1. -/
def plModInv (P : Type) : PL.Model P ⥤ FOL.Structure (PLtoFOL.sig P) where
  obj v := PLtoFOL.expansion P v.val
  map h := ⟨fun s => PEmpty.elim s, fun o => PEmpty.elim o, fun r _ hr => h.down r.2 hr⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- A first-order structure over `PLtoFOL.sig P` is the expansion of its valuation. -/
theorem pl_expansion_valuation {P : Type} (M : FOL.Structure (PLtoFOL.sig P)) :
    PLtoFOL.expansion P (PLtoFOL.valuation M) = M := by
  unfold PLtoFOL.expansion
  obtain ⟨⟨carrier, op⟩, rel⟩ := M
  obtain rfl : carrier = fun s => PEmpty.elim s := funext fun s => PEmpty.elim s
  have hop : @op = fun {n} {w} {s} o _ => PEmpty.elim o := by
    funext n w s o
    exact PEmpty.elim o
  subst hop
  congr 1
  funext n w r args
  obtain ⟨⟨rfl⟩, p⟩ := r
  obtain rfl : w = Fin.elim0 := fin0_funext _ _
  exact congrArg (rel (n := 0) (w := Fin.elim0) (⟨rfl⟩, p)) (fin0_funext _ _)

/-- The model translation of `PL → FOL` followed by its inverse is the identity. -/
theorem pl_mod_comp_inv (P : Type) : PLtoFOL.mod P ⋙ plModInv P = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun M => pl_expansion_valuation M) (fun _ _ _ => Subsingleton.elim _ _)

/-- The model translation of `PL → FOL` is an isomorphism of model categories. -/
theorem pl_isIso_mod (P : Type) :
    IsIso (X := (FOL.institution.obj (PLtoFOL.sig P)).Mod) (Y := (PL.institution.obj P).Mod)
      (Cat.Hom.ofFunctor (PLtoFOL.mod P)) :=
  isIso_ofFunctor (C := (FOL.institution.obj (PLtoFOL.sig P)).Mod)
    (D := (PL.institution.obj P).Mod) (PLtoFOL.mod P) (plModInv P) (pl_mod_comp_inv P) rfl

/-- The inverse of the model translation of `EQ → FOL`: an algebra as a first-order structure
without relations.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3(5). -/
def eqModInv (Sg : EQ.Signature) : EQ.Algebra Sg ⥤ FOL.Structure (EQtoFOL.sig Sg) where
  obj A := EQtoFOL.expansion A
  map h := ⟨h.map, h.map_op, fun r => PEmpty.elim r⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A first-order structure over `EQtoFOL.sig Sg` is the expansion of its algebra. -/
theorem eq_expansion_toAlgebra {Sg : EQ.Signature} (M : FOL.Structure (EQtoFOL.sig Sg)) :
    EQtoFOL.expansion M.toAlgebra = M := by
  unfold EQtoFOL.expansion
  obtain ⟨A, rel⟩ := M
  congr 1
  funext n w r
  exact PEmpty.elim r

/-- The model translation of `EQ → FOL` followed by its inverse is the identity. -/
theorem eq_mod_comp_inv (Sg : EQ.Signature) : EQtoFOL.mod Sg ⋙ eqModInv Sg = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun M => eq_expansion_toAlgebra M) ?_
  rintro ⟨A, rA⟩ ⟨B, rB⟩ f
  obtain rfl : @rA = fun {n} {w} r _ => PEmpty.elim r := by
    funext n w r
    exact PEmpty.elim r
  obtain rfl : @rB = fun {n} {w} r _ => PEmpty.elim r := by
    funext n w r
    exact PEmpty.elim r
  rfl

/-- The model translation of `EQ → FOL` is an isomorphism of model categories. -/
theorem eq_isIso_mod (Sg : EQ.Signature) :
    IsIso (X := (FOL.institution.obj (EQtoFOL.sig Sg)).Mod) (Y := (EQ.institution.obj Sg).Mod)
      (Cat.Hom.ofFunctor (EQtoFOL.mod Sg)) :=
  isIso_ofFunctor (C := (FOL.institution.obj (EQtoFOL.sig Sg)).Mod)
    (D := (EQ.institution.obj Sg).Mod) (EQtoFOL.mod Sg) (eqModInv Sg) (eq_mod_comp_inv Sg) rfl

/-- The nullary relation symbols of a first-order signature (with their empty arity). -/
def nullaryRels : FOL.Signature ⥤ Type where
  obj F := Σ w : Fin 0 → F.S, F.Rel 0 w
  map σ := TypeCat.ofHom fun r => ⟨σ.sorts ∘ r.1, σ.rels r.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Transport a nullary relation symbol to an arity `w : Fin n → S` with `n = 0`. -/
def relCast {F : FOL.Signature} {n : ℕ} (h : n = 0) (w : Fin n → F.S)
    (x : Σ w : Fin 0 → F.S, F.Rel 0 w) : F.Rel n w := by
  subst h
  exact (fin0_funext x.1 w) ▸ x.2

/-- The signature functor of `PL → FOL` is left adjoint to taking nullary relation symbols: a
first-order signature morphism out of `PLtoFOL.sig P` is a choice of a nullary relation symbol
for each propositional variable.

Source: the adjunction underlying the morphism–comorphism duality of
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §4.2, Theorem 4.11, here for
the comorphism `PL → FOL` of
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1. -/
def plAdjunction : PLtoFOL.sigFunctor ⊣ nullaryRels :=
  Adjunction.mkOfHomEquiv
    { homEquiv P F :=
        { toFun f := TypeCat.ofHom fun p =>
            ⟨f.sorts ∘ Fin.elim0, f.rels (n := 0) (w := Fin.elim0) (⟨rfl⟩, p)⟩
          invFun g := FOL.Signature.Hom.mk ⟨fun s => PEmpty.elim s, fun o => PEmpty.elim o⟩
            (fun {_ w} r => relCast r.1.down _ (show Σ w : Fin 0 → F.S, F.Rel 0 w from g r.2))
          left_inv := by
            intro f
            obtain ⟨⟨sorts, ops⟩, rels⟩ := f
            obtain rfl : sorts = fun s => PEmpty.elim s := funext fun s => PEmpty.elim s
            have hops : @ops = fun {n} {w} {s} o => PEmpty.elim o := by
              funext n w s o
              exact PEmpty.elim o
            subst hops
            dsimp only
            congr 1
            funext n w r
            obtain ⟨⟨rfl⟩, p⟩ := r
            obtain rfl : w = Fin.elim0 := fin0_funext _ _
            rfl
          right_inv := by
            intro g
            ext p
            change (⟨_, relCast rfl _ (g p)⟩ : Σ w : Fin 0 → F.S, F.Rel 0 w) = g p
            generalize g p = x
            obtain ⟨w, r⟩ := x
            obtain rfl : w = (fun s => PEmpty.elim s) ∘ Fin.elim0 := fin0_funext _ _
            rfl }
      homEquiv_naturality_left_symm := by
        intros
        rfl
      homEquiv_naturality_right := by
        intros
        rfl }

/-- Every reduct of a model translation of the logic graph is an isomorphism of model
categories: identities, and the model translations of `PL → FOL` and `EQ → FOL`. -/
theorem isIso_mod {i j : WalkingCospan} (d : i ⟶ j) (S : (IndexedCoInst.inst hetLogic i).Sign) :
    IsIso
      (X := ((IndexedCoInst.inst hetLogic j).I.obj ((IndexedCoInst.coHom hetLogic d).Φ.obj S)).Mod)
      (Y := ((IndexedCoInst.inst hetLogic i).I.obj S).Mod)
      (Cat.Hom.ofFunctor ((IndexedCoInst.coHom hetLogic d).ρ.app S).mod) := by
  have hid : ∀ (X : WalkingCospan) (S : (IndexedCoInst.inst hetLogic X).Sign),
      IsIso
        (X := ((IndexedCoInst.inst hetLogic X).I.obj
          ((IndexedCoInst.coHom hetLogic (𝟙 X)).Φ.obj S)).Mod)
        (Y := ((IndexedCoInst.inst hetLogic X).I.obj S).Mod)
        (Cat.Hom.ofFunctor ((IndexedCoInst.coHom hetLogic (𝟙 X)).ρ.app S).mod) := fun X S => by
    change IsIso (𝟙 ((IndexedCoInst.inst hetLogic X).I.obj S).Mod)
    infer_instance
  cases d with
  | id => exact hid _ S
  | term k =>
    cases k
    · exact pl_isIso_mod S
    · exact eq_isIso_mod S

/-- A Grothendieck signature morphism of `hetInst` with an invertible fiber component has an
invertible model reduct. -/
theorem isIso_modHom_flat {X Y : IndexedCoInst.FlatSig hetLogic} (f : X ⟶ Y)
    (hf : IsIso f.fiber) : IsIso (modHom (IndexedCoInst.flat hetLogic) f) := by
  have h₁ := isIso_modHom (IndexedCoInst.inst hetLogic Y.base).I f.fiber hf
  have h₂ := isIso_mod f.base X.fiber
  exact IsIso.comp_isIso' h₁ h₂

/-- Two composites of `eqToHom`s between the same objects are equal. -/
theorem eqToHom_three {C : Type*} [Category C] {a b c d e : C} (p : a = b) (q : b = c)
    (r : c = d) (p' : a = e) (r' : e = d) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r = eqToHom p' ≫ eqToHom r' := by
  simp

/-- In a Grothendieck construction, the square of morphisms with identity fiber components out
of `(i, S)` along a commuting square of indices commutes. -/
theorem grothendieck_square {Ind : Type*} [Category Ind] (G : Ind ⥤ Cat) {i i₁ i₂ j : Ind}
    (d₁ : i ⟶ i₁) (d₂ : i ⟶ i₂) (e₁ : i₁ ⟶ j) (e₂ : i₂ ⟶ j) (hsq : d₁ ≫ e₁ = d₂ ≫ e₂)
    (S : G.obj i) (T : G.obj j)
    (h₁ : (G.map e₁).toFunctor.obj ((G.map d₁).toFunctor.obj S) = T)
    (h₂ : (G.map e₂).toFunctor.obj ((G.map d₂).toFunctor.obj S) = T) :
    @CategoryStruct.comp (Grothendieck G) _ ⟨i, S⟩ ⟨i₁, (G.map d₁).toFunctor.obj S⟩ ⟨j, T⟩
        (Grothendieck.Hom.mk d₁ (𝟙 _)) (Grothendieck.Hom.mk e₁ (eqToHom h₁)) =
      @CategoryStruct.comp (Grothendieck G) _ ⟨i, S⟩ ⟨i₂, (G.map d₂).toFunctor.obj S⟩ ⟨j, T⟩
        (Grothendieck.Hom.mk d₂ (𝟙 _)) (Grothendieck.Hom.mk e₂ (eqToHom h₂)) :=
  Grothendieck.ext _ _ hsq (by
    simp
    exact eqToHom_three _ _ _ _ _)

/-- `WalkingCospan` has pushouts: in each span one leg factors through the other. -/
theorem walkingCospan_hasPushouts : HasPushouts WalkingCospan := by
  have hl : ∀ {X Y Z : WalkingCospan} (f : X ⟶ Y) (g : X ⟶ Z) (_ : Y ⟶ Z),
      HasColimit (span f g) := fun f g h =>
    ⟨⟨⟨PushoutCocone.mk h (𝟙 _) (Subsingleton.elim _ _),
      PushoutCocone.IsColimit.mk _ (fun s => s.inr) (fun _ => Subsingleton.elim _ _)
        (fun _ => Subsingleton.elim _ _) (fun _ _ _ _ => Subsingleton.elim _ _)⟩⟩⟩
  have hr : ∀ {X Y Z : WalkingCospan} (f : X ⟶ Y) (g : X ⟶ Z) (_ : Z ⟶ Y),
      HasColimit (span f g) := fun f g h =>
    ⟨⟨⟨PushoutCocone.mk (𝟙 _) h (Subsingleton.elim _ _),
      PushoutCocone.IsColimit.mk _ (fun s => s.inl) (fun _ => Subsingleton.elim _ _)
        (fun _ => Subsingleton.elim _ _) (fun _ _ _ _ => Subsingleton.elim _ _)⟩⟩⟩
  refine @hasPushouts_of_hasColimit_span WalkingCospan _ ?_
  intro X Y Z f g
  cases f with
  | id => exact hl _ g g
  | term j =>
    cases g with
    | id => exact hr _ _ (WidePullbackShape.Hom.term j)
    | term => exact hl _ _ (𝟙 _)

end Het

/-- Every comorphism of the logic graph `PL → FOL ← EQ` is exact (the identities trivially, the
two translations by `plToFol_exact` and `eqToFol_exact`).

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.2,
Definition 4.9 (pullback form). -/
theorem hetLogic_exact {i j : WalkingCospan} (d : i ⟶ j) :
    (IndexedCoInst.coHom hetLogic d).Exact := by
  have hid : ∀ X : WalkingCospan, (IndexedCoInst.coHom hetLogic (𝟙 X)).Exact := by
    intro X S S' σ
    change IsPullback (modHom (IndexedCoInst.inst hetLogic X).I σ) (𝟙 _) (𝟙 _)
      (modHom (IndexedCoInst.inst hetLogic X).I σ)
    exact IsPullback.of_id_snd
  cases d with
  | id => exact hid _
  | term k =>
    cases k
    · exact plToFol_exact
    · exact eqToFol_exact

/-- Every component of the logic graph is semi-exact.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Definition 3.10. -/
theorem hetLogic_semiExact (i : WalkingCospan) :
    SemiExact (IndexedCoInst.inst hetLogic i).I := by
  rcases i with _ | _ | _
  exacts [FOL.semiExact, PL.semiExact, EQ.semiExact]

/-- **The heterogeneous logic `PL → FOL ← EQ` is semi-exact**: the payoff of the three
conditions above, via `IndexedCoInst.semiExact_flat_iff`.

Proof route: `WalkingCospan` has pushouts (it is a thin category in which any two arrows out of
an object have a join); the components have pushouts (`Type`, `EQ.hasPushouts`,
`FOL.hasPushouts`); both signature translations preserve pushouts, being left adjoints
(`EQtoFOL.adjunction`; for `PL → FOL` the right adjoint sends a first-order signature to its
nullary relation symbols); index semi-exactness reduces, for the only non-trivial index
pushouts (both legs into `one`), to the kernel pair of a model translation, which is trivial
because the model translations are isomorphisms; `hetLogic_semiExact` and `hetLogic_exact`
give the other two conditions.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3,
Proposition 3.5 (PDF page 5); `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`,
§2 (PDF page 4: amalgamation in the Grothendieck institution is needed by the heterogeneous
proof calculus). -/
theorem hetInst_semiExact : SemiExact (IndexedCoInst.flat hetLogic) := by
  have : HasPushouts WalkingCospan := Het.walkingCospan_hasPushouts
  have : ∀ i : WalkingCospan, HasPushouts (IndexedCoInst.inst hetLogic i).Sign := by
    rintro (_ | _ | _)
    exacts [FOL.hasPushouts, inferInstanceAs (HasPushouts Type), EQ.hasPushouts]
  have hΦ : ∀ ⦃i j : WalkingCospan⦄ (d : i ⟶ j),
      PreservesColimitsOfShape WalkingSpan (IndexedCoInst.coHom hetLogic d).Φ := by
    have hid : ∀ X : WalkingCospan,
        PreservesColimitsOfShape WalkingSpan (IndexedCoInst.coHom hetLogic (𝟙 X)).Φ := by
      intro X
      change PreservesColimitsOfShape WalkingSpan (𝟭 (IndexedCoInst.inst hetLogic X).Sign)
      infer_instance
    intro i j d
    cases d with
    | id => exact hid _
    | term k =>
      cases k
      · exact Het.plAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
      · exact EQtoFOL.adjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hidx : IndexedCoInst.IndexSemiExact hetLogic := by
    intro i i₁ i₂ j d₁ d₂ e₁ e₂ _ S
    refine Het.amalgamates_of_isIso _ ?_ (Het.isIso_modHom_flat _ ?_)
      (Het.isIso_modHom_flat _ ?_)
    · exact Het.grothendieck_square (IndexedCoInst.sign hetLogic) d₁ d₂ e₁ e₂
        (Subsingleton.elim _ _) S ((IndexedCoInst.coHom hetLogic (d₁ ≫ e₁)).Φ.obj S)
        (congrArg (fun g => g.Φ.obj S) (IndexedCoInst.coHom_comp hetLogic d₁ e₁).symm)
        (congrArg (fun g => g.Φ.obj S) ((IndexedCoInst.coHom_comp hetLogic d₂ e₂).symm.trans
          (congrArg (IndexedCoInst.coHom hetLogic) (Subsingleton.elim (d₂ ≫ e₂) (d₁ ≫ e₁)))))
    · exact (eqToIso _).isIso_hom
    · exact IsIso.id _
  exact (IndexedCoInst.semiExact_flat_iff hetLogic hΦ).2
    ⟨hetLogic_semiExact, hidx, fun _ _ d => hetLogic_exact d⟩

/-- Propositional consequence is consequence in the heterogeneous logic, via the component
embedding of `PL` into the Grothendieck institution.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7 (borrowing along a model-expansive comorphism). -/
theorem PL.entails_iff_het (P : Type) (Γ : Set (PL.Formula P)) (φ : PL.Formula P) :
    (PL.institution.obj P).Entails Γ φ ↔
      ((IndexedCoInst.flat hetLogic).obj
          ((IndexedCoInst.ι hetLogic WalkingCospan.left).Φ.obj P)).Entails
        (((IndexedCoInst.ι hetLogic WalkingCospan.left).ρ.app P).sen '' Γ)
        (((IndexedCoInst.ι hetLogic WalkingCospan.left).ρ.app P).sen φ) :=
  IndexedCoInst.entails_iff_flat hetLogic WalkingCospan.left P Γ φ

end Silmaril.Logic.Institution

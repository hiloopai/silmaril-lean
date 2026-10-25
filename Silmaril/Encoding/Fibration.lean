module

public import Silmaril.Encoding.Category
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# `carrierFunctor` is a fibration and an opfibration

`EncCat₂.carrierFunctor : EncCat₂ ⥤ Type` sends an encoding `(σ, α, E)` to its
carrier `σ`.  Its fiber over `σ` is `EncCat σ` (`EncCat.isoCarrierFiber`).  This
file packages the carrier-change lifts of `Silmaril.Encoding.Category` as
Mathlib fibered-category structure:

* A morphism `φ : X ⟶ Y` lies over `g` exactly when `φ.onCarrier = g`
  (`isHomLift_iff`).
* **Cartesian lifts.**  For `Y : EncCat₂` and `g : R ⟶ Y.carrier`, the morphism
  `pullLift Y g : (R, Y.ast, Y.rel.pull g) ⟶ Y` with components `(g, id)` is
  `pullCounit g` at `⟨Y.ast, Y.rel⟩` (`pullLift_eq_pullCounit`, by `rfl`), and it
  is strongly cartesian (`isStronglyCartesian_pullLift`).  Hence
  `carrierFunctor` is a fibered category (`IsFibered`, `IsPreFibered`).
* **Cocartesian lifts.**  For `X : EncCat₂` and `g : X.carrier ⟶ S`,
  `pushLift X g : X ⟶ (S, X.ast, X.rel.push g)` with components `(g, id)` is
  `pushUnit g` at `⟨X.ast, X.rel⟩` and is strongly cocartesian
  (`isStronglyCocartesian_pushLift`).  Mathlib has no opfibration class, so we
  state `carrierFunctor_exists_isStronglyCocartesian`.

Reindexing along `g` is thus `pullFunctor g` (the fibration) and `pushFunctor g`
(the opfibration), and the adjunction `pushFunctor g ⊣ pullFunctor g` is the
usual one for a bifibration.
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

namespace EncCat₂

/-- A morphism of `EncCat₂` lies over `f` exactly when its carrier map is `f`. -/
theorem isHomLift_iff {X Y : EncCat₂} (f : carrierFunctor.obj X ⟶ carrierFunctor.obj Y)
    (φ : X ⟶ Y) :
    carrierFunctor.IsHomLift f φ ↔ φ.onCarrier = ⇑f := by
  constructor
  · intro _
    have h' := IsHomLift.eq_of_isHomLift carrierFunctor f φ
    subst h'
    rfl
  · intro h
    have h' : f = carrierFunctor.map φ := by
      ext s
      exact (congrFun h s).symm
    subst h'
    exact .map φ

/-! ## Cartesian lifts -/

/-- The pullback of `Y` along `g : R ⟶ Y.carrier`: carrier `R`, same syntax,
relation `Y.rel.pull g`. -/
abbrev pullObj (Y : EncCat₂) {R : Type} (g : R ⟶ carrierFunctor.obj Y) : EncCat₂ :=
  ⟨R, Y.ast, Y.rel.pull g⟩

/-- The cartesian lift `(g, id) : g^* Y ⟶ Y`. -/
def pullLift (Y : EncCat₂) {R : Type} (g : R ⟶ carrierFunctor.obj Y) : pullObj Y g ⟶ Y :=
  ⟨g, id, fun _ _ h => h⟩

/-- `pullLift` is the component of `EncCat.pullCounit` at `Y` read as an object
of `EncCat Y.carrier` (the identification `(incl Y.carrier).obj ⟨Y.ast, Y.rel⟩ = Y`
holds by structure eta). -/
theorem pullLift_eq_pullCounit (Y : EncCat₂) {R : Type} (g : R ⟶ carrierFunctor.obj Y) :
    pullLift Y g =
      (EncCat.pullCounit (σ := R) (σ' := Y.carrier) g).app (⟨Y.ast, Y.rel⟩ : EncCat Y.carrier) :=
  rfl

instance (Y : EncCat₂) {R : Type} (g : R ⟶ carrierFunctor.obj Y) :
    carrierFunctor.IsHomLift g (pullLift Y g) :=
  (isHomLift_iff (X := pullObj Y g) g (pullLift Y g)).mpr rfl

/-- **`pullLift` (i.e. `pullCounit`) is strongly cartesian over `carrierFunctor`.**
Given `φ' : X' ⟶ Y` over `g' ≫ g`, the unique factorization through `pullLift Y g`
lying over `g'` has components `(g', φ'.fn)`. -/
instance isStronglyCartesian_pullLift (Y : EncCat₂) {R : Type} (g : R ⟶ carrierFunctor.obj Y) :
    carrierFunctor.IsStronglyCartesian g (pullLift Y g) where
  universal_property' {X'} g' φ' hφ' := by
    have hc : φ'.onCarrier = ⇑(g' ≫ g) := (isHomLift_iff (g' ≫ g) φ').mp hφ'
    refine ⟨⟨g', φ'.fn, fun s a h => ?_⟩,
      ⟨(isHomLift_iff (X := X') (Y := pullObj Y g) g' _).mpr rfl, ?_⟩, ?_⟩
    · have := φ'.preserves s a h
      rw [hc] at this
      exact this
    · exact hom_ext hc.symm rfl
    · rintro χ ⟨hχ, hχφ⟩
      have h₁ : χ.onCarrier = ⇑g' := (isHomLift_iff g' χ).mp hχ
      have h₂ := congrArg Hom.fn hχφ
      exact hom_ext h₁ h₂

/-- Every morphism into `Y` over `R ⟶ Y.carrier` has a strongly cartesian lift. -/
theorem carrierFunctor_exists_isStronglyCartesian (Y : EncCat₂) (R : Type)
    (g : R ⟶ carrierFunctor.obj Y) :
    ∃ (X : EncCat₂) (φ : X ⟶ Y), carrierFunctor.IsStronglyCartesian g φ :=
  ⟨pullObj Y g, pullLift Y g, inferInstance⟩

/-- **`carrierFunctor` is a fibered category.** -/
instance isFibered_carrierFunctor : carrierFunctor.IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian carrierFunctor_exists_isStronglyCartesian

instance isPreFibered_carrierFunctor : carrierFunctor.IsPreFibered := inferInstance

/-- In particular every cartesian morphism over `carrierFunctor` is strongly
cartesian. -/
example {R S : Type} (f : R ⟶ S) {X Y : EncCat₂} (φ : X ⟶ Y)
    [carrierFunctor.IsCartesian f φ] : carrierFunctor.IsStronglyCartesian f φ :=
  inferInstance

/-! ## Cocartesian lifts -/

/-- The pushforward of `X` along `g : X.carrier ⟶ S`: carrier `S`, same syntax,
relation `X.rel.push g`. -/
abbrev pushObj (X : EncCat₂) {S : Type} (g : carrierFunctor.obj X ⟶ S) : EncCat₂ :=
  ⟨S, X.ast, X.rel.push g⟩

/-- The cocartesian lift `(g, id) : X ⟶ g_! X`. -/
def pushLift (X : EncCat₂) {S : Type} (g : carrierFunctor.obj X ⟶ S) : X ⟶ pushObj X g :=
  ⟨g, id, fun s _ h => ⟨s, rfl, h⟩⟩

/-- `pushLift` is the component of `EncCat.pushUnit` at `X` read as an object of
`EncCat X.carrier`. -/
theorem pushLift_eq_pushUnit (X : EncCat₂) {S : Type} (g : carrierFunctor.obj X ⟶ S) :
    pushLift X g =
      (EncCat.pushUnit (σ := X.carrier) (σ' := S) g).app (⟨X.ast, X.rel⟩ : EncCat X.carrier) :=
  rfl

instance (X : EncCat₂) {S : Type} (g : carrierFunctor.obj X ⟶ S) :
    carrierFunctor.IsHomLift g (pushLift X g) :=
  (isHomLift_iff (Y := pushObj X g) g (pushLift X g)).mpr rfl

/-- **`pushLift` (i.e. `pushUnit`) is strongly cocartesian over `carrierFunctor`.** -/
instance isStronglyCocartesian_pushLift (X : EncCat₂) {S : Type} (g : carrierFunctor.obj X ⟶ S) :
    carrierFunctor.IsStronglyCocartesian g (pushLift X g) where
  universal_property' {Y'} g' φ' hφ' := by
    have hc : φ'.onCarrier = ⇑(g ≫ g') := (isHomLift_iff (g ≫ g') φ').mp hφ'
    refine ⟨⟨g', φ'.fn, ?_⟩, ⟨(isHomLift_iff (X := pushObj X g) (Y := Y') g' _).mpr rfl, ?_⟩, ?_⟩
    · rintro _ a ⟨s, rfl, h⟩
      have := φ'.preserves s a h
      rw [hc] at this
      exact this
    · exact hom_ext hc.symm rfl
    · rintro χ ⟨hχ, hχφ⟩
      have h₁ : χ.onCarrier = ⇑g' := (isHomLift_iff (X := pushObj X g) (Y := Y') g' χ).mp hχ
      have h₂ := congrArg Hom.fn hχφ
      exact hom_ext h₁ h₂

/-- **`carrierFunctor` is an opfibration**: every carrier map out of
`X.carrier` has a strongly cocartesian lift, whose codomain lies over `S`
definitionally (`pushObj X g`). -/
theorem carrierFunctor_exists_isStronglyCocartesian (X : EncCat₂) {S : Type}
    (g : carrierFunctor.obj X ⟶ S) :
    ∃ (Y : EncCat₂) (φ : X ⟶ Y) (_ : carrierFunctor.obj Y = S),
      carrierFunctor.IsStronglyCocartesian g φ :=
  ⟨pushObj X g, pushLift X g, rfl, inferInstance⟩

end EncCat₂

end Silmaril

module

public import Silmaril.Logic.Institution.Grothendieck.Amalgamation
public import Silmaril.Logic.Institution.Examples.Propositional
public import Silmaril.Logic.Institution.Examples.Equational
public import Silmaril.Logic.Institution.Grothendieck.Examples.CatPullback
public import Silmaril.Logic.Institution.Grothendieck.Examples.EQPushout
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

/-!
# Semi-exactness of propositional and equational logic

* Propositional logic over `Type` (whose pushouts Mathlib provides) is semi-exact: valuations
  agreeing on the common variables of a pushout of signatures amalgamate uniquely.
* Many-sorted equational signatures have pushouts, constructed sort-wise and symbol-wise
  (`EQ.hasPushouts`), and equational logic is semi-exact.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory Limits Examples

/-- The model functors of a commuting square of signatures commute. -/
theorem modHom_comm {Sign : Type*} [Category Sign] (I : Sign ⥤ Room.{0, 0, 1})
    {S S₁ S₂ S' : Sign} {f₁ : S ⟶ S₁} {f₂ : S ⟶ S₂} {g₁ : S₁ ⟶ S'} {g₂ : S₂ ⟶ S'}
    (w : f₁ ≫ g₁ = f₂ ≫ g₂) : modHom I g₁ ≫ modHom I f₁ = modHom I g₂ ≫ modHom I f₂ := by
  apply Cat.Hom.ext
  change (I.map g₁).mod ⋙ (I.map f₁).mod = (I.map g₂).mod ⋙ (I.map f₂).mod
  rw [← Room.comp_mod, ← Room.comp_mod, ← I.map_comp, ← I.map_comp, w]

namespace PL.Amalgamation

open Examples.PL

theorem model_ext {P : Type} {v v' : Model P} (h : ∀ x, v.val x = v'.val x) : v = v' := by
  obtain ⟨v⟩ := v
  obtain ⟨v'⟩ := v'
  exact congrArg ULift.up (funext h)

variable {S S₁ S₂ S' : Type} {f₁ : S ⟶ S₁} {f₂ : S ⟶ S₂} {g₁ : S₁ ⟶ S'} {g₂ : S₂ ⟶ S'}

theorem cover (h : IsPushout f₁ f₂ g₁ g₂) (x : S') : (∃ x₁, g₁ x₁ = x) ∨ ∃ x₂, g₂ x₂ = x := by
  have := h.hom_ext (W := Prop)
    (k := TypeCat.ofHom fun x => (∃ x₁, g₁ x₁ = x) ∨ ∃ x₂, g₂ x₂ = x)
    (l := TypeCat.ofHom fun _ => True)
    (ConcreteCategory.hom_ext _ _ fun x => eq_true (Or.inl ⟨x, rfl⟩))
    (ConcreteCategory.hom_ext _ _ fun x => eq_true (Or.inr ⟨x, rfl⟩))
  exact of_eq_true (ConcreteCategory.congr_hom this x)

theorem model_ext_of_reducts (h : IsPushout f₁ f₂ g₁ g₂) {v v' : Model S'}
    (h₁ : (Model.reduct g₁).obj v = (Model.reduct g₁).obj v')
    (h₂ : (Model.reduct g₂).obj v = (Model.reduct g₂).obj v') : v = v' := by
  refine model_ext fun x => ?_
  rcases cover h x with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact congrArg (fun m : Model S₁ => m.val x) h₁
  · exact congrArg (fun m : Model S₂ => m.val x) h₂

end PL.Amalgamation

/-- Propositional logic is semi-exact: on a pushout of sets of propositional variables, two
valuations agreeing on the common variables have exactly one common extension.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Definition 3.10
(PDF page 10); propositional logic is the institution CPL of
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4 (after
Definition 4.2), whose signature category is `Type`. -/
theorem PL.semiExact : SemiExact PL.institution := by
  intro S S₁ S₂ S' f₁ f₂ g₁ g₂ h
  refine CatPullback.isPullback_of_amalgamation (modHom_comm _ h.w) ?_ ?_
  · intro (v₁ : PL.Model S₁) (v₂ : PL.Model S₂) hv
    have hv' : ∀ x, v₁.val (f₁ x) = v₂.val (f₂ x) := fun x =>
      congrArg (fun m : PL.Model S => m.val x) hv
    let d := h.desc (TypeCat.ofHom v₁.val) (TypeCat.ofHom v₂.val)
      (ConcreteCategory.hom_ext _ _ hv')
    have hd₁ : ∀ x, d (g₁ x) = v₁.val x := ConcreteCategory.congr_hom (h.inl_desc _ _ _)
    have hd₂ : ∀ x, d (g₂ x) = v₂.val x := ConcreteCategory.congr_hom (h.inr_desc _ _ _)
    refine ⟨(ULift.up fun x => d x : PL.Model S'), ⟨PL.Amalgamation.model_ext hd₁,
      PL.Amalgamation.model_ext hd₂⟩, fun v hv => ?_⟩
    exact PL.Amalgamation.model_ext_of_reducts h (hv.1.trans (PL.Amalgamation.model_ext hd₁).symm)
      (hv.2.trans (PL.Amalgamation.model_ext hd₂).symm)
  · intro (p : PL.Model S') (p' : PL.Model S') u₁ u₂ _
    refine ⟨⟨fun x hx => ?_⟩, ⟨rfl, rfl⟩, fun u _ => rfl⟩
    rcases PL.Amalgamation.cover h x with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact u₁.down x hx
    · exact u₂.down x hx

/-- The category of many-sorted equational signatures has pushouts, computed on sorts and on
operation symbols.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 50
(the category of signatures). -/
theorem EQ.hasPushouts : HasPushouts EQ.Signature :=
  @hasPushouts_of_hasColimit_span _ _ fun {_ _ _ f₁ f₂} => (EQ.pushout_isPushout f₁ f₂).hasPushout

/-- Many-sorted equational logic is semi-exact.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Definition 3.10
(PDF page 10: "many sorted logics tend to be exact"). -/
theorem EQ.semiExact : SemiExact EQ.institution := by
  intro S S₁ S₂ S' f₁ f₂ g₁ g₂ h
  have hsq : ∀ A : EQ.Algebra S', (EQ.Algebra.reduct f₁).obj ((EQ.Algebra.reduct g₁).obj A) =
      (EQ.Algebra.reduct f₂).obj ((EQ.Algebra.reduct g₂).obj A) := fun A => by
    change (EQ.Algebra.reduct (f₁ ≫ g₁)).obj A = (EQ.Algebra.reduct (f₂ ≫ g₂)).obj A
    rw [h.w]
  refine CatPullback.isPullback_of_amalgamation (modHom_comm _ h.w) ?_ ?_
  · intro (M₁ : EQ.Algebra S₁) (M₂ : EQ.Algebra S₂) hM
    obtain ⟨M, hM₁, hM₂⟩ := EQ.exists_amalgam h M₁ M₂ hM
    exact ⟨M, ⟨hM₁, hM₂⟩, fun N hN =>
      EQ.algebra_ext h (hN.1.trans hM₁.symm) (hN.2.trans hM₂.symm)⟩
  · intro (p : EQ.Algebra S') (p' : EQ.Algebra S') u₁ u₂ hu
    change (EQ.Algebra.reduct g₁).obj p ⟶ (EQ.Algebra.reduct g₁).obj p' at u₁
    change (EQ.Algebra.reduct g₂).obj p ⟶ (EQ.Algebra.reduct g₂).obj p' at u₂
    change (EQ.Algebra.reduct f₁).map u₁ ≍ (EQ.Algebra.reduct f₂).map u₂ at hu
    obtain ⟨a, ha₁, ha₂⟩ := EQ.exists_glue h (fun s => p.carrier s → p'.carrier s) u₁.map u₂.map
      (EQ.Algebra.Hom.map_heq (hsq p) (hsq p') hu)
    let u : p ⟶ p' := ⟨a, fun {n w s} o args => by
      rcases EQ.ops_cover h o with ⟨w₁, s₁, o₁, rfl, rfl, ho⟩ | ⟨w₁, s₁, o₁, rfl, rfl, ho⟩
      · obtain rfl := eq_of_heq ho
        have := u₁.map_op o₁ args
        simp only [Function.comp_apply, ha₁]
        exact this
      · obtain rfl := eq_of_heq ho
        have := u₂.map_op o₁ args
        simp only [Function.comp_apply, ha₂]
        exact this⟩
    refine ⟨u, ⟨EQ.Algebra.Hom.ext' fun s x => congrFun (ha₁ s) x,
      EQ.Algebra.Hom.ext' fun s x => congrFun (ha₂ s) x⟩, fun v hv => ?_⟩
    refine EQ.Algebra.Hom.ext' fun s x => ?_
    rcases EQ.sorts_cover h s with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · have := congrArg (fun φ : (EQ.Algebra.reduct g₁).obj p ⟶ (EQ.Algebra.reduct g₁).obj p' =>
        φ.map s x) hv.1
      exact this.trans (congrFun (ha₁ s) x).symm
    · have := congrArg (fun φ : (EQ.Algebra.reduct g₂).obj p ⟶ (EQ.Algebra.reduct g₂).obj p' =>
        φ.map s x) hv.2
      exact this.trans (congrFun (ha₂ s) x).symm

end Silmaril.Logic.Institution

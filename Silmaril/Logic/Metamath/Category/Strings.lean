module

public import Silmaril.Logic.Metamath.Category.Functor

@[expose] public section

/-!
# The string side of the category

For an unambiguous grammar, flattening is injective on well-formed tree
assertions (`Grammar.TAssertion.flatten_injective`): the floating hypotheses
and disjointness conditions are copied, and trees of the same sort with the
same flattening in the (shared, functional) variable context are equal.

On the full subcategory `GAxSet.Unamb` of objects with unambiguous grammars,
string derivability on flattened well-formed assertions is therefore a functor
`GAxSet.toStringPropSystems`: a morphism acts on a string by parsing it back
to its unique tree assertion, translating, and flattening. Flattening is a
natural isomorphism from tree derivability to this string functor
(`GAxSet.flattenIso`), by `Grammar.tderivable_iff_derivable`.
-/

namespace Silmaril.Logic.Metamath

open CategoryTheory Grammar Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.InferenceSystemCat

universe u

theorem List.eq_of_map_eq_of_injOn {α β : Type*} {f : α → β} {l₁ l₂ : List α}
    (h : l₁.map f = l₂.map f) (hinj : ∀ x ∈ l₁, ∀ y ∈ l₂, f x = f y → x = y) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons x l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons y l₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hinj x (by simp) y (by simp) h.1,
        ih h.2 fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb])]

namespace Grammar

variable {L C V : Type u} [DecidableEq V] {G : Grammar L C V}

namespace TAssertion

/-- Assertions with the same flattening have the same variable context. -/
theorem ctx_eq_of_flatten_eq {A B : TAssertion L C V} (h : A.flatten G = B.flatten G) :
    A.ctx = B.ctx := by
  funext v s
  apply propext
  rw [← float_mem_flatten (G := G), h, float_mem_flatten]

/-- For an unambiguous grammar, flattening is injective on well-formed tree
assertions. -/
theorem flatten_injective (hG : G.Unambiguous) {A B : TAssertion L C V} (hA : A.WellFormed G)
    (hB : B.WellFormed G) (h : A.flatten G = B.flatten G) : A = B := by
  have hctx := ctx_eq_of_flatten_eq h
  have hfun := functional_ctx hA.floats_nodup
  have key : ∀ e e' : TExpr L C V, e.WellTyped G A.ctx → e'.WellTyped G B.ctx →
      e.flatten G = e'.flatten G → e = e' := by
    rintro ⟨c, t⟩ ⟨c', t'⟩ ⟨s, hs, ht⟩ ⟨s', hs', ht'⟩ he
    simp only [TExpr.flatten, Expr.mk.injEq] at he hs hs' ht ht'
    obtain ⟨rfl, hflat⟩ := he
    rw [hs] at hs'
    cases hs'
    rw [← hctx] at ht'
    rw [hG A.ctx hfun s t t' ht ht' hflat]
  have hhyps : A.hyps = B.hyps := by
    refine List.eq_of_map_eq_of_injOn (f := THyp.flatten G) (congrArg Assertion.hyps h) ?_
    intro x hx y hy hxy
    cases x with
    | float c v =>
      cases y with
      | float c' v' => simpa [THyp.flatten] using hxy
      | ess e' => simp [THyp.flatten] at hxy
    | ess e =>
      cases y with
      | float c' v' => simp [THyp.flatten] at hxy
      | ess e' =>
        simp only [THyp.flatten, Hyp.ess.injEq] at hxy
        rw [key e e' (hA.ess_wellTyped e (mem_essentials.2 hx))
          (hB.ess_wellTyped e' (mem_essentials.2 hy)) hxy]
  have hdv : A.dv = B.dv := congrArg Assertion.dv h
  have hc : A.concl = B.concl :=
    key _ _ hA.concl_wellTyped hB.concl_wellTyped (congrArg Assertion.concl h)
  cases A; cases B
  simp only at hhyps hdv hc
  rw [hhyps, hdv, hc]

end TAssertion

end Grammar

namespace GAxSet

/-- Objects whose grammar is unambiguous. -/
def IsUnambiguous : ObjectProperty GAxSet.{u} := fun X => X.G.Unambiguous

/-- The full subcategory of objects with unambiguous grammars. -/
abbrev Unamb := IsUnambiguous.{u}.FullSubcategory

/-- The flattenings of the well-formed tree assertions of `X`. -/
abbrev FlatAssertion (X : GAxSet.{u}) : Type u :=
  {a : Assertion X.C X.V // ∃ A : TWFAssertion X.G, A.1.flatten X.G = a}

/-- String derivability on flattened well-formed assertions. -/
def stringPropSystem (X : GAxSet.{u}) : PropSystems.{u} where
  Conclusion := FlatAssertion X
  Derivation a := Derivable (X.G.axioms X.axioms) a.1

variable {X Y : GAxSet.{u}}

/-- A well-formed tree assertion with the given flattening. -/
noncomputable def parse (a : (stringPropSystem X).Conclusion) : (propSystem X).Conclusion :=
  a.2.choose

theorem flatten_parse (a : (stringPropSystem X).Conclusion) :
    (parse a).1.flatten X.G = a.1 := a.2.choose_spec

/-- The flattening of a well-formed tree assertion. -/
def flat (A : (propSystem X).Conclusion) : (stringPropSystem X).Conclusion :=
  ⟨A.1.flatten X.G, A, rfl⟩

theorem parse_flat (hX : X.G.Unambiguous) (A : (propSystem X).Conclusion) :
    parse (flat A) = A :=
  Subtype.ext (TAssertion.flatten_injective hX (parse (flat A)).2 A.2 (flatten_parse (flat A)))

theorem flat_parse (a : (stringPropSystem X).Conclusion) : flat (parse a) = a :=
  Subtype.ext (flatten_parse a)

theorem derivable_iff_parse (hX : X.G.Unambiguous) (a : (stringPropSystem X).Conclusion) :
    Derivable (X.G.axioms X.axioms) a.1 ↔ TDerivable X.G X.axioms (parse a).1 := by
  rw [← flatten_parse a]
  exact (tderivable_iff_derivable hX X.wf (parse a).2).symm

/-- The action of a morphism on flattened assertions: parse, translate, flatten. -/
noncomputable def stringMap {X Y : Unamb.{u}} (f : X ⟶ Y) :
    stringPropSystem X.obj ⟶ stringPropSystem Y.obj where
  map a := flat ((propMap f.hom).map (parse a))
  mapDerivation {a} h :=
    ((propMap f.hom).mapDerivation ((derivable_iff_parse X.property a).1 h)).flatten

/-- String derivability of flattened assertions, functorially in objects with
unambiguous grammars. -/
noncomputable def toStringPropSystems : Unamb.{u} ⥤ PropSystems.{u} where
  obj X := stringPropSystem X.obj
  map := stringMap
  map_id X := PropSystems.hom_ext (funext fun a => by
    have h : flat ((propMap (𝟙 X.obj)).map (parse a)) = a := by
      rw [propMap_id]
      exact flat_parse a
    exact h)
  map_comp {X Y Z} f g := PropSystems.hom_ext (funext fun a => by
    have h : flat ((propMap (f.hom ≫ g.hom)).map (parse a)) =
        flat ((propMap g.hom).map (parse (flat ((propMap f.hom).map (parse a))))) := by
      rw [parse_flat Y.property, propMap_comp]
      rfl
    exact h)

/-- On objects with unambiguous grammars, flattening is a natural isomorphism
from tree derivability to string derivability of flattened assertions. -/
noncomputable def flattenIso :
    IsUnambiguous.ι ⋙ toPropSystems.{u} ≅ toStringPropSystems.{u} :=
  NatIso.ofComponents (fun X =>
    { hom := ⟨flat, fun h => TDerivable.flatten h⟩
      inv := ⟨parse, fun {a} h => (derivable_iff_parse X.property a).1 h⟩
      hom_inv_id := PropSystems.hom_ext (funext (parse_flat X.property))
      inv_hom_id := PropSystems.hom_ext (funext flat_parse) }) (by
    intro X Y f
    refine PropSystems.hom_ext (funext fun A => ?_)
    have h : ∀ B : (propSystem X.obj).Conclusion,
        flat ((propMap f.hom).map B) = flat ((propMap f.hom).map (parse (flat B))) :=
      fun B => by rw [parse_flat X.property]
    exact h A)

end GAxSet

end Silmaril.Logic.Metamath

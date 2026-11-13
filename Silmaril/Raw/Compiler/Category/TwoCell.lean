module

public import Silmaril.Compile.Category.Pass
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

@[expose] public section

/-!
# 2-cells between conventions, and factoring compilation routes

Conventions `L ⟶ L'` are ordered (`Convention.le_def`: same interface map, fewer matched
observations), and composition is monotone (`Convention.comp_mono`), so languages,
conventions and this order form a locally thin 2-category. This file makes its 2-cells
first-class and puts the existing theorems behind them:

* `TwoCell c d` (notation `c ⟹ d`): a 2-cell between parallel conventions, as data (the
  interface equation and the inclusion of matchings). There is at most one
  (`TwoCell.eq`), so every equation between 2-cells (associativity, units, the interchange law,
  horizontal composition as two whiskerings) holds; they are stated for use by `rw`.
* Vertical composition `TwoCell.vcomp`, horizontal composition `TwoCell.hcomp`, whiskering
  `TwoCell.whiskerLeft`, `TwoCell.whiskerRight`, and the structural 2-cells `TwoCell.ofEq`,
  `assoc`, `leftUnitor`, `rightUnitor`.
* `Language.bicategory`: the 2-category as a Mathlib `Bicategory`, strict
  (`Language.bicategory_strict`), with the convention order as hom-categories.
* Action on validity and passes: a 2-cell `α : c ⟹ d` gives `Valid c ≤ Valid d`
  (`TwoCell.valid`, from `valid_mono`) and moves a pass along it (`Pass.along`). Moving is
  functorial and natural for pass composition: `Pass.along_comp_along` (horizontal),
  `Pass.comp_along_left`, `Pass.comp_along_right` (whiskering).
* Read-back rigidity (`Convention.ReadBack.eq_of_twoCell`): between two read-back conventions
  every 2-cell is an equation. 2-cells carry information only when a convention matches one
  target observation to several source observations.
* Path factoring: `FactorsVia a c d F e` says that every valid compilation at `a` of a program of
  `F` goes through `e p` along `c` then `d`; `Factors a c d F` is its existential shadow.
  `Realises.factorsVia` (from `Realises.factor_of_le`) builds one from a realising elaboration
  and one 2-cell `a ⟹ c ≫ d`; with a 2-cell back, `c ≫ d ⟹ a`, the route `c ≫ d` and `a`
  have the same valid compilations on `F` (`Factors.valid_iff`). Factorizations compose along
  paths (`FactorsVia.trans`), and two routes linked by 2-cells both ways, each realised,
  are interchangeable (`route_iff`).

So a new compilation route `c ≫ d` to an established convention `a` costs its two local passes
and one 2-cell `c ≫ d ⟹ a` (`Pass.route`); the converse direction (every compilation at `a`
goes through the route) costs a realising elaboration and one 2-cell `a ⟹ c ≫ d`.

The instance on the Ail → Core → Mir triangle is `Silmaril.Compile.C.Sem.TriangleTwoCell`.

Source: Koenig and Shao, *CompCertO: compiling certified open C components*, PLDI 2021, Definition 5.1 (refinement of
simulation conventions, the 2-cells here without Kripke worlds).
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

variable {L L' L'' L''' : Language.{u}}

/-- A 2-cell `c ⟹ d` between parallel conventions: `d` translates interfaces as `c` does and
admits every target observation that `c` admits. -/
structure TwoCell (c d : L ⟶ L') : Type where
  /-- Both conventions translate interfaces alike. -/
  Φ_eq : c.Φ = d.Φ
  /-- Every matching of `c` is a matching of `d`. -/
  R_le : c.R ≤ d.R

@[inherit_doc] scoped infix:50 " ⟹ " => TwoCell

namespace TwoCell

/-- There is at most one 2-cell between two conventions. -/
instance (c d : L ⟶ L') : Subsingleton (c ⟹ d) := ⟨fun ⟨_, _⟩ ⟨_, _⟩ => rfl⟩

theorem eq {c d : L ⟶ L'} (α β : c ⟹ d) : α = β := Subsingleton.elim α β

/-- The order of a 2-cell. -/
theorem le {c d : L ⟶ L'} (α : c ⟹ d) : c ≤ d := ⟨α.Φ_eq, α.R_le⟩

/-- The 2-cell of an inequality. -/
def ofLe {c d : L ⟶ L'} (h : c ≤ d) : c ⟹ d := ⟨h.1, h.2⟩

theorem nonempty_iff_le {c d : L ⟶ L'} : Nonempty (c ⟹ d) ↔ c ≤ d :=
  ⟨fun ⟨α⟩ => α.le, fun h => ⟨ofLe h⟩⟩

/-- The identity 2-cell. -/
def id (c : L ⟶ L') : c ⟹ c := ofLe le_rfl

/-- The 2-cell of an equation of conventions. -/
def ofEq {c d : L ⟶ L'} (h : c = d) : c ⟹ d := ofLe h.le

/-- Vertical composition. -/
def vcomp {c d e : L ⟶ L'} (α : c ⟹ d) (β : d ⟹ e) : c ⟹ e := ofLe (α.le.trans β.le)

/-- Horizontal composition, along composition of conventions. -/
def hcomp {c c' : L ⟶ L'} {d d' : L' ⟶ L''} (α : c ⟹ c') (β : d ⟹ d') : c ≫ d ⟹ c' ≫ d' :=
  ofLe (Convention.comp_mono α.le β.le)

/-- Left whiskering: precompose both sides of a 2-cell with a convention. -/
def whiskerLeft (c : L ⟶ L') {d d' : L' ⟶ L''} (β : d ⟹ d') : c ≫ d ⟹ c ≫ d' :=
  hcomp (id c) β

/-- Right whiskering: postcompose both sides of a 2-cell with a convention. -/
def whiskerRight {c c' : L ⟶ L'} (α : c ⟹ c') (d : L' ⟶ L'') : c ≫ d ⟹ c' ≫ d :=
  hcomp α (id d)

/-- The associator. -/
def assoc (c : L ⟶ L') (d : L' ⟶ L'') (e : L'' ⟶ L''') : (c ≫ d) ≫ e ⟹ c ≫ d ≫ e :=
  ofEq (Category.assoc c d e)

/-- The inverse associator. -/
def assocInv (c : L ⟶ L') (d : L' ⟶ L'') (e : L'' ⟶ L''') : c ≫ d ≫ e ⟹ (c ≫ d) ≫ e :=
  ofEq (Category.assoc c d e).symm

/-- The left unitor. -/
def leftUnitor (c : L ⟶ L') : 𝟙 L ≫ c ⟹ c := ofEq (Category.id_comp c)

/-- The right unitor. -/
def rightUnitor (c : L ⟶ L') : c ≫ 𝟙 L' ⟹ c := ofEq (Category.comp_id c)

/-! ### Laws (all by thinness) -/

section Laws

variable {c c' c'' c''' : L ⟶ L'} {d d' d'' : L' ⟶ L''}

theorem id_vcomp (α : c ⟹ c') : (id c).vcomp α = α := eq _ _
theorem vcomp_id (α : c ⟹ c') : α.vcomp (id c') = α := eq _ _
theorem vcomp_assoc (α : c ⟹ c') (β : c' ⟹ c'') (γ : c'' ⟹ c''') :
    (α.vcomp β).vcomp γ = α.vcomp (β.vcomp γ) := eq _ _

/-- The interchange law. -/
theorem interchange (α : c ⟹ c') (α' : c' ⟹ c'') (β : d ⟹ d') (β' : d' ⟹ d'') :
    (α.vcomp α').hcomp (β.vcomp β') = (α.hcomp β).vcomp (α'.hcomp β') := eq _ _

/-- Horizontal composition is whiskering, in either order. -/
theorem hcomp_eq_whisker (α : c ⟹ c') (β : d ⟹ d') :
    α.hcomp β = (α.whiskerRight d).vcomp (whiskerLeft c' β) := eq _ _

theorem hcomp_eq_whisker' (α : c ⟹ c') (β : d ⟹ d') :
    α.hcomp β = (whiskerLeft c β).vcomp (α.whiskerRight d') := eq _ _

theorem hcomp_id : (id c).hcomp (id d) = id (c ≫ d) := eq _ _

end Laws

/-! ### Action on validity -/

/-- A 2-cell enlarges the valid compilations. -/
theorem valid {c d : L ⟶ L'} (α : c ⟹ d) : Valid c ≤ Valid d := valid_mono α.le

/-- A 2-cell enlarges the translation of every specification. -/
theorem lift_subset {c d : L ⟶ L'} (α : c ⟹ d) (B : Set L.Obs) : c.lift B ⊆ d.lift B :=
  Convention.lift_le_of_le α.le B

/-- The lax law through a 2-cell: valid compilations along the route `c ≫ d` are valid at every
convention above it. -/
theorem valid_comp {c : L ⟶ L'} {d : L' ⟶ L''} {a : L ⟶ L''} (β : c ≫ d ⟹ a) :
    Relation.Comp (Valid c) (Valid d) ≤ Valid a :=
  (valid_comp_le c d).trans β.valid

end TwoCell

/-! ### Read-back rigidity -/

/-- Between read-back conventions, a 2-cell is an equation: a read-back matches each target
observation to exactly one source observation, so a larger read-back reads back alike. -/
theorem Convention.ReadBack.eq_of_twoCell {c d : L ⟶ L'} (hc : Convention.ReadBack c)
    (hd : Convention.ReadBack d) (α : c ⟹ d) : c = d := by
  have hg : ∀ o', hc.g o' = hd.g o' := fun o' =>
    (hd.spec _ _).1 (α.R_le _ _ ((hc.spec _ _).2 rfl))
  refine Convention.ext α.Φ_eq (funext fun o => funext fun o' => propext ?_)
  rw [hc.spec, hd.spec, hg]

/-- Between read-back conventions, a 2-cell exists exactly when they are equal. -/
theorem Convention.ReadBack.nonempty_twoCell_iff {c d : L ⟶ L'} (hc : Convention.ReadBack c)
    (hd : Convention.ReadBack d) : Nonempty (c ⟹ d) ↔ c = d :=
  ⟨fun ⟨α⟩ => hc.eq_of_twoCell hd α, fun h => ⟨TwoCell.ofEq h⟩⟩

/-! ### Moving passes along 2-cells -/

namespace Pass

/-- Move a pass along a 2-cell (`Pass.weaken`). -/
def along {c d : L ⟶ L'} (P : Pass c) (α : c ⟹ d) : Pass d := P.weaken α.le

@[simp] theorem along_run {c d : L ⟶ L'} (P : Pass c) (α : c ⟹ d) : (P.along α).run = P.run :=
  rfl

theorem along_id {c : L ⟶ L'} (P : Pass c) : P.along (TwoCell.id c) = P := Pass.ext rfl

theorem along_along {c d e : L ⟶ L'} (P : Pass c) (α : c ⟹ d) (β : d ⟹ e) :
    (P.along α).along β = P.along (α.vcomp β) := Pass.ext rfl

/-- Moving passes is natural for composition: horizontal composition of 2-cells. -/
theorem along_comp_along {c c' : L ⟶ L'} {d d' : L' ⟶ L''} (P : Pass c) (Q : Pass d)
    (α : c ⟹ c') (β : d ⟹ d') : P.along α ≫ₚ Q.along β = (P ≫ₚ Q).along (α.hcomp β) :=
  Pass.ext rfl

/-- Moving the first pass is right whiskering. -/
theorem comp_along_left {c c' : L ⟶ L'} {d : L' ⟶ L''} (P : Pass c) (Q : Pass d)
    (α : c ⟹ c') : P.along α ≫ₚ Q = (P ≫ₚ Q).along (α.whiskerRight d) := Pass.ext rfl

/-- Moving the second pass is left whiskering. -/
theorem comp_along_right {c : L ⟶ L'} {d d' : L' ⟶ L''} (P : Pass c) (Q : Pass d)
    (β : d ⟹ d') : P ≫ₚ Q.along β = (P ≫ₚ Q).along (TwoCell.whiskerLeft c β) := Pass.ext rfl

/-- **A new route costs one 2-cell.** Two passes along `c ≫ d` and a 2-cell into an
established convention `a` give a pass at `a`. -/
def route {c : L ⟶ L'} {d : L' ⟶ L''} {a : L ⟶ L''} (P : Pass c) (Q : Pass d)
    (β : c ≫ d ⟹ a) : Pass a :=
  (P ≫ₚ Q).along β

@[simp] theorem route_run {c : L ⟶ L'} {d : L' ⟶ L''} {a : L ⟶ L''} (P : Pass c) (Q : Pass d)
    (β : c ≫ d ⟹ a) (p : L.Prog) : (P.route Q β).run p = (P.run p).bind Q.run := rfl

end Pass

/-- A pipeline whose composite convention lies below `a` is a pass at `a`. -/
def Pipeline.along {c a : L ⟶ L'} (P : Pipeline c) (β : c ⟹ a) : Pass a := P.toPass.along β

theorem Pipeline.along_run {c a : L ⟶ L'} (P : Pipeline c) (β : c ⟹ a) :
    (P.along β).run = P.run :=
  P.toPass_run

/-! ### Path factoring -/

section Factoring

variable {L M N O : Language.{u}}

/-- The route `c ≫ d` through `M` captures the compilations at `a` on the fragment `F`, through
the elaboration `e`: every valid compilation at `a` of a program `p` of `F` is a valid
compilation at `d` of `e p`, itself a valid compilation of `p` at `c`. -/
def FactorsVia (a : L ⟶ N) (c : L ⟶ M) (d : M ⟶ N) (F : Set L.Prog) (e : L.Prog → M.Prog) :
    Prop :=
  ∀ p ∈ F, ∀ r, Valid a p r → Valid c p (e p) ∧ Valid d (e p) r

/-- The route `c ≫ d` through `M` captures the compilations at `a` on the fragment `F`: every
valid compilation at `a` of a program of `F` goes through some intermediate program. -/
def Factors (a : L ⟶ N) (c : L ⟶ M) (d : M ⟶ N) (F : Set L.Prog) : Prop :=
  ∀ p ∈ F, ∀ r, Valid a p r → Relation.Comp (Valid c) (Valid d) p r

theorem FactorsVia.factors {a : L ⟶ N} {c : L ⟶ M} {d : M ⟶ N} {F : Set L.Prog}
    {e : L.Prog → M.Prog} (h : FactorsVia a c d F e) : Factors a c d F :=
  fun p hp r hv => ⟨e p, h p hp r hv⟩

/-- **Factoring from one 2-cell.** A realising elaboration and a 2-cell `a ⟹ c ≫ d` factor
every valid compilation at `a` through the route. -/
theorem Realises.factorsVia {c : L ⟶ M} {F : Set L.Prog} {e : L.Prog → M.Prog}
    (h : Realises c F e) {d : M ⟶ N} {a : L ⟶ N} (α : a ⟹ c ≫ d) : FactorsVia a c d F e :=
  fun _ hp _ hv => h.factor hp (α.valid _ _ hv)

/-- With a 2-cell back, the route and `a` have the same valid compilations on `F`. -/
theorem Factors.valid_iff {a : L ⟶ N} {c : L ⟶ M} {d : M ⟶ N} {F : Set L.Prog}
    (h : Factors a c d F) (β : c ≫ d ⟹ a) {p : L.Prog} (hp : p ∈ F) (r : N.Prog) :
    Relation.Comp (Valid c) (Valid d) p r ↔ Valid a p r :=
  ⟨fun hv => β.valid_comp p r hv, h p hp r⟩

theorem FactorsVia.mono {a : L ⟶ N} {c : L ⟶ M} {d : M ⟶ N} {F G : Set L.Prog}
    {e : L.Prog → M.Prog} (h : FactorsVia a c d F e) (hG : G ⊆ F) : FactorsVia a c d G e :=
  fun p hp => h p (hG hp)

/-- Factorizations are inherited along a 2-cell into the factored convention. -/
theorem FactorsVia.of_twoCell {a a' : L ⟶ N} {c : L ⟶ M} {d : M ⟶ N} {F : Set L.Prog}
    {e : L.Prog → M.Prog} (h : FactorsVia a c d F e) (α : a' ⟹ a) : FactorsVia a' c d F e :=
  fun p hp r hv => h p hp r (α.valid _ _ hv)

/-- Factorizations move along 2-cells out of the legs. -/
theorem FactorsVia.along {a : L ⟶ N} {c c' : L ⟶ M} {d d' : M ⟶ N} {F : Set L.Prog}
    {e : L.Prog → M.Prog} (h : FactorsVia a c d F e) (α : c ⟹ c') (β : d ⟹ d') :
    FactorsVia a c' d' F e :=
  fun p hp r hv => (h p hp r hv).imp (α.valid _ _) (β.valid _ _)

/-- **Factoring along a path.** If `a` factors through `c ≫ d`, and `d` factors through
`c' ≫ d'` on the programs that `e` produces, then `a` factors through `(c ≫ c') ≫ d'`. -/
theorem FactorsVia.trans {a : L ⟶ O} {c : L ⟶ M} {d : M ⟶ O} {c' : M ⟶ N} {d' : N ⟶ O}
    {F : Set L.Prog} {G : Set M.Prog} {e : L.Prog → M.Prog} {e' : M.Prog → N.Prog}
    (h : FactorsVia a c d F e) (h' : FactorsVia d c' d' G e') (hFG : ∀ p ∈ F, e p ∈ G) :
    FactorsVia a (c ≫ c') d' F (e' ∘ e) := by
  intro p hp r hv
  obtain ⟨h₁, h₂⟩ := h p hp r hv
  obtain ⟨h₃, h₄⟩ := h' (e p) (hFG p hp) r h₂
  exact ⟨valid_comp_le c c' p _ ⟨e p, h₁, h₃⟩, h₄⟩

/-- **Interchangeable routes.** Two routes to `N` related by 2-cells both ways, the second
realised on `F`, have the same composite valid compilations on `F`. -/
theorem route_iff {M' : Language.{u}} {c : L ⟶ M} {d : M ⟶ N} {c' : L ⟶ M'} {d' : M' ⟶ N}
    {F : Set L.Prog} {e : L.Prog → M.Prog} {e' : L.Prog → M'.Prog} (h : Realises c F e)
    (h' : Realises c' F e') (α : c ≫ d ⟹ c' ≫ d') (β : c' ≫ d' ⟹ c ≫ d) {p : L.Prog}
    (hp : p ∈ F) (r : N.Prog) :
    Relation.Comp (Valid c) (Valid d) p r ↔ Relation.Comp (Valid c') (Valid d') p r :=
  ⟨fun hv => ((h'.factorsVia (TwoCell.id _)).factors.valid_iff (TwoCell.id _) hp r).2
      (α.valid_comp p r hv),
    fun hv => ((h.factorsVia (TwoCell.id _)).factors.valid_iff (TwoCell.id _) hp r).2
      (β.valid_comp p r hv)⟩

end Factoring

/-! ### The bicategory of languages -/

/-- Languages, conventions and the convention order form a (locally thin, strict) bicategory,
whose 2-morphisms `c ⟶ d` are those of the preorder category of `Convention L L'`, equivalent
to `TwoCell c d` (`TwoCell.equivHom`). A definition rather than an instance, so that `L ⟶ L'`
keeps elaborating through `Language.category`. -/
@[instance_reducible]
def Language.bicategory : Bicategory.{u, u} Language.{u} where
  toCategoryStruct := Language.category.toCategoryStruct
  homCategory _ _ := inferInstance
  whiskerLeft f _ _ η := (TwoCell.whiskerLeft f (TwoCell.ofLe η.le)).le.hom
  whiskerRight η h := ((TwoCell.ofLe η.le).whiskerRight h).le.hom
  associator f g h := eqToIso (Category.assoc f g h)
  leftUnitor f := eqToIso (Category.id_comp f)
  rightUnitor f := eqToIso (Category.comp_id f)
  whiskerLeft_id _ _ := Subsingleton.elim _ _
  whiskerLeft_comp _ _ _ _ _ _ := Subsingleton.elim _ _
  id_whiskerLeft _ := Subsingleton.elim _ _
  comp_whiskerLeft _ _ _ _ _ := Subsingleton.elim _ _
  id_whiskerRight _ _ := Subsingleton.elim _ _
  comp_whiskerRight _ _ _ := Subsingleton.elim _ _
  whiskerRight_id _ := Subsingleton.elim _ _
  whiskerRight_comp _ _ _ := Subsingleton.elim _ _
  whisker_assoc _ _ _ _ _ := Subsingleton.elim _ _
  whisker_exchange _ _ := Subsingleton.elim _ _
  pentagon _ _ _ _ := Subsingleton.elim _ _
  triangle _ _ := Subsingleton.elim _ _

attribute [local instance] Language.bicategory in
/-- The bicategory of languages is strict: associators and unitors are identities. -/
theorem Language.bicategory_strict : Bicategory.Strict Language.{u} where
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

/-- 2-cells are the 2-morphisms of `Language.bicategory`. -/
def TwoCell.equivHom {c d : L ⟶ L'} : (c ⟹ d) ≃ (c ⟶ d) where
  toFun α := α.le.hom
  invFun η := TwoCell.ofLe η.le
  left_inv _ := TwoCell.eq _ _
  right_inv _ := Subsingleton.elim _ _

end Silmaril.Compile.Category

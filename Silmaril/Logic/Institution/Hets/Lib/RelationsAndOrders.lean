module

public import Silmaril.Logic.Institution.Hets.CASL.FinSig
public import Silmaril.Logic.Institution.Hets.Calculus
public import Silmaril.Logic.Institution.Hets.StructuredSpec

@[expose] public section

/-!
# Selected Hets-library presentations: relations and orders

The specifications `Relation`, `ReflexiveRelation`, `IrreflexiveRelation`,
`AsymmetricRelation`, `AntisymmetricRelation`, `TransitiveRelation`, `PreOrder`, `StrictOrder`,
`PartialOrder` and `TotalOrder` from the Hets library `Basic/RelationsAndOrders` are represented
as finite first-order presentations (`Hets/CASL/FinSig.lean`). This file defines their
signatures and axioms, their development graph over first-order logic
(`graph`), the structured specification of each node (`spec`) and the proof obligation of the
`%implies` annotation in `StrictOrder` (`impliesGoal`).

These are selected formalized presentations, not the output of a bundled CASL parser.
Apart from graph well-foundedness, the proofs are in `Hets/Lib/RelationsAndOrdersProofs.lean`:
they relate the presentations to Mathlib order structures and discharge `impliesGoal`.
See `docs/projects/logic.md#hets` for the scope of the development.

## Development graph

One node per named specification and per anonymous union, renaming and extension, as in Hets'
static analysis; all definition links are global.

* `relation` (`Relation`, no axioms) ⟶ `reflexive`, `irreflexive`, `asymmetric`,
  `antisymmetric`, `transitive` (`Relation then …`, one axiom each).
* `reflexive`, `transitive` ⟶ `reflTrans` (`ReflexiveRelation and TransitiveRelation`)
  ⟶`[~ ↦ ≤]` `preOrder`.
* `irreflexive`, `transitive` ⟶ `irrTrans`; `irrTrans`, `asymmetric` ⟶ `strictBody`
  (`… then %implies AsymmetricRelation`) ⟶`[~ ↦ <]` `strictOrder`. The `%implies` annotation
  is the global theorem link `asymmetric ⇢ irrTrans` (`impliesGoal`).
* `antisymmetric` ⟶`[~ ↦ ≤]` `antisymLe`; `preOrder`, `antisymLe` ⟶ `partialOrder` ⟶
  `totalOrder` (`dichotomy_TotalOrder`).

## References

* `cofi-2004-casl-reference-manual` in `references.bib`, Part V §3 (printed pages 387–389,
  PDF pages 401–403): the library `Basic/RelationsAndOrders`; Part II §5.2.5 (printed page 111,
  PDF page 125): "A well-formed `%implies` annotation holds iff the model class of (SP then
  SP′) is the model class of SP".
* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
  Definitions 4 and 11 (PDF pages 6 and 9): development graphs and theorem links.
-/

namespace Silmaril.Logic.Institution.Hets.Lib.RelationsAndOrders

open CategoryTheory Silmaril.Logic.Institution.Examples Silmaril.Logic.Institution.Hets.CASL
  FinSig

/-! ### Signatures -/

/-- The sort `Elem`. -/
abbrev Elem : Fin 1 := 0

/-- `sort Elem; pred __~__ : Elem × Elem` (`Relation`). -/
def relSig : FinSig where
  nSorts := 1
  sortNames _ := "Elem"
  ops := []
  preds := [{ name := "__~__", arity := 2, args := fun _ => Elem }]

/-- `sort Elem; pred __<=__ : Elem × Elem` (`PreOrder`, `PartialOrder`, `TotalOrder`). -/
def leSig : FinSig where
  nSorts := 1
  sortNames _ := "Elem"
  ops := []
  preds := [{ name := "__<=__", arity := 2, args := fun _ => Elem }]

/-- `sort Elem; pred __<__ : Elem × Elem` (`StrictOrder`). -/
def ltSig : FinSig where
  nSorts := 1
  sortNames _ := "Elem"
  ops := []
  preds := [{ name := "__<__", arity := 2, args := fun _ => Elem }]

/-- The renaming `pred __~__ ↦ __<=__`. -/
def renLe : Mor relSig leSig where
  sorts := id
  ops i := i
  preds i := i
  ops_ar := by decide
  preds_ar := by decide

/-- The renaming `pred __~__ ↦ __<__`. -/
def renLt : Mor relSig ltSig where
  sorts := id
  ops i := i
  preds i := i
  ops_ar := by decide
  preds_ar := by decide

/-! ### Axioms -/

/-- `k` variables of sort `Elem`. -/
abbrev ctx (k : ℕ) : Fin k → Fin 1 := fun _ => Elem

/-- `t ~ u`. -/
def sim {k : ℕ} {Γ : Fin k → Fin 1} (t u : Tm relSig Γ Elem) : Fm relSig Γ :=
  pred (D := relSig) ⟨0, by decide⟩ (![t, u] : Fin 2 → Tm relSig Γ Elem)

/-- `t <= u`. -/
def le {k : ℕ} {Γ : Fin k → Fin 1} (t u : Tm leSig Γ Elem) : Fm leSig Γ :=
  pred (D := leSig) ⟨0, by decide⟩ (![t, u] : Fin 2 → Tm leSig Γ Elem)

/-- `%(refl)%`: `∀ x : Elem • x ~ x`. -/
def reflAx : FOL.Sentence relSig.toSignature :=
  closed (ctx 1) (sim (.var 0) (.var 0))

/-- `%(irrefl)%`: `∀ x : Elem • ¬ x ~ x`. -/
def irreflAx : FOL.Sentence relSig.toSignature :=
  closed (ctx 1) (.not (sim (.var 0) (.var 0)))

/-- `%(asym)%`: `∀ x, y : Elem • ¬ x ~ y if y ~ x` (`x` is variable `1`, `y` variable `0`). -/
def asymAx : FOL.Sentence relSig.toSignature :=
  closed (ctx 2) (imp (sim (.var 0) (.var 1)) (.not (sim (.var 1) (.var 0))))

/-- `%(antisym)%`: `∀ x, y : Elem • x = y if x ~ y ∧ y ~ x`. -/
def antisymAx : FOL.Sentence relSig.toSignature :=
  closed (ctx 2)
    (imp (.and (sim (.var 1) (.var 0)) (sim (.var 0) (.var 1))) (.eq (.var 1) (.var 0)))

/-- `%(trans)%`: `∀ x, y, z : Elem • x ~ z if x ~ y ∧ y ~ z` (`x`, `y`, `z` are variables
`2`, `1`, `0`). -/
def transAx : FOL.Sentence relSig.toSignature :=
  closed (ctx 3)
    (imp (.and (sim (.var 2) (.var 1)) (sim (.var 1) (.var 0))) (sim (.var 2) (.var 0)))

/-- `%(dichotomy_TotalOrder)%`: `∀ x, y : Elem • x <= y ∨ y <= x`. -/
def dichotomyAx : FOL.Sentence leSig.toSignature :=
  closed (ctx 2) (or (le (.var 1) (.var 0)) (le (.var 0) (.var 1)))

/-! ### The development graph -/

/-- The nodes of the development graph. -/
inductive Node : Type
  | relation
  | reflexive
  | irreflexive
  | asymmetric
  | antisymmetric
  | transitive
  /-- `{ReflexiveRelation and TransitiveRelation}` in `PreOrder`. -/
  | reflTrans
  | preOrder
  /-- `IrreflexiveRelation and TransitiveRelation` in `StrictOrder`. -/
  | irrTrans
  /-- `{… then %implies AsymmetricRelation}` in `StrictOrder`. -/
  | strictBody
  | strictOrder
  /-- `AntisymmetricRelation with pred __~__ ↦ __<=__` in `PartialOrder`. -/
  | antisymLe
  | partialOrder
  | totalOrder
  deriving DecidableEq

/-- The finite signature of a node. -/
def finSig : Node → FinSig
  | .preOrder => leSig
  | .antisymLe => leSig
  | .partialOrder => leSig
  | .totalOrder => leSig
  | .strictOrder => ltSig
  | _ => relSig

/-- The first-order signature of a node. -/
abbrev sig (N : Node) : FOL.Signature := (finSig N).toSignature

/-- The identity of the signature of `Relation`. -/
abbrev idR : relSig.toSignature ⟶ relSig.toSignature := (Mor.id relSig).toHom

/-- The identity of the signature of `PreOrder`. -/
abbrev idL : leSig.toSignature ⟶ leSig.toSignature := (Mor.id leSig).toHom

/-- The local axioms of the nodes. -/
def axioms : (N : Node) → Set (FOL.institution.obj (sig N)).Sen
  | .reflexive => {reflAx}
  | .irreflexive => {irreflAx}
  | .asymmetric => {asymAx}
  | .antisymmetric => {antisymAx}
  | .transitive => {transAx}
  | .totalOrder => {dichotomyAx}
  | _ => ∅

/-- The global definition links. -/
def globalDef : (M N : Node) → Set (sig M ⟶ sig N)
  | .relation, .reflexive => {idR}
  | .relation, .irreflexive => {idR}
  | .relation, .asymmetric => {idR}
  | .relation, .antisymmetric => {idR}
  | .relation, .transitive => {idR}
  | .reflexive, .reflTrans => {idR}
  | .transitive, .reflTrans => {idR}
  | .reflTrans, .preOrder => {renLe.toHom}
  | .irreflexive, .irrTrans => {idR}
  | .transitive, .irrTrans => {idR}
  | .irrTrans, .strictBody => {idR}
  | .asymmetric, .strictBody => {idR}
  | .strictBody, .strictOrder => {renLt.toHom}
  | .antisymmetric, .antisymLe => {renLe.toHom}
  | .preOrder, .partialOrder => {idL}
  | .antisymLe, .partialOrder => {idL}
  | .partialOrder, .totalOrder => {idL}
  | _, _ => ∅

/-- The rank of a node: definition links go from lower to higher rank. -/
def rank : Node → ℕ
  | .relation => 0
  | .reflexive => 1
  | .irreflexive => 1
  | .asymmetric => 1
  | .antisymmetric => 1
  | .transitive => 1
  | .reflTrans => 2
  | .irrTrans => 2
  | .antisymLe => 2
  | .preOrder => 3
  | .strictBody => 3
  | .strictOrder => 4
  | .partialOrder => 4
  | .totalOrder => 5

theorem wf : WellFounded fun M N : Node =>
    (globalDef M N).Nonempty ∨ (∅ : Set (sig M ⟶ sig N)).Nonempty ∨
      (∅ : Set (sig N ⟶ sig M)).Nonempty := by
  refine Subrelation.wf ?_ (InvImage.wf rank wellFounded_lt)
  intro M N h
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · cases M <;> cases N <;> first | exact (hσ : False).elim | (show rank _ < rank _; decide)
  · exact (hσ : False).elim
  · exact (hσ : False).elim

/-- The development graph of the formalized presentations.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §4,
Definition 4 (PDF page 6). -/
def graph : DevGraph FOL.institution where
  Node := Node
  sig := sig
  axioms := axioms
  globalDef := globalDef
  localDef _ _ := ∅
  hidingDef _ _ := ∅
  wf := wf

/-- The proof obligation of `%implies` in `StrictOrder`: the global theorem link
`asymmetric ⇢id irrTrans` (`IrreflexiveRelation and TransitiveRelation` proves
`AsymmetricRelation`). -/
def impliesGoal : graph.ThmLink := .glob .asymmetric .irrTrans idR

/-! ### Structured specifications -/

noncomputable section

/-- Structured specifications over the signature `D`. -/
abbrev Spec (D : FinSig) : Type 1 := StrSpec FOL.institution D.toSignature

/-- `Relation`. -/
def relationSpec : Spec relSig := .basic _ ∅

/-- `Relation then ∀ x • x ~ x`. -/
def reflexiveSpec : Spec relSig := .union (.translate idR relationSpec) (.basic _ {reflAx})

/-- `Relation then ∀ x • ¬ x ~ x`. -/
def irreflexiveSpec : Spec relSig := .union (.translate idR relationSpec) (.basic _ {irreflAx})

/-- `Relation then ∀ x, y • ¬ x ~ y if y ~ x`. -/
def asymmetricSpec : Spec relSig := .union (.translate idR relationSpec) (.basic _ {asymAx})

/-- `Relation then ∀ x, y • x = y if x ~ y ∧ y ~ x`. -/
def antisymmetricSpec : Spec relSig :=
  .union (.translate idR relationSpec) (.basic _ {antisymAx})

/-- `Relation then ∀ x, y, z • x ~ z if x ~ y ∧ y ~ z`. -/
def transitiveSpec : Spec relSig := .union (.translate idR relationSpec) (.basic _ {transAx})

/-- `ReflexiveRelation and TransitiveRelation`. -/
def reflTransSpec : Spec relSig :=
  .union (.translate idR reflexiveSpec) (.translate idR transitiveSpec)

/-- `PreOrder = {ReflexiveRelation and TransitiveRelation} with pred __~__ ↦ __<=__`. -/
def preOrderSpec : Spec leSig := .translate renLe.toHom reflTransSpec

/-- `IrreflexiveRelation and TransitiveRelation`. -/
def irrTransSpec : Spec relSig :=
  .union (.translate idR irreflexiveSpec) (.translate idR transitiveSpec)

/-- `IrreflexiveRelation and TransitiveRelation then %implies AsymmetricRelation`. -/
def strictBodySpec : Spec relSig :=
  .union (.translate idR irrTransSpec) (.translate idR asymmetricSpec)

/-- `StrictOrder = {…} with pred __~__ ↦ __<__`. -/
def strictOrderSpec : Spec ltSig := .translate renLt.toHom strictBodySpec

/-- `AntisymmetricRelation with pred __~__ ↦ __<=__`. -/
def antisymLeSpec : Spec leSig := .translate renLe.toHom antisymmetricSpec

/-- `PartialOrder = PreOrder and AntisymmetricRelation with pred __~__ ↦ __<=__`. -/
def partialOrderSpec : Spec leSig :=
  .union (.translate idL preOrderSpec) (.translate idL antisymLeSpec)

/-- `TotalOrder = PartialOrder then ∀ x, y • x <= y ∨ y <= x`. -/
def totalOrderSpec : Spec leSig := .union (.translate idL partialOrderSpec) (.basic _ {dichotomyAx})

/-- The structured specification of each node. -/
def spec : (N : Node) → Spec (finSig N)
  | .relation => relationSpec
  | .reflexive => reflexiveSpec
  | .irreflexive => irreflexiveSpec
  | .asymmetric => asymmetricSpec
  | .antisymmetric => antisymmetricSpec
  | .transitive => transitiveSpec
  | .reflTrans => reflTransSpec
  | .preOrder => preOrderSpec
  | .irrTrans => irrTransSpec
  | .strictBody => strictBodySpec
  | .strictOrder => strictOrderSpec
  | .antisymLe => antisymLeSpec
  | .partialOrder => partialOrderSpec
  | .totalOrder => totalOrderSpec

end

end Silmaril.Logic.Institution.Hets.Lib.RelationsAndOrders

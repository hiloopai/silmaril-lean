module

public import Silmaril.Logic.Institution.Hets.CASL.FinSig
public import Silmaril.Logic.Institution.Hets.Calculus
public import Silmaril.Logic.Institution.Hets.StructuredSpec

@[expose] public section

/-!
# Selected Hets-library presentations: monoids, groups and rings

The specifications `Monoid`, `CommutativeMonoid`, `Group`, `AbelianGroup` and `Ring` and the
view `AbelianGroup_in_Ring_add` from the Hets library `Basic/Algebra_I` are represented as
finite first-order presentations (`Hets/CASL/FinSig.lean`); the operation attributes `assoc`,
`comm` and `unit e` become axioms. This file defines the signatures, axioms,
development graph over first-order logic (`graph`), structured specification of each
node (`spec`) and the proof obligation of the view (`viewGoal`).

These are selected formalized presentations, not the output of a bundled CASL parser.
Apart from graph well-foundedness, the proofs are in `Hets/Lib/AlgebraIProofs.lean`:
they construct Mathlib model witnesses, recover algebraic structures from models and
discharge `viewGoal`. See `docs/projects/logic.md#hets` for the scope of the development.

## Development graph

* `monoid` (`Monoid`: `assoc`, `unit e`) ⟶ `commMonoid` (`comm`), ⟶ `group` (`%(inv_Group)%`);
  `group`, `commMonoid` ⟶ `abelianGroup` (`Group and CommutativeMonoid`).
* `abelianGroup` ⟶`[e ↦ 0, * ↦ +]` `abGroupAdd`; `abGroupAdd` ⟶ `ringUnion` ⟵ `monoid`
  (`AbelianGroup with … and Monoid with ops e, __*__`, the signature `{0, +, e, *}`);
  `ringUnion` ⟶ `ring` (`%(distr1_Ring)%`, `%(distr2_Ring)%`).
* The view `AbelianGroup_in_Ring_add : AbelianGroup to Ring = ops e ↦ 0, __*__ ↦ __+__` is the
  global theorem link `abelianGroup ⇢ ring` along `viewMor` (`viewGoal`).

The rest of the library (`IntegralDomain`, `Field`, `ExtMonoid`, …), including its use of
`given Nat`/`Int`, subsorts and hiding of sorts, is outside this selected slice.

## References

* `cofi-2004-casl-reference-manual` in `references.bib`, Part V §4 (printed pages 393–394,
  PDF pages 407–408): the library `Basic/Algebra_I`; Part I §2.3 (printed pages 12–13, PDF
  pages 26–27: operation attributes `assoc`, `comm`, `unit`).
* `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5 (printed page 137, PDF
  page 139): the verification semantics of views as global theorem links.
-/

namespace Silmaril.Logic.Institution.Hets.Lib.AlgebraI

open CategoryTheory Silmaril.Logic.Institution.Examples Silmaril.Logic.Institution.Hets.CASL
  FinSig

/-! ### Signatures -/

/-- The sort `Elem`. -/
abbrev Elem : Fin 1 := 0

/-- `sort Elem; ops e : Elem; __*__ : Elem × Elem → Elem` (`Monoid`, `Group`, …). -/
def monSig : FinSig where
  nSorts := 1
  sortNames _ := "Elem"
  ops :=
    [{ name := "e", arity := 0, args := Fin.elim0, res := Elem },
     { name := "__*__", arity := 2, args := fun _ => Elem, res := Elem }]
  preds := []

/-- `sort Elem; ops 0 : Elem; __+__ : Elem × Elem → Elem` (`AbelianGroup` renamed in `Ring`). -/
def addSig : FinSig where
  nSorts := 1
  sortNames _ := "Elem"
  ops :=
    [{ name := "0", arity := 0, args := Fin.elim0, res := Elem },
     { name := "__+__", arity := 2, args := fun _ => Elem, res := Elem }]
  preds := []

/-- `sort Elem; ops 0, e : Elem; __+__, __*__ : Elem × Elem → Elem` (`Ring`). -/
def ringSig : FinSig where
  nSorts := 1
  sortNames _ := "Elem"
  ops :=
    [{ name := "0", arity := 0, args := Fin.elim0, res := Elem },
     { name := "__+__", arity := 2, args := fun _ => Elem, res := Elem },
     { name := "e", arity := 0, args := Fin.elim0, res := Elem },
     { name := "__*__", arity := 2, args := fun _ => Elem, res := Elem }]
  preds := []

/-- The renaming `ops __*__ ↦ __+__, e ↦ 0` (`AbelianGroup with …` in `Ring`). -/
def renAdd : Mor monSig addSig where
  sorts := id
  ops := ![⟨0, by decide⟩, ⟨1, by decide⟩]
  preds := ![]
  ops_ar := by decide
  preds_ar := by decide

/-- The inclusion of `{0, +}` into `{0, +, e, *}`. -/
def inclAdd : Mor addSig ringSig where
  sorts := id
  ops := ![⟨0, by decide⟩, ⟨1, by decide⟩]
  preds := ![]
  ops_ar := by decide
  preds_ar := by decide

/-- The inclusion of `{e, *}` into `{0, +, e, *}` (`Monoid with ops e, __*__` in `Ring`). -/
def inclMon : Mor monSig ringSig where
  sorts := id
  ops := ![⟨2, by decide⟩, ⟨3, by decide⟩]
  preds := ![]
  ops_ar := by decide
  preds_ar := by decide

/-- The morphism of the view `AbelianGroup_in_Ring_add`: `ops e ↦ 0, __*__ ↦ __+__`. -/
def viewMor : Mor monSig ringSig where
  sorts := id
  ops := ![⟨0, by decide⟩, ⟨1, by decide⟩]
  preds := ![]
  ops_ar := by decide
  preds_ar := by decide

/-! ### Axioms -/

/-- `k` variables of sort `Elem`. -/
abbrev ctx (k : ℕ) : Fin k → Fin 1 := fun _ => Elem

/-- `e`. -/
def one {k : ℕ} {Γ : Fin k → Fin 1} : Tm monSig Γ Elem :=
  app (D := monSig) ⟨0, by decide⟩ (fun j : Fin 0 => j.elim0)

/-- `t * u`. -/
def mul {k : ℕ} {Γ : Fin k → Fin 1} (t u : Tm monSig Γ Elem) : Tm monSig Γ Elem :=
  app (D := monSig) ⟨1, by decide⟩ (![t, u] : Fin 2 → Tm monSig Γ Elem)

/-- `0` in `Ring`. -/
def rzero {k : ℕ} {Γ : Fin k → Fin 1} : Tm ringSig Γ Elem :=
  app (D := ringSig) ⟨0, by decide⟩ (fun j : Fin 0 => j.elim0)

/-- `t + u` in `Ring`. -/
def radd {k : ℕ} {Γ : Fin k → Fin 1} (t u : Tm ringSig Γ Elem) : Tm ringSig Γ Elem :=
  app (D := ringSig) ⟨1, by decide⟩ (![t, u] : Fin 2 → Tm ringSig Γ Elem)

/-- `t * u` in `Ring`. -/
def rmul {k : ℕ} {Γ : Fin k → Fin 1} (t u : Tm ringSig Γ Elem) : Tm ringSig Γ Elem :=
  app (D := ringSig) ⟨3, by decide⟩ (![t, u] : Fin 2 → Tm ringSig Γ Elem)

/-- `assoc` of `__*__` in `Monoid`: `∀ x, y, z • (x * y) * z = x * (y * z)`. -/
def assocAx : FOL.Sentence monSig.toSignature :=
  closed (ctx 3)
    (.eq (mul (mul (.var 2) (.var 1)) (.var 0)) (mul (.var 2) (mul (.var 1) (.var 0))))

/-- `unit e` of `__*__` in `Monoid`, left: `∀ x • e * x = x`. -/
def unitLAx : FOL.Sentence monSig.toSignature :=
  closed (ctx 1) (.eq (mul one (.var 0)) (.var 0))

/-- `unit e` of `__*__` in `Monoid`, right: `∀ x • x * e = x`. -/
def unitRAx : FOL.Sentence monSig.toSignature :=
  closed (ctx 1) (.eq (mul (.var 0) one) (.var 0))

/-- `comm` of `__*__` in `CommutativeMonoid`: `∀ x, y • x * y = y * x`. -/
def commAx : FOL.Sentence monSig.toSignature :=
  closed (ctx 2) (.eq (mul (.var 1) (.var 0)) (mul (.var 0) (.var 1)))

/-- `%(inv_Group)%`: `∀ x : Elem • ∃ x' : Elem • x' * x = e` (`x'` is variable `0`). -/
def invGroupAx : FOL.Sentence monSig.toSignature :=
  closed (ctx 1) (ex (Δ := ctx 2) rfl (.eq (mul (.var 0) (.var 1)) one))

/-- Right inverses, `∀ x : Elem • ∃ x' : Elem • x * x' = e`: not an axiom of the library, a
consequence of `Group` used as an additional proof goal. -/
def rightInvAx : FOL.Sentence monSig.toSignature :=
  closed (ctx 1) (ex (Δ := ctx 2) rfl (.eq (mul (.var 1) (.var 0)) one))

/-- `%(distr1_Ring)%`: `∀ x, y, z • (x + y) * z = (x * z) + (y * z)`. -/
def distr1Ax : FOL.Sentence ringSig.toSignature :=
  closed (ctx 3)
    (.eq (rmul (radd (.var 2) (.var 1)) (.var 0))
      (radd (rmul (.var 2) (.var 0)) (rmul (.var 1) (.var 0))))

/-- `%(distr2_Ring)%`: `∀ x, y, z • z * (x + y) = (z * x) + (z * y)`. -/
def distr2Ax : FOL.Sentence ringSig.toSignature :=
  closed (ctx 3)
    (.eq (rmul (.var 0) (radd (.var 2) (.var 1)))
      (radd (rmul (.var 0) (.var 2)) (rmul (.var 0) (.var 1))))

/-! ### The development graph -/

/-- The nodes of the development graph. -/
inductive Node : Type
  | monoid
  | commMonoid
  | group
  | abelianGroup
  /-- `AbelianGroup with sort Elem, ops __*__ ↦ __+__, e ↦ 0` in `Ring`. -/
  | abGroupAdd
  /-- `… and Monoid with ops e, __*__` in `Ring`. -/
  | ringUnion
  | ring
  deriving DecidableEq

/-- The finite signature of a node. -/
def finSig : Node → FinSig
  | .abGroupAdd => addSig
  | .ringUnion => ringSig
  | .ring => ringSig
  | _ => monSig

/-- The first-order signature of a node. -/
abbrev sig (N : Node) : FOL.Signature := (finSig N).toSignature

/-- The identity of the signature of `Monoid`. -/
abbrev idM : monSig.toSignature ⟶ monSig.toSignature := (Mor.id monSig).toHom

/-- The identity of the signature of `Ring`. -/
abbrev idRg : ringSig.toSignature ⟶ ringSig.toSignature := (Mor.id ringSig).toHom

/-- The local axioms of the nodes. -/
def axioms : (N : Node) → Set (FOL.institution.obj (sig N)).Sen
  | .monoid => {assocAx, unitLAx, unitRAx}
  | .commMonoid => {commAx}
  | .group => {invGroupAx}
  | .ring => {distr1Ax, distr2Ax}
  | _ => ∅

/-- The global definition links. -/
def globalDef : (M N : Node) → Set (sig M ⟶ sig N)
  | .monoid, .commMonoid => {idM}
  | .monoid, .group => {idM}
  | .group, .abelianGroup => {idM}
  | .commMonoid, .abelianGroup => {idM}
  | .abelianGroup, .abGroupAdd => {renAdd.toHom}
  | .abGroupAdd, .ringUnion => {inclAdd.toHom}
  | .monoid, .ringUnion => {inclMon.toHom}
  | .ringUnion, .ring => {idRg}
  | _, _ => ∅

/-- The rank of a node: definition links go from lower to higher rank. -/
def rank : Node → ℕ
  | .monoid => 0
  | .commMonoid => 1
  | .group => 1
  | .abelianGroup => 2
  | .abGroupAdd => 3
  | .ringUnion => 4
  | .ring => 5

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

/-- The proof obligation of the view `AbelianGroup_in_Ring_add`: the global theorem link
`abelianGroup ⇢viewMor ring`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5 (printed page 137,
PDF page 139: "`view SP₁ to SP₂ = σ` ⊳ `DG₁ ⊎ DG₂ ⊎ {N₁ ⇢σ N₂}`"). -/
def viewGoal : graph.ThmLink := .glob .abelianGroup .ring viewMor.toHom

/-! ### Structured specifications -/

noncomputable section

/-- Structured specifications over the signature `D`. -/
abbrev Spec (D : FinSig) : Type 1 := StrSpec FOL.institution D.toSignature

/-- `Monoid`. -/
def monoidSpec : Spec monSig := .basic _ {assocAx, unitLAx, unitRAx}

/-- `CommutativeMonoid = Monoid then op __*__ : Elem × Elem → Elem, comm`. -/
def commMonoidSpec : Spec monSig := .union (.translate idM monoidSpec) (.basic _ {commAx})

/-- `Group = Monoid then ∀ x • ∃ x' • x' * x = e`. -/
def groupSpec : Spec monSig := .union (.translate idM monoidSpec) (.basic _ {invGroupAx})

/-- `AbelianGroup = Group and CommutativeMonoid`. -/
def abelianGroupSpec : Spec monSig :=
  .union (.translate idM groupSpec) (.translate idM commMonoidSpec)

/-- `AbelianGroup with sort Elem, ops __*__ ↦ __+__, e ↦ 0`. -/
def abGroupAddSpec : Spec addSig := .translate renAdd.toHom abelianGroupSpec

/-- `AbelianGroup with … and Monoid with ops e, __*__`. -/
def ringUnionSpec : Spec ringSig :=
  .union (.translate inclAdd.toHom abGroupAddSpec) (.translate inclMon.toHom monoidSpec)

/-- `Ring = … then ∀ x, y, z • (x + y) * z = … • z * (x + y) = …`. -/
def ringSpec : Spec ringSig :=
  .union (.translate idRg ringUnionSpec) (.basic _ {distr1Ax, distr2Ax})

/-- The structured specification of each node. -/
def spec : (N : Node) → Spec (finSig N)
  | .monoid => monoidSpec
  | .commMonoid => commMonoidSpec
  | .group => groupSpec
  | .abelianGroup => abelianGroupSpec
  | .abGroupAdd => abGroupAddSpec
  | .ringUnion => ringUnionSpec
  | .ring => ringSpec

end

end Silmaril.Logic.Institution.Hets.Lib.AlgebraI

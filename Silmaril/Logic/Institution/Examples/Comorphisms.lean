module

public import Silmaril.Logic.Institution.Borrowing
public import Silmaril.Logic.Institution.Examples.Propositional
public import Silmaril.Logic.Institution.Examples.FirstOrder

@[expose] public section

/-!
# Comorphisms into first-order logic, and borrowing

* `plToFol : PL → FOL`. A set `P` of propositional variables becomes the first-order signature
  with no sorts, no operation symbols and one nullary relation symbol per variable. Formulas are
  translated homomorphically (`⊥ ↦ ¬true`, `φ → ψ ↦ ¬(φ ∧ ¬ψ)`, `φ ∨ ψ ↦ ¬(¬φ ∧ ¬ψ)`), and a
  first-order structure is reduced to the valuation reading off its nullary relations.
* `eqToFol : EQ → FOL`. An equational signature becomes the first-order signature with the same
  sorts and operations and no relation symbols; an equation `(∀ X) t₁ = t₂` becomes the universal
  closure of the equality atom `t₁ = t₂`; a structure is reduced to its underlying algebra.
  This is Goguen–Roşu's comorphism of Example 4.3(5).

Both comorphisms are model-expansive, so propositional and equational consequence can be decided
by first-order means (`PL.entails_iff_fol`, `EQ.entails_iff_fol`).
-/

namespace Silmaril.Logic.Institution.Examples

open CategoryTheory

universe u

/-- Any two functions out of `Fin 0` are equal. -/
theorem fin0_funext {α : Fin 0 → Sort u} (a b : ∀ j, α j) : a = b :=
  funext fun j => j.elim0

/-! ### Propositional logic into first-order logic -/

namespace PLtoFOL

/-- The first-order signature of a set of propositional variables: no sorts, no operations, and
the variables as nullary relation symbols.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
cf. Example 4.4 (there, for modal logic, propositional symbols become unary predicates; without
worlds they become nullary ones). -/
def sig (P : Type) : FOL.Signature where
  S := PEmpty
  Op := fun _ _ _ => PEmpty
  Rel := fun n _ => PLift (n = 0) × P

/-- The signature functor `Set ⥤ FoSig`. -/
def sigFunctor : Type ⥤ FOL.Signature where
  obj := sig
  map σ := FOL.Signature.Hom.mk ⟨id, fun o => o⟩ (fun r => (r.1, σ r.2))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The empty context of `sig P`. -/
def ctx0 (P : Type) : Fin 0 → (sig P).S := Fin.elim0

/-- The atomic formula of a propositional variable. -/
def atom {P : Type} (p : P) : FOL.Formula (sig P) (ctx0 P) :=
  FOL.Formula.rel (w := Fin.elim0) (⟨rfl⟩, p) (fun j => j.elim0)

/-- Sentence translation of formulas (classical encodings of `⊥`, `→`, `∨`).

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
Definition 4.3 (sentence translation of a comorphism). -/
def formula {P : Type} : PL.Formula P → FOL.Formula (sig P) (ctx0 P)
  | .var p => atom p
  | .bot => .not .tt
  | .imp φ ψ => .not (.and (formula φ) (.not (formula ψ)))
  | .and φ ψ => .and (formula φ) (formula ψ)
  | .or φ ψ => .not (.and (.not (formula φ)) (.not (formula ψ)))

/-- Sentence translation `PL(P) → FOL(sig P)`. -/
def sen {P : Type} (φ : PL.Formula P) : FOL.Sentence (sig P) := ⟨ctx0 P, formula φ⟩

/-- The valuation read off a first-order structure over `sig P`. -/
def valuation {P : Type} (M : FOL.Structure (sig P)) : P → Prop :=
  fun p => M.rel (n := 0) (w := Fin.elim0) (⟨rfl⟩, p) (fun j => j.elim0)

/-- Model translation `FOL(sig P) ⥤ PL(P)`. -/
def mod (P : Type) : FOL.Structure (sig P) ⥤ PL.Model P where
  obj M := ULift.up (valuation M)
  map {M N} h := ⟨fun p hp => by
    exact (congrArg (N.rel (n := 0) (w := Fin.elim0) (⟨rfl⟩, p)) (funext fun j => j.elim0)).mp
        (h.map_rel _ _ hp)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The translated formula holds in a first-order structure (under the unique assignment of the
empty context) iff the propositional formula holds under the valuation read off the structure.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
Definition 4.3 (satisfaction condition of a comorphism), by induction on formulas. -/
theorem holds_formula {P : Type} (M : FOL.Structure (sig P)) (ρ : ∀ i, M.carrier (ctx0 P i))
    (φ : PL.Formula P) : (formula φ).Holds M ρ ↔ φ.eval (valuation M) := by
  induction φ with
  | var p =>
    change M.rel _ _ ↔ M.rel _ _
    exact Iff.of_eq (congrArg (M.rel _) (fin0_funext _ _))
  | bot =>
    show ¬True ↔ False
    exact ⟨fun h => h trivial, False.elim⟩
  | imp φ ψ ihφ ihψ =>
    show ¬((formula φ).Holds M ρ ∧ ¬(formula ψ).Holds M ρ) ↔
      (φ.eval (valuation M) → ψ.eval (valuation M))
    rw [ihφ, ihψ]
    exact ⟨fun h ha => Classical.byContradiction fun hb => h ⟨ha, hb⟩,
      fun h hab => hab.2 (h hab.1)⟩
  | and φ ψ ihφ ihψ =>
    exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ =>
    show ¬(¬(formula φ).Holds M ρ ∧ ¬(formula ψ).Holds M ρ) ↔
      (φ.eval (valuation M) ∨ ψ.eval (valuation M))
    rw [ihφ, ihψ]
    exact ⟨fun h => Classical.byContradiction fun hn =>
        h ⟨fun ha => hn (Or.inl ha), fun hb => hn (Or.inr hb)⟩,
      fun h hn => h.elim hn.1 hn.2⟩

/-- The comorphism satisfaction condition for `PL → FOL`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Definition 4.2;
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
Definition 4.3. -/
theorem sat {P : Type} (M : FOL.Structure (sig P)) (φ : PL.Formula P) :
    (sen φ).Holds M ↔ φ.eval (valuation M) :=
  holds_formula M (fun i => i.elim0) φ

/-- The corridor `PL(P) → FOL(sig P)`. -/
def corridor (P : Type) : PL.institution.obj P ⟶ (sigFunctor ⋙ FOL.institution).obj P :=
  ⟨sen, mod P, fun (M : FOL.Structure (sig P)) φ => sat M φ⟩

/-- Translating formulas commutes with renaming propositional variables.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Definition 4.2
(naturality of `ρ`). -/
theorem formula_map {P Q : Type} (σ : P ⟶ Q) (φ : PL.Formula P) :
    (formula φ).map (sigFunctor.map σ) = formula (φ.rename σ) := by
  induction φ with
  | var p =>
    exact congrArg (FOL.Formula.rel (Γ := ctx0 Q) (w := Fin.elim0) (⟨rfl⟩, σ p))
      (fin0_funext _ _)
  | bot => rfl
  | imp φ ψ ihφ ihψ =>
    exact congrArg FOL.Formula.not (congr (congrArg FOL.Formula.and ihφ)
      (congrArg FOL.Formula.not ihψ))
  | and φ ψ ihφ ihψ =>
    exact congr (congrArg FOL.Formula.and ihφ) ihψ
  | or φ ψ ihφ ihψ =>
    exact congrArg FOL.Formula.not (congr (congrArg FOL.Formula.and
      (congrArg FOL.Formula.not ihφ)) (congrArg FOL.Formula.not ihψ))

/-- Translating sentences commutes with renaming propositional variables.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Definition 4.2
(naturality of `ρ`). -/
theorem sen_map {P Q : Type} (σ : P ⟶ Q) (φ : PL.Formula P) :
    (sen φ).map (sigFunctor.map σ) = sen (φ.rename σ) :=
  congrArg (FOL.Sentence.mk (ctx0 Q)) (formula_map σ φ)

/-- Naturality of the corridors in the signature. -/
theorem naturality {P Q : Type} (σ : P ⟶ Q) :
    PL.institution.map σ ≫ corridor Q =
      corridor P ≫ (sigFunctor ⋙ FOL.institution).map σ :=
  Room.hom_ext (funext fun φ => (sen_map σ φ).symm) rfl

/-- A first-order structure over `sig P` interpreting each nullary relation symbol by a given
valuation (there are no sorts, so no carriers or operations).

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6 (the expansion witnessing model expansiveness), §4.1. -/
def expansion (P : Type) (v : P → Prop) : FOL.Structure (sig P) where
  carrier := fun s => PEmpty.elim s
  op := fun o _ => PEmpty.elim o
  rel := fun r _ => v r.2

end PLtoFOL

/-- The comorphism `PL → FOL`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Definition 4.2;
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
Definition 4.3. -/
def plToFol : Inst.CoHom PL.inst FOL.inst where
  Φ := PLtoFOL.sigFunctor
  ρ :=
    { app := PLtoFOL.corridor
      naturality := fun _ _ σ => PLtoFOL.naturality σ }

/-- Every valuation is the reduct of a first-order structure: `PL → FOL` is model-expansive.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6 (model expansion), §4.1. -/
theorem plToFol_modelExpansive : plToFol.ModelExpansive :=
  fun P v => ⟨PLtoFOL.expansion P (ULift.down v), rfl⟩

/-- Borrowing instantiated: propositional consequence is first-order consequence of the
translations.

Source: Cerioli and Meseguer 1997 (citation only);
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7, lifted in §4.1. -/
theorem PL.entails_iff_fol (P : Type) (Γ : Set (PL.Formula P)) (φ : PL.Formula P) :
    (PL.institution.obj P).Entails Γ φ ↔
      (FOL.institution.obj (PLtoFOL.sig P)).Entails (PLtoFOL.sen '' Γ) (PLtoFOL.sen φ) :=
  plToFol.entails_iff plToFol_modelExpansive P Γ φ

/-! ### Equational logic into first-order logic -/

namespace EQtoFOL

/-- The first-order signature of an equational signature: no relation symbols.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3(5)
("Let Φ' send an equational signature Σ to the first order signature (∅, Σ)"). -/
def sig (Sg : EQ.Signature) : FOL.Signature := { Sg with Rel := fun _ _ => PEmpty }

/-- The signature functor `Sig ⥤ FoSig`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3(5). -/
def sigFunctor : EQ.Signature ⥤ FOL.Signature where
  obj := sig
  map σ := FOL.Signature.Hom.mk σ (fun r => r)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The universal closure of a formula, quantifying away its context one variable at a time.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3(5)
("send a Σ-equation to the corresponding (∅, Σ)-sentence"). -/
def closeAll {Sg : FOL.Signature} : {k : ℕ} → (Γ : Fin k → Sg.S) → FOL.Formula Sg Γ →
    FOL.Sentence Sg
  | 0, Γ, φ => ⟨Γ, φ⟩
  | _ + 1, Γ, φ => closeAll (Γ ∘ Fin.succ) (.all rfl φ)

/-- A closed formula holds iff the formula holds under every assignment of its context.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2,
Definition 65(5) (iterated). -/
theorem holds_closeAll {Sg : FOL.Signature} (M : FOL.Structure Sg) {k : ℕ} (Γ : Fin k → Sg.S)
    (φ : FOL.Formula Sg Γ) : (closeAll Γ φ).Holds M ↔ ∀ ρ, φ.Holds M ρ := by
  induction k with
  | zero =>
    constructor
    · intro h ρ
      obtain rfl : ρ = fun i => i.elim0 := fin0_funext _ _
      exact h
    · intro h
      exact h _
  | succ k ih =>
    refine (ih (Γ ∘ Fin.succ) (.all rfl φ)).trans ?_
    constructor
    · intro h ρ
      exact h (fun i => ρ i.succ) ρ (fun _ => HEq.rfl)
    · intro h _ ρ' _
      exact h ρ'

/-- Translating a universal closure along a signature morphism is the universal closure of the
translation.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 64 (`WFF_X(Φ)`, defined on generators). -/
theorem map_closeAll {Sg Sg' : FOL.Signature} (τ : Sg ⟶ Sg') {k : ℕ} (Γ : Fin k → Sg.S)
    (φ : FOL.Formula Sg Γ) : (closeAll Γ φ).map τ = closeAll (τ.sorts ∘ Γ) (φ.map τ) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (Γ ∘ Fin.succ) (.all rfl φ)

/-- Sentence translation: an equation becomes the universal closure of an equality atom. -/
def sen {Sg : EQ.Signature} (e : EQ.Equation Sg) : FOL.Sentence (sig Sg) :=
  closeAll (Sg := sig Sg) e.ctx (.eq e.lhs e.rhs)

/-- Model translation: a structure without relations is reduced to its algebra.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3(5)
("let β' send a (∅, Σ)-model to the corresponding Σ-algebra"). -/
def mod (Sg : EQ.Signature) : FOL.Structure (sig Sg) ⥤ EQ.Algebra Sg where
  obj M := M.toAlgebra
  map h := h.toAlgebraHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comorphism satisfaction condition for `EQ → FOL`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Definition 4.2 and
Example 4.3(5) ("It is now easy to check the naturality and satisfaction conditions"). -/
theorem sat {Sg : EQ.Signature} (M : FOL.Structure (sig Sg)) (e : EQ.Equation Sg) :
    (sen e).Holds M ↔ e.Holds M.toAlgebra :=
  holds_closeAll M e.ctx (.eq e.lhs e.rhs)

/-- The corridor `EQ(Σ) → FOL(Σ)`. -/
def corridor (Sg : EQ.Signature) :
    EQ.institution.obj Sg ⟶ (sigFunctor ⋙ FOL.institution).obj Sg :=
  ⟨sen, mod Sg, fun (M : FOL.Structure (sig Sg)) e => sat M e⟩

/-- Translating equations commutes with signature morphisms.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3(5)
("It is now easy to check the naturality and satisfaction conditions"). -/
theorem sen_map {Sg Sg' : EQ.Signature} (σ : Sg ⟶ Sg') (e : EQ.Equation Sg) :
    (sen e).map (sigFunctor.map σ) = sen (e.map σ) :=
  map_closeAll (sigFunctor.map σ) e.ctx (.eq e.lhs e.rhs)

/-- Naturality of the corridors in the signature. -/
theorem naturality {Sg Sg' : EQ.Signature} (σ : Sg ⟶ Sg') :
    EQ.institution.map σ ≫ corridor Sg' =
      corridor Sg ≫ (sigFunctor ⋙ FOL.institution).map σ :=
  Room.hom_ext (funext fun e => (sen_map σ e).symm) rfl

/-- The first-order structure over `sig Sg` with a given underlying algebra (there are no
relation symbols to interpret).

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3(5)
(`β'` sends a `(∅, Σ)`-model to the corresponding `Σ`-algebra). -/
def expansion {Sg : EQ.Signature} (A : EQ.Algebra Sg) : FOL.Structure (sig Sg) where
  carrier := A.carrier
  op := A.op
  rel := fun r _ => PEmpty.elim r

/-- First-order signature morphisms out of `sig Sg` are determined by their equational part,
since `sig Sg` has no relation symbols.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4.2, Example 4.12,
item 1. -/
theorem sigHom_ext {Sg : EQ.Signature} {F : FOL.Signature} (f g : sigFunctor.obj Sg ⟶ F)
    (h : f.toHom = g.toHom) : f = g := by
  obtain ⟨f₀, rf⟩ := f
  obtain ⟨g₀, rg⟩ := g
  obtain rfl : f₀ = g₀ := h
  obtain rfl : @rf = @rg := by
    funext n w x
    exact PEmpty.elim x
  rfl

end EQtoFOL

/-- The comorphism `EQ → FOL`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3(5). -/
def eqToFol : Inst.CoHom EQ.inst FOL.inst where
  Φ := EQtoFOL.sigFunctor
  ρ :=
    { app := EQtoFOL.corridor
      naturality := fun _ _ σ => EQtoFOL.naturality σ }

/-- Every algebra is the reduct of a structure (interpret no relations): `EQ → FOL` is
model-expansive.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6, §4.1. -/
theorem eqToFol_modelExpansive : eqToFol.ModelExpansive :=
  fun _ A => ⟨EQtoFOL.expansion A, rfl⟩

/-- Borrowing instantiated: equational consequence is first-order consequence of the universal
closures.

Source: Cerioli and Meseguer 1997 (citation only);
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, after Theorem 4.4;
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7, lifted in §4.1. -/
theorem EQ.entails_iff_fol (Sg : EQ.Signature) (Γ : Set (EQ.Equation Sg)) (e : EQ.Equation Sg) :
    (EQ.institution.obj Sg).Entails Γ e ↔
      (FOL.institution.obj (EQtoFOL.sig Sg)).Entails (EQtoFOL.sen '' Γ) (EQtoFOL.sen e) :=
  eqToFol.entails_iff eqToFol_modelExpansive Sg Γ e

/-! ### The forgetful morphism `FOL → EQ`, by duality -/

/-- The signature functor of `EQ → FOL` is left adjoint to the forgetful functor `FoSig ⥤ Sig`:
a first-order signature morphism out of a signature with no relation symbols is the same as an
equational signature morphism into the underlying equational signature.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4.2, Example 4.12,
item 1 ("The functor Φ' in item 5 of Example 4.3, from equational to first order signatures, is
left adjoint to the functor Φ in item 1 of Example 4.3"). -/
def EQtoFOL.adjunction : EQtoFOL.sigFunctor ⊣ FOL.Signature.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv Sg F :=
        { toFun f := f.toHom
          invFun g := FOL.Signature.Hom.mk g (fun r => PEmpty.elim r)
          left_inv := by
            intro f
            exact EQtoFOL.sigHom_ext _ _ (by rfl)
          right_inv := by
            intro g
            rfl }
      homEquiv_naturality_left_symm := by
        intros
        exact EQtoFOL.sigHom_ext _ _ (by rfl)
      homEquiv_naturality_right := by
        intros
        rfl }

/-- The forgetful institution morphism `FOL → EQ`, obtained from the comorphism `EQ → FOL`
by the morphism–comorphism duality.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3,
item 1 (the morphism), and §4.2, Theorem 4.11 and Example 4.12, item 1 ("the morphism (item 1)
and comorphism (item 5) between these institutions correspond under the bijection of
Theorem 4.11"). -/
def folToEq : Inst.Hom FOL.inst EQ.inst :=
  eqToFol.toHom (A := FOL.inst) (B := EQ.inst) EQtoFOL.adjunction

/-- The signature functor of `FOL → EQ` forgets relation symbols.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3,
item 1. -/
theorem folToEq_Φ : folToEq.Φ = FOL.Signature.forget :=
  rfl

/-- The first-order structure with a given underlying algebra and every relation empty.

Source: `goguen-burstall-1992` in `references.bib`, §4.1, Definition 34 (the
model witnessing soundness). -/
def folToEqExpansion {Sg : FOL.Signature} (A : EQ.Algebra Sg.toSignature) : FOL.Structure Sg where
  carrier := A.carrier
  op := A.op
  rel := fun _ _ => False

/-- `FOL → EQ` is sound: every algebra over the equational part of a first-order signature is
the image of a first-order structure (interpret every relation as empty), so equational
consequence can be borrowed from first-order consequence along it as well.

Source: `goguen-burstall-1992` in `references.bib`, §4.1, Definition 34;
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3, item 1, and
Theorem 4.4. -/
theorem folToEq_sound : folToEq.Sound := by
  intro S
  rw [show folToEq.η.app S = _ from morphismEquivComorphism_symm_apply_app EQtoFOL.adjunction
    FOL.institution EQ.institution eqToFol.ρ S]
  intro A
  exact ⟨folToEqExpansion A, rfl⟩

end Silmaril.Logic.Institution.Examples

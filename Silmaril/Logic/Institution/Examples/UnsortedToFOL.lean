module

public import Silmaril.Logic.Institution.Examples.Unsorted
public import Silmaril.Logic.Institution.Examples.Comorphisms

@[expose] public section

/-!
# Unsorted into many-sorted first-order logic

An unsorted signature becomes the one-sorted first-order signature (sort `()`, every symbol typed
by a list of `()`s of its arity), terms and formulas are translated homomorphically, and the
quantifier `∀` becomes the many-sorted `∀` over the one sort.

Many-sorted first-order logic (`FOL.inst`) allows empty carriers while unsorted structures are
nonempty, so the comorphism is *simple theoroidal*: an unsorted signature goes to the one-sorted
theory with the single axiom `∃x. x = x` (`nonemptyAx`). Every unsorted structure is (literally)
the reduct of a model of that theory, so the comorphism is model-expansive and unsorted
consequence is many-sorted consequence of the translations plus `∃x. x = x`
(`UFOL.entails_iff_fol`).

Source: `mossakowski-et-al-2014-proof-support-common-logic` in `references.bib`, §4.8
("FOL to CFOL"), p. 11; `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4,
Example 4.3(2) (unsorted into many-sorted algebra, "better seen as a comorphism"), p. 12, and
§5.1, Definition 5.7 (theoroidal comorphisms).
-/

namespace Silmaril.Logic.Institution.Examples

open CategoryTheory

namespace UFOLtoFOL

/-- The one-sorted first-order signature of an unsorted signature. -/
def sig (Sg : UFOL.Signature) : FOL.Signature where
  S := Unit
  Op n _ _ := Sg.Op n
  Rel n _ := Sg.Rel n

/-- The signature functor. -/
def sigFunctor : UFOL.Signature ⥤ FOL.Signature where
  obj := sig
  map {Sg Sg'} σ := ({ sorts := id, ops := fun o => σ.ops o, rels := fun r => σ.rels r } :
    FOL.Signature.Hom (sig Sg) (sig Sg'))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The one-sorted context of length `k`. -/
def ctx (Sg : UFOL.Signature) (k : ℕ) : Fin k → (sig Sg).S := fun _ => ()

variable {Sg : UFOL.Signature} {k : ℕ}

/-- First-order terms of the translation. -/
abbrev FTerm (Sg : UFOL.Signature) (k : ℕ) : Type := EQ.Term (sig Sg).toSignature (ctx Sg k) ()

/-- Translate a term. -/
def term : UFOL.Term Sg k → FTerm Sg k
  | .var i => EQ.Term.var i
  | .app o args =>
      EQ.Term.app (Sg := (sig Sg).toSignature) (Γ := ctx Sg k) (w := fun _ => ()) (s := ()) o
        (fun j => term (args j))

/-- Translate a formula. -/
def formula : {k : ℕ} → UFOL.Formula Sg k → FOL.Formula (sig Sg) (ctx Sg k)
  | _, .eq t u => FOL.Formula.eq (s := ()) (term t) (term u)
  | k, .rel r args =>
      FOL.Formula.rel (Sg := sig Sg) (Γ := ctx Sg k) (w := fun _ => ()) r (fun j => term (args j))
  | _, .tt => .tt
  | _, .not φ => .not (formula φ)
  | _, .and φ ψ => .and (formula φ) (formula ψ)
  | k, .all φ => .all (Δ := ctx Sg (k + 1)) rfl (formula φ)

/-- Translate a sentence. -/
def sen (φ : UFOL.Sentence Sg) : FOL.Sentence (sig Sg) := ⟨ctx Sg 0, formula φ⟩

/-- `∃x. x = x`: the carrier is nonempty. -/
def nonemptyAx (Sg : UFOL.Signature) : FOL.Sentence (sig Sg) :=
  ⟨ctx Sg 0, .not (.all (Δ := ctx Sg 1) rfl
    (.not (.eq (s := ()) (EQ.Term.var 0) (EQ.Term.var 0))))⟩

/-- The axioms of the theory of a signature. -/
def axioms (Sg : UFOL.Signature) : Set (FOL.Sentence (sig Sg)) := {nonemptyAx Sg}

/-- The one-sorted theory with nonempty carrier. -/
def theory (Sg : UFOL.Signature) : Theory FOL.institution :=
  (Theory.ofPresentation FOL.institution).obj ⟨sig Sg, axioms Sg⟩

theorem nonemptyAx_map {Sg Sg' : UFOL.Signature} (σ : Sg ⟶ Sg') :
    (nonemptyAx Sg).map (sigFunctor.map σ) = nonemptyAx Sg' :=
  rfl

theorem axioms_mapsTo {Sg Sg' : UFOL.Signature} (σ : Sg ⟶ Sg') :
    Set.MapsTo (FOL.Sentence.map (sigFunctor.map σ)) (axioms Sg) (axioms Sg') := by
  rintro φ rfl
  exact nonemptyAx_map σ

/-- The signature functor of the comorphism, into first-order theories. -/
def thFunctor : UFOL.Signature ⥤ Theory FOL.institution where
  obj := theory
  map {Sg Sg'} σ := Theory.homMk (sigFunctor.map σ)
    ((Theory.presentation_lemma (I := FOL.institution) (sigFunctor.map σ) (axioms Sg)
      (axioms Sg')).2 fun _ hφ =>
        (FOL.institution.obj (sig Sg')).subset_closure _ (axioms_mapsTo σ hφ))
  map_id Sg := Theory.hom_ext (sigFunctor.map_id Sg)
  map_comp σ τ := Theory.hom_ext (sigFunctor.map_comp σ τ)

/-- Models of `theory Sg` satisfy `axioms Sg`. -/
theorem models_axioms (M : (theory Sg).Models) : ∀ φ ∈ axioms Sg, φ.Holds M.obj :=
  fun φ hφ => M.property φ ((FOL.institution.obj (sig Sg)).subset_closure _ hφ)

/-- The unsorted structure of a one-sorted structure with nonempty carrier. -/
def toStructure (M : FOL.Structure (sig Sg)) (hM : ∀ φ ∈ axioms Sg, φ.Holds M) :
    UFOL.Structure Sg where
  carrier := M.carrier ()
  nonempty := by
    by_contra hne
    exact hM (nonemptyAx Sg) rfl (fun ρ' _ _ => hne ⟨ρ' 0⟩)
  op o args := M.op (w := fun _ => ()) (s := ()) o args
  rel r args := M.rel (w := fun _ => ()) r args

/-- The model translation. -/
def modFunctor (Sg : UFOL.Signature) : (theory Sg).Models ⥤ UFOL.Structure Sg where
  obj M := toStructure M.obj (models_axioms M)
  map f := ⟨f.hom.map (), fun o args => f.hom.map_op (w := fun _ => ()) (s := ()) o args,
    fun r args h => f.hom.map_rel (w := fun _ => ()) r args h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Translated terms denote what the unsorted terms denote. -/
theorem eval_term (M : FOL.Structure (sig Sg)) (hM : ∀ φ ∈ axioms Sg, φ.Holds M)
    (ρ : Fin k → M.carrier ()) (t : UFOL.Term Sg k) :
    (term t).eval M.toAlgebra ρ = t.eval (toStructure M hM) ρ := by
  induction t with
  | var i => rfl
  | app o args ih =>
    show M.op (w := fun _ => ()) (s := ()) o (fun j => (term (args j)).eval M.toAlgebra ρ) =
      M.op (w := fun _ => ()) (s := ()) o (fun j => (args j).eval (toStructure M hM) ρ)
    exact congrArg _ (funext ih)

/-- Translated formulas hold iff the unsorted formulas hold. -/
theorem holds_formula (M : FOL.Structure (sig Sg)) (hM : ∀ φ ∈ axioms Sg, φ.Holds M)
    (φ : UFOL.Formula Sg k) (ρ : Fin k → M.carrier ()) :
    (formula φ).Holds M ρ ↔ φ.Holds (toStructure M hM) ρ := by
  induction φ with
  | eq t u => exact Iff.of_eq (congrArg₂ Eq (eval_term M hM ρ t) (eval_term M hM ρ u))
  | rel r args =>
    exact Iff.of_eq (congrArg (M.rel (w := fun _ => ()) r)
      (funext fun j => eval_term M hM ρ (args j)))
  | tt => exact Iff.rfl
  | not φ ih => exact not_congr (ih ρ)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ ρ) (ihψ ρ)
  | all φ ih =>
    show (∀ ρ' : Fin _ → M.carrier (), (∀ i, HEq (ρ' i.succ) (ρ i)) → (formula φ).Holds M ρ') ↔
      ∀ x : M.carrier (), φ.Holds (toStructure M hM) (Fin.cons x ρ)
    constructor
    · intro h x
      exact (ih _).1 (h (Fin.cons x ρ) fun i => heq_of_eq (Fin.cons_succ (α := fun _ => M.carrier ()) x ρ i))
    · intro h ρ' hρ'
      have htail : Fin.tail ρ' = ρ := funext fun i => eq_of_heq (hρ' i)
      have hρ : ρ' = Fin.cons (ρ' 0) ρ := by rw [← htail, Fin.cons_self_tail]
      rw [hρ]
      exact (ih _).2 (h (ρ' 0))

/-- The satisfaction condition of the translation. -/
theorem sat (M : (theory Sg).Models) (φ : UFOL.Sentence Sg) :
    (sen φ).Holds M.obj ↔ UFOL.Sentence.Holds ((modFunctor Sg).obj M) φ :=
  holds_formula M.obj (models_axioms M) φ Fin.elim0

/-- The corridor at a signature. -/
def corridor (Sg : UFOL.Signature) : UFOL.inst.I.obj Sg ⟶ (thFunctor ⋙ FOL.inst.th.I).obj Sg :=
  ⟨sen, modFunctor Sg, fun M φ => sat M φ⟩

/-- Translating terms commutes with signature morphisms. -/
theorem term_map {Sg' : UFOL.Signature} (σ : Sg ⟶ Sg') (t : UFOL.Term Sg k) :
    term (t.map σ) = (term t).map (sigFunctor.map σ).toHom := by
  induction t with
  | var i => rfl
  | app o args ih =>
    show EQ.Term.app (Sg := (sig Sg').toSignature) (Γ := ctx Sg' k) (w := fun _ => ()) (s := ())
        (σ.ops o) (fun j => term ((args j).map σ)) =
      EQ.Term.app (Sg := (sig Sg').toSignature) (Γ := ctx Sg' k) (w := fun _ => ()) (s := ())
        (σ.ops o) (fun j => (term (args j)).map (sigFunctor.map σ).toHom)
    exact congrArg _ (funext ih)

/-- Translating formulas commutes with signature morphisms. -/
theorem formula_map {Sg' : UFOL.Signature} (σ : Sg ⟶ Sg') (φ : UFOL.Formula Sg k) :
    formula (φ.map σ) = (formula φ).map (sigFunctor.map σ) := by
  induction φ with
  | eq t u =>
    exact congrArg₂ (fun a b => FOL.Formula.eq (Sg := sig Sg') (Γ := ctx Sg' _) (s := ()) a b)
      (term_map σ t) (term_map σ u)
  | rel r args =>
    show FOL.Formula.rel (Sg := sig Sg') (Γ := ctx Sg' _) (w := fun _ => ()) (σ.rels r)
        (fun j => term ((args j).map σ)) =
      FOL.Formula.rel (Sg := sig Sg') (Γ := ctx Sg' _) (w := fun _ => ()) (σ.rels r)
        (fun j => (term (args j)).map (sigFunctor.map σ).toHom)
    exact congrArg _ (funext fun j => term_map σ (args j))
  | tt => rfl
  | not φ ih => exact congrArg FOL.Formula.not ih
  | and φ ψ ihφ ihψ => exact congrArg₂ FOL.Formula.and ihφ ihψ
  | all φ ih => exact congrArg (FOL.Formula.all (Δ := ctx Sg' (_ + 1)) rfl) ih

theorem naturality {Sg Sg' : UFOL.Signature} (σ : Sg ⟶ Sg') :
    UFOL.inst.I.map σ ≫ corridor Sg' = corridor Sg ≫ (thFunctor ⋙ FOL.inst.th.I).map σ := by
  exact Room.hom_ext (funext fun φ => congrArg (FOL.Sentence.mk (ctx Sg' 0)) (formula_map σ φ))
    rfl

/-- Every unsorted structure as a one-sorted structure. -/
def expansion (A : UFOL.Structure Sg) : FOL.Structure (sig Sg) where
  carrier _ := A.carrier
  op o args := A.op o args
  rel r args := A.rel r args

theorem expansion_mem (A : UFOL.Structure Sg) :
    ∀ φ ∈ (theory Sg).sentences, φ.Holds (expansion A) := by
  intro φ hφ
  refine hφ (expansion A) ?_
  rintro _ rfl
  obtain ⟨x⟩ := A.nonempty
  exact fun H => H (fun _ => x) (fun i => i.elim0) rfl

end UFOLtoFOL

/-- The simple theoroidal comorphism from unsorted into many-sorted first-order logic.

Source: `mossakowski-et-al-2014-proof-support-common-logic` in `references.bib`, §4.8, p. 11;
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §5.1, Definition 5.7. -/
def ufolToFol : Inst.SimpleTheoroidalCoHom UFOL.inst FOL.inst where
  Φ := UFOLtoFOL.thFunctor
  ρ :=
    { app := UFOLtoFOL.corridor
      naturality := fun _ _ σ => UFOLtoFOL.naturality σ }

/-- Every unsorted structure is the reduct of a one-sorted model: `UFOL → FOL` is
model-expansive. -/
theorem ufolToFol_modelExpansive : ufolToFol.ModelExpansive :=
  fun _ A => ⟨⟨UFOLtoFOL.expansion A, UFOLtoFOL.expansion_mem A⟩, rfl⟩

/-- Borrowing: unsorted consequence is many-sorted consequence of the translations together with
`∃x. x = x`. -/
theorem UFOL.entails_iff_fol (Sg : UFOL.Signature) (Γ : Set (UFOL.Sentence Sg))
    (φ : UFOL.Sentence Sg) :
    (UFOL.institution.obj Sg).Entails Γ φ ↔
      (FOL.institution.obj (UFOLtoFOL.sig Sg)).Entails
        (UFOLtoFOL.axioms Sg ∪ UFOLtoFOL.sen '' Γ) (UFOLtoFOL.sen φ) := by
  refine (Inst.CoHom.entails_iff ufolToFol ufolToFol_modelExpansive Sg Γ φ).trans ?_
  constructor
  · intro h M hM
    exact h ⟨M, fun ψ hψ => hψ M (fun χ hχ => hM χ (Or.inl hχ))⟩ (fun ψ hψ => hM ψ (Or.inr hψ))
  · intro h M hM
    refine h M.obj (fun ψ hψ => ?_)
    rcases hψ with hψ | hψ
    · exact UFOLtoFOL.models_axioms M ψ hψ
    · exact hM ψ hψ

end Silmaril.Logic.Institution.Examples

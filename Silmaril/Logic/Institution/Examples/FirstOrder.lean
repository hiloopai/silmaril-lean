module

public import Silmaril.Logic.Institution.Examples.Equational

@[expose] public section

/-!
# The institution of many-sorted first-order logic with equality

A first-order signature `(S, Σ, Π)` extends an equational signature with relation symbols of
each arity. Models are first-order structures (an algebra with a relation for each relation
symbol); morphisms are homomorphisms of the algebra that preserve (not necessarily reflect)
relations. Formulas over a finite sorted context are built from equations and relational atoms
with `true`, `¬`, `∧` and `∀`, as in Goguen–Burstall's Definition 64 with equality atoms
(Example 67). Sentences are closed formulas, i.e. formulas over the empty context.

The quantifier `∀` binds the first variable of an extended context `Δ` with `Δ ∘ Fin.succ = Γ`;
keeping the extension as a hypothesis rather than as the term `Fin.cons s Γ` makes sentence
translation commute with context extension without casts. Carriers may be empty (Goguen–Roşu,
Example 3.2(4); Goguen–Burstall's Definition 63 requires nonempty carriers instead).

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2,
Definitions 62–65, Examples 66 and 67.
-/

namespace Silmaril.Logic.Institution.Examples.FOL

open CategoryTheory

/-- A many-sorted first-order signature: sorts, operation symbols and relation symbols.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, Definition 62. -/
structure Signature extends EQ.Signature where
  /-- The relation symbols of arity `w`. -/
  Rel : (n : ℕ) → (Fin n → S) → Type

/-- A first-order signature morphism.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, Definition 62. -/
structure Signature.Hom (Sg Sg' : Signature) extends
    EQ.Signature.Hom Sg.toSignature Sg'.toSignature where
  /-- The relation-symbol map. -/
  rels : ∀ {n : ℕ} {w : Fin n → Sg.S}, Sg.Rel n w → Sg'.Rel n (sorts ∘ w)

/-- The category `FoSig` of first-order signatures.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 62. -/
instance : Category.{0} Signature where
  Hom := Signature.Hom
  id _ := { sorts := id, ops := fun o => o, rels := fun r => r }
  comp f g :=
    { sorts := g.sorts ∘ f.sorts, ops := fun o => g.ops (f.ops o), rels := fun r => g.rels (f.rels r) }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The forgetful functor `FoSig ⥤ Sig` from first-order to equational signatures, dropping the
relation symbols.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Example 4.3,
item 1 ("the forgetful functor which on objects sends `(Π, Σ)` to `Σ`"). -/
def Signature.forget : Signature ⥤ EQ.Signature where
  obj Sg := Sg.toSignature
  map σ := σ.toHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- First-order structures.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, Definition 63
(with possibly empty carriers). -/
structure Structure (Sg : Signature) extends EQ.Algebra Sg.toSignature where
  /-- The interpretation of each relation symbol. -/
  rel : ∀ {n : ℕ} {w : Fin n → Sg.S}, Sg.Rel n w → (∀ j, carrier (w j)) → Prop

/-- Homomorphisms of first-order structures: sorted maps commuting with the operations
(homomorphisms of the underlying algebras) and preserving relations.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 63. -/
structure Structure.Hom {Sg : Signature} (M N : Structure Sg) : Type where
  /-- The sorted map of carriers. -/
  map : ∀ s, M.carrier s → N.carrier s
  /-- The homomorphism condition. -/
  map_op : ∀ {n : ℕ} {w : Fin n → Sg.S} {s : Sg.S} (o : Sg.Op n w s) (args : ∀ j, M.carrier (w j)),
    map s (M.op o args) = N.op o (fun j => map (w j) (args j))
  /-- Relations are preserved. -/
  map_rel : ∀ {n : ℕ} {w : Fin n → Sg.S} (r : Sg.Rel n w) (args : ∀ j, M.carrier (w j)),
    M.rel r args → N.rel r (fun j => map (w j) (args j))

/-- The algebra homomorphism underlying a homomorphism of structures. -/
def Structure.Hom.toAlgebraHom {Sg : Signature} {M N : Structure Sg} (h : Structure.Hom M N) :
    EQ.Algebra.Hom M.toAlgebra N.toAlgebra :=
  ⟨h.map, h.map_op⟩

/-- The category `FoMod(Ω)` of first-order structures.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 63. -/
instance (Sg : Signature) : Category.{0} (Structure Sg) where
  Hom := Structure.Hom
  id _ := ⟨fun _ x => x, fun _ _ => rfl, fun _ _ h => h⟩
  comp f g := ⟨fun s x => g.map s (f.map s x), fun o args => by rw [f.map_op, g.map_op],
    fun {_ w} r args h => g.map_rel r (fun j => f.map (w j) (args j)) (f.map_rel r args h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The reduct functor `FoMod(σ)`.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 63 (the functor `FoMod(Φ)`). -/
def Structure.reduct {Sg Sg' : Signature} (σ : Sg ⟶ Sg') : Structure Sg' ⥤ Structure Sg where
  obj M := { toAlgebra := (EQ.Algebra.reduct σ.toHom).obj M.toAlgebra,
             rel := fun r args => M.rel (σ.rels r) args }
  map h := ⟨fun s => h.map (σ.sorts s), fun o args => h.map_op (σ.ops o) args,
    fun r args hr => h.map_rel (σ.rels r) args hr⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- First-order formulas over a finite sorted context `Γ`: equations and relational atoms,
`true`, negation, conjunction and universal quantification of the first variable of an extended
context.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, Definition 64
(connectives `true`, `¬`, `&`, `∀x`) and Example 67 (equality atoms). -/
inductive Formula (Sg : Signature) : {k : ℕ} → (Fin k → Sg.S) → Type
  | eq {k : ℕ} {Γ : Fin k → Sg.S} {s : Sg.S} (t u : EQ.Term Sg.toSignature Γ s) : Formula Sg Γ
  | rel {k : ℕ} {Γ : Fin k → Sg.S} {n : ℕ} {w : Fin n → Sg.S} (r : Sg.Rel n w)
      (args : ∀ j, EQ.Term Sg.toSignature Γ (w j)) : Formula Sg Γ
  | tt {k : ℕ} {Γ : Fin k → Sg.S} : Formula Sg Γ
  | not {k : ℕ} {Γ : Fin k → Sg.S} (φ : Formula Sg Γ) : Formula Sg Γ
  | and {k : ℕ} {Γ : Fin k → Sg.S} (φ ψ : Formula Sg Γ) : Formula Sg Γ
  | all {k : ℕ} {Γ : Fin k → Sg.S} {Δ : Fin (k + 1) → Sg.S} (h : Δ ∘ Fin.succ = Γ)
      (φ : Formula Sg Δ) : Formula Sg Γ

namespace Formula

variable {Sg Sg' Sg'' : Signature}

/-- Translation of formulas along a signature morphism.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 64 (`WFF_X(Φ)`, defined on generators). -/
def map (σ : Sg ⟶ Sg') : {k : ℕ} → {Γ : Fin k → Sg.S} → Formula Sg Γ → Formula Sg' (σ.sorts ∘ Γ)
  | _, _, eq t u => eq (t.map σ.toHom) (u.map σ.toHom)
  | _, _, rel r args => rel (σ.rels r) (fun j => (args j).map σ.toHom)
  | _, _, tt => tt
  | _, _, not φ => not (map σ φ)
  | _, _, and φ ψ => and (map σ φ) (map σ ψ)
  | _, _, all h φ => all (congrArg (σ.sorts ∘ ·) h) (map σ φ)

/-- Tarskian satisfaction of a formula under an assignment of the context variables. The
quantifier ranges over the assignments of the extended context that agree with the given one on
the old variables.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2,
Definition 65. -/
def Holds (M : Structure Sg) : {k : ℕ} → {Γ : Fin k → Sg.S} → Formula Sg Γ →
    (∀ i, M.carrier (Γ i)) → Prop
  | _, _, eq t u, ρ => t.eval M.toAlgebra ρ = u.eval M.toAlgebra ρ
  | _, _, rel r args, ρ => M.rel r (fun j => (args j).eval M.toAlgebra ρ)
  | _, _, tt, _ => True
  | _, _, not φ, ρ => ¬ Holds M φ ρ
  | _, _, and φ ψ, ρ => Holds M φ ρ ∧ Holds M ψ ρ
  | _, _, all (Δ := Δ) _ φ, ρ =>
      ∀ ρ' : ∀ i, M.carrier (Δ i), (∀ i, HEq (ρ' i.succ) (ρ i)) → Holds M φ ρ'

theorem map_id {k : ℕ} {Γ : Fin k → Sg.S} (φ : Formula Sg Γ) : φ.map (𝟙 Sg) = φ := by
  (induction φ with
     | eq t u => exact congrArg₂ eq (EQ.Term.map_id t) (EQ.Term.map_id u)
     | rel r args => exact congrArg (rel r) (funext fun j => EQ.Term.map_id (args j))
     | tt => rfl
     | not φ ih => exact congrArg not ih
     | and φ ψ ihφ ihψ => exact congrArg₂ and ihφ ihψ
     | all h φ ih => exact congrArg (all h) ih)

theorem map_comp (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'') {k : ℕ} {Γ : Fin k → Sg.S}
    (φ : Formula Sg Γ) : φ.map (σ ≫ τ) = (φ.map σ).map τ := by
  (induction φ with
     | eq t u =>
       exact congrArg₂ eq (EQ.Term.map_comp σ.toHom τ.toHom t)
         (EQ.Term.map_comp σ.toHom τ.toHom u)
     | rel r args =>
       exact congrArg (rel (τ.rels (σ.rels r)))
         (funext fun j => EQ.Term.map_comp σ.toHom τ.toHom (args j))
     | tt => rfl
     | not φ ih => exact congrArg not ih
     | and φ ψ ihφ ihψ => exact congrArg₂ and ihφ ihψ
     | all h φ ih => exact congrArg (all _) ih)

/-- The satisfaction condition for formulas: a translated formula holds in a `Σ'`-structure
under an assignment iff the formula holds in the reduct under the same assignment.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 65 ("This follows from an argument much like that used for the equational case"). -/
theorem holds_map (σ : Sg ⟶ Sg') (M : Structure Sg') {k : ℕ} {Γ : Fin k → Sg.S}
    (φ : Formula Sg Γ) (ρ : ∀ i, M.carrier (σ.sorts (Γ i))) :
    (φ.map σ).Holds M ρ ↔ φ.Holds ((Structure.reduct σ).obj M) ρ := by
  (induction φ with
     | eq t u =>
       exact Iff.of_eq (congrArg₂ Eq (EQ.Term.eval_map σ.toHom M.toAlgebra ρ t)
         (EQ.Term.eval_map σ.toHom M.toAlgebra ρ u))
     | rel r args =>
       exact Iff.of_eq (congrArg (M.rel (σ.rels r))
         (funext fun j => EQ.Term.eval_map σ.toHom M.toAlgebra ρ (args j)))
     | tt => exact Iff.rfl
     | not φ ih => exact not_congr (ih ρ)
     | and φ ψ ihφ ihψ => exact and_congr (ihφ ρ) (ihψ ρ)
     | all h φ ih => exact forall_congr' fun ρ' => imp_congr_right fun _ => ih ρ')

end Formula

/-- A first-order sentence: a formula over the empty context.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 64 ("an Ω-sentence [is] a closed Ω-formula"). -/
structure Sentence (Sg : Signature) : Type where
  /-- The (empty) context. -/
  ctx : Fin 0 → Sg.S
  /-- The closed formula. -/
  formula : Formula Sg ctx

/-- Translation of sentences (`FoSen(σ)`).

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 64. -/
def Sentence.map {Sg Sg' : Signature} (σ : Sg ⟶ Sg') (φ : Sentence Sg) : Sentence Sg' :=
  ⟨σ.sorts ∘ φ.ctx, φ.formula.map σ⟩

/-- Satisfaction of a sentence: the formula holds under the empty assignment.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2,
Definition 65. -/
def Sentence.Holds {Sg : Signature} (M : Structure Sg) (φ : Sentence Sg) : Prop :=
  φ.formula.Holds M (fun i => i.elim0)

theorem Sentence.map_id {Sg : Signature} (φ : Sentence Sg) : φ.map (𝟙 Sg) = φ := by
  (obtain ⟨ctx, f⟩ := φ; exact congrArg (Sentence.mk ctx) (Formula.map_id f))

theorem Sentence.map_comp {Sg Sg' Sg'' : Signature} (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'')
    (φ : Sentence Sg) : φ.map (σ ≫ τ) = (φ.map σ).map τ := by
  (obtain ⟨ctx, f⟩ := φ
   exact congrArg (Sentence.mk (τ.sorts ∘ σ.sorts ∘ ctx)) (Formula.map_comp σ τ f))

/-- The satisfaction condition for first-order logic.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 65, and Examples 66–67. -/
theorem Sentence.holds_map {Sg Sg' : Signature} (σ : Sg ⟶ Sg') (M : Structure Sg')
    (φ : Sentence Sg) : (φ.map σ).Holds M ↔ φ.Holds ((Structure.reduct σ).obj M) := by
  exact Formula.holds_map σ M φ.formula _

/-- The room of first-order logic over a signature. -/
def room (Sg : Signature) : Room.{0, 0, 1} :=
  ⟨Sentence Sg, Cat.of (Structure Sg), fun (M : Structure Sg) φ => φ.Holds M⟩

/-- The corridor of a signature morphism. -/
def corridor {Sg Sg' : Signature} (σ : Sg ⟶ Sg') : room Sg ⟶ room Sg' :=
  ⟨Sentence.map σ, Structure.reduct σ, fun (M : Structure Sg') φ => Sentence.holds_map σ M φ⟩

theorem corridor_id (Sg : Signature) : corridor (𝟙 Sg) = 𝟙 (room Sg) := by
  exact Room.hom_ext (funext Sentence.map_id) rfl

theorem corridor_comp {Sg Sg' Sg'' : Signature} (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'') :
    corridor (σ ≫ τ) = corridor σ ≫ corridor τ := by
  exact Room.hom_ext (funext (Sentence.map_comp σ τ)) rfl

/-- Many-sorted first-order logic with equality as an institution `FoSig ⥤ Room`.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, Examples 66
and 67. -/
def institution : Signature ⥤ Room.{0, 0, 1} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

/-- First-order logic as a bundled institution. -/
def inst : Inst.{1, 0, 0, 0, 1} := ⟨Signature, institution⟩

end Silmaril.Logic.Institution.Examples.FOL

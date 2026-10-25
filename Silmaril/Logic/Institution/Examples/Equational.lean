module

public import Silmaril.Logic.Institution.Morphism

@[expose] public section

/-!
# The institution of many-sorted equational logic

A signature `(S, Σ)` has a set of sorts and, for every arity `w : Fin n → S` and result sort
`s`, a set `Σ_{w,s}` of operation symbols. A signature morphism maps sorts and operation symbols
compatibly with arities. Models are many-sorted algebras with homomorphisms, and the reduct along
a signature morphism reindexes carriers and operations. Sentences are universally quantified
equations `(∀ X) t₁ = t₂` over an explicit finite sorted context `X : Fin k → S` (the explicit
variable declaration of Goguen–Burstall, Definition 56); a signature morphism translates the
context and the two terms.

Following Goguen–Roşu (Example 3.2(2)) carriers may be empty. Variables are de Bruijn indices
into the context, so translation never renames or captures variables.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1,
Definitions 48–59, Proposition 60 and Example 61.
-/

namespace Silmaril.Logic.Institution.Examples.EQ

open CategoryTheory

/-- A many-sorted equational signature.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 48
(with arities as functions `Fin n → S` instead of strings in `S*`). -/
structure Signature : Type 1 where
  /-- The sorts. -/
  S : Type
  /-- The operation symbols of arity `w` and result sort `s`. -/
  Op : (n : ℕ) → (Fin n → S) → S → Type

/-- A signature morphism: a sort map and an arity-respecting map of operation symbols.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 49. -/
structure Signature.Hom (Sg Sg' : Signature) : Type where
  /-- The sort map. -/
  sorts : Sg.S → Sg'.S
  /-- The operation-symbol map. -/
  ops : ∀ {n : ℕ} {w : Fin n → Sg.S} {s : Sg.S}, Sg.Op n w s → Sg'.Op n (sorts ∘ w) (sorts s)

/-- The category of equational signatures.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 50. -/
instance : Category.{0} Signature where
  Hom := Signature.Hom
  id _ := ⟨id, fun o => o⟩
  comp f g := ⟨g.sorts ∘ f.sorts, fun o => g.ops (f.ops o)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Terms of sort `s` over a signature and a finite sorted context `Γ`.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1 (the term
algebra `T_Σ(X)`, Theorem 55), with variables as indices into the context. -/
inductive Term (Sg : Signature) {k : ℕ} (Γ : Fin k → Sg.S) : Sg.S → Type
  | var (i : Fin k) : Term Sg Γ (Γ i)
  | app {n : ℕ} {w : Fin n → Sg.S} {s : Sg.S} (o : Sg.Op n w s) (args : ∀ j, Term Sg Γ (w j)) :
      Term Sg Γ s

namespace Term

variable {Sg Sg' Sg'' : Signature} {k : ℕ} {Γ : Fin k → Sg.S}

/-- Translation of terms along a signature morphism.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 58. -/
def map (σ : Sg ⟶ Sg') : {s : Sg.S} → Term Sg Γ s → Term Sg' (σ.sorts ∘ Γ) (σ.sorts s)
  | _, var i => var i
  | _, app o args => app (σ.ops o) (fun j => map σ (args j))

theorem map_id {s : Sg.S} (t : Term Sg Γ s) : t.map (𝟙 Sg) = t := by
  (induction t with
     | var i => rfl
     | app o args ih => simp only [map]; congr 1; funext j; exact ih j)

theorem map_comp (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'') {s : Sg.S} (t : Term Sg Γ s) :
    t.map (σ ≫ τ) = (t.map σ).map τ := by
  (induction t with
     | var i => rfl
     | app o args ih => simp only [map]; congr 1; funext j; exact ih j)

end Term

/-- A many-sorted algebra: a carrier for every sort and a function for every operation symbol.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 51
(empty carriers allowed, as in `goguen-rosu-2002-institution-morphisms` in `references.bib`,
Example 3.2(2)). -/
structure Algebra (Sg : Signature) : Type 1 where
  /-- The carrier of each sort. -/
  carrier : Sg.S → Type
  /-- The interpretation of each operation symbol. -/
  op : ∀ {n : ℕ} {w : Fin n → Sg.S} {s : Sg.S}, Sg.Op n w s → (∀ j, carrier (w j)) → carrier s

/-- A homomorphism of algebras.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 52. -/
structure Algebra.Hom {Sg : Signature} (A B : Algebra Sg) : Type where
  /-- The sorted map of carriers. -/
  map : ∀ s, A.carrier s → B.carrier s
  /-- The homomorphism condition. -/
  map_op : ∀ {n : ℕ} {w : Fin n → Sg.S} {s : Sg.S} (o : Sg.Op n w s) (args : ∀ j, A.carrier (w j)),
    map s (A.op o args) = B.op o (fun j => map (w j) (args j))

/-- The category `Alg_Σ` of algebras.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 53. -/
instance (Sg : Signature) : Category.{0} (Algebra Sg) where
  Hom := Algebra.Hom
  id _ := ⟨fun _ x => x, fun _ _ => rfl⟩
  comp f g := ⟨fun s x => g.map s (f.map s x), fun o args => by rw [f.map_op, g.map_op]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The reduct functor `Alg(σ) : Alg_{Σ'} ⥤ Alg_Σ`.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 54. -/
def Algebra.reduct {Sg Sg' : Signature} (σ : Sg ⟶ Sg') : Algebra Sg' ⥤ Algebra Sg where
  obj A := ⟨fun s => A.carrier (σ.sorts s), fun o args => A.op (σ.ops o) args⟩
  map h := ⟨fun s => h.map (σ.sorts s), fun o args => h.map_op (σ.ops o) args⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation of a term under an assignment of the context variables.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 57
(the unique extension `a#` of an assignment, Theorem 55). -/
def Term.eval {Sg : Signature} {k : ℕ} {Γ : Fin k → Sg.S} (A : Algebra Sg)
    (ρ : ∀ i, A.carrier (Γ i)) : {s : Sg.S} → Term Sg Γ s → A.carrier s
  | _, .var i => ρ i
  | _, .app o args => A.op o (fun j => (args j).eval A ρ)

/-- Evaluating a translated term in a `Σ'`-algebra is evaluating the term in the reduct.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, the lemma
underlying Proposition 60. -/
theorem Term.eval_map {Sg Sg' : Signature} (σ : Sg ⟶ Sg') {k : ℕ} {Γ : Fin k → Sg.S}
    (A : Algebra Sg') (ρ : ∀ i, A.carrier (σ.sorts (Γ i))) {s : Sg.S} (t : Term Sg Γ s) :
    (t.map σ).eval A ρ = t.eval ((Algebra.reduct σ).obj A) ρ := by
  (induction t with
     | var i => rfl
     | app o args ih => simp only [Term.map, Term.eval]; congr 1; funext j; exact ih j)

/-- A `Σ`-equation `(∀ X) t₁ = t₂`, with its context declared explicitly.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 56. -/
structure Equation (Sg : Signature) : Type where
  /-- The number of declared variables. -/
  k : ℕ
  /-- The sorts of the declared variables. -/
  ctx : Fin k → Sg.S
  /-- The common sort of both sides. -/
  sort : Sg.S
  /-- The left-hand side. -/
  lhs : Term Sg ctx sort
  /-- The right-hand side. -/
  rhs : Term Sg ctx sort

/-- Translation of equations: `Eqn(σ)((X, t₁, t₂)) = (X;σ, σ(t₁), σ(t₂))`.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 59. -/
def Equation.map {Sg Sg' : Signature} (σ : Sg ⟶ Sg') (e : Equation Sg) : Equation Sg' :=
  ⟨e.k, σ.sorts ∘ e.ctx, σ.sorts e.sort, e.lhs.map σ, e.rhs.map σ⟩

/-- Equational satisfaction: both sides agree under every assignment.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Definition 57. -/
def Equation.Holds {Sg : Signature} (A : Algebra Sg) (e : Equation Sg) : Prop :=
  ∀ ρ : ∀ i, A.carrier (e.ctx i), e.lhs.eval A ρ = e.rhs.eval A ρ

theorem Equation.map_id {Sg : Signature} (e : Equation Sg) : e.map (𝟙 Sg) = e := by
  (obtain ⟨k, ctx, s, l, r⟩ := e; simp only [Equation.map, Term.map_id]; rfl)

theorem Equation.map_comp {Sg Sg' Sg'' : Signature} (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'')
    (e : Equation Sg) : e.map (σ ≫ τ) = (e.map σ).map τ := by
  (obtain ⟨k, ctx, s, l, r⟩ := e; simp only [Equation.map, Term.map_comp]; rfl)

/-- The satisfaction condition for many-sorted equational logic.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1,
Proposition 60. -/
theorem Equation.holds_map {Sg Sg' : Signature} (σ : Sg ⟶ Sg') (A : Algebra Sg')
    (e : Equation Sg) : (e.map σ).Holds A ↔ e.Holds ((Algebra.reduct σ).obj A) := by
  (simp only [Equation.Holds, Equation.map, Term.eval_map]; rfl)

/-- The room of equational logic over a signature. -/
def room (Sg : Signature) : Room.{0, 0, 1} :=
  ⟨Equation Sg, Cat.of (Algebra Sg), fun (A : Algebra Sg) e => e.Holds A⟩

/-- The corridor of a signature morphism. -/
def corridor {Sg Sg' : Signature} (σ : Sg ⟶ Sg') : room Sg ⟶ room Sg' :=
  ⟨Equation.map σ, Algebra.reduct σ, fun (A : Algebra Sg') e => Equation.holds_map σ A e⟩

theorem corridor_id (Sg : Signature) : corridor (𝟙 Sg) = 𝟙 (room Sg) := by
  exact Room.hom_ext (funext Equation.map_id) rfl

theorem corridor_comp {Sg Sg' Sg'' : Signature} (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'') :
    corridor (σ ≫ τ) = corridor σ ≫ corridor τ := by
  exact Room.hom_ext (funext (Equation.map_comp σ τ)) rfl

/-- Many-sorted equational logic as an institution `Sig ⥤ Room`.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A1, Example 61. -/
def institution : Signature ⥤ Room.{0, 0, 1} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

/-- Many-sorted equational logic as a bundled institution. -/
def inst : Inst.{1, 0, 0, 0, 1} := ⟨Signature, institution⟩

end Silmaril.Logic.Institution.Examples.EQ

module

public import Silmaril.Logic.Institution.Examples.Comorphisms
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# Finite CASL signatures as first-order signatures

A CASL basic specification with total operations and no subsorts is a presentation in
many-sorted first-order logic with equality (`Examples.FOL`). `FinSig` records finitely many
sorts, a list of operation declarations `f : s₁ × ⋯ × sₙ → s` and a list of predicate
declarations `p : s₁ × ⋯ × sₙ`, each symbol identified by its position.

* `FinSig.toSignature`: the first-order signature; its operation (relation) symbols of arity
  `(w, s)` are the declarations with that arity (`FinSig.Op.mk`, `FinSig.Rel.mk`).
* `FinSig.Mor`: a signature morphism given by index maps on sorts, operations and predicates
  that respect arities; concrete arity conditions can be checked with `decide`.
  `Mor.toHom` is the first-order signature morphism, functorial (`Mor.toHom_id`,
  `Mor.toHom_comp`).
* `FinSig.app`, `FinSig.pred`, `FinSig.imp`, `FinSig.ex`, …: term and formula constructors,
  including CASL's `⇒`, `∨`, `⇔`, `∃`, `false` in terms of `¬`, `∧`, `∀`, `true`.
* `FinSig.model1`: a single-sorted structure from interpretations of the symbols by index, used
  to build models of the selected library presentations from Mathlib structures.

See `docs/projects/logic.md#hets` for the supported specification fragment and examples.

## References

* `cofi-2004-casl-reference-manual` in `references.bib`: Part I §2 (printed pages 5–26,
  PDF pages 19–40: basic specifications) and Part III §2.1 (printed pages 124–126, PDF
  pages 138–140: many-sorted signatures and signature morphisms).
* `goguen-burstall-1992` in `references.bib`, Appendix A2, Definitions 62–65.
-/

namespace Silmaril.Logic.Institution.Hets.CASL

open CategoryTheory Silmaril.Logic.Institution.Examples

/-- An operation declaration `f : s₁ × ⋯ × sₙ → s` over the sorts `Fin k`. -/
structure OpDecl (k : ℕ) where
  /-- The CASL name, for printing and provenance. -/
  name : String
  /-- The number of arguments. -/
  arity : ℕ
  /-- The argument sorts. -/
  args : Fin arity → Fin k
  /-- The result sort. -/
  res : Fin k

/-- A predicate declaration `p : s₁ × ⋯ × sₙ` over the sorts `Fin k`. -/
structure PredDecl (k : ℕ) where
  /-- The CASL name, for printing and provenance. -/
  name : String
  /-- The number of arguments. -/
  arity : ℕ
  /-- The argument sorts. -/
  args : Fin arity → Fin k

/-- The arity `(n, w, s)` of an operation symbol. -/
abbrev OpAr (k : ℕ) : Type := Σ n : ℕ, (Fin n → Fin k) × Fin k

/-- The arity `(n, w)` of a predicate symbol. -/
abbrev PredAr (k : ℕ) : Type := Σ n : ℕ, Fin n → Fin k

/-- Renaming the sorts of an operation arity. -/
def OpAr.map {k k' : ℕ} (g : Fin k → Fin k') (a : OpAr k) : OpAr k' := ⟨a.1, (g ∘ a.2.1, g a.2.2)⟩

/-- Renaming the sorts of a predicate arity. -/
def PredAr.map {k k' : ℕ} (g : Fin k → Fin k') (a : PredAr k) : PredAr k' := ⟨a.1, g ∘ a.2⟩

/-- The arity of an operation declaration. -/
def OpDecl.ar {k : ℕ} (o : OpDecl k) : OpAr k := ⟨o.arity, (o.args, o.res)⟩

/-- The arity of a predicate declaration. -/
def PredDecl.ar {k : ℕ} (p : PredDecl k) : PredAr k := ⟨p.arity, p.args⟩

/-- A finite many-sorted CASL signature with total operations and no subsorts.

Source: `cofi-2004-casl-reference-manual` in `references.bib`, Part III §2.1 (printed
page 124, PDF page 138: "A many-sorted signature Σ consists of: a set of sorts; …"), without partial
operations. -/
structure FinSig where
  /-- The number of sorts. -/
  nSorts : ℕ
  /-- The CASL sort names. -/
  sortNames : Fin nSorts → String
  /-- The operation declarations. -/
  ops : List (OpDecl nSorts)
  /-- The predicate declarations. -/
  preds : List (PredDecl nSorts)

namespace FinSig

variable (D : FinSig)

/-- The sorts. -/
abbrev Srt : Type := Fin D.nSorts

/-- Operation symbols of arity `(n, w, s)`: the declarations with that arity. -/
inductive Op : (n : ℕ) → (Fin n → D.Srt) → D.Srt → Type
  /-- The `i`-th declared operation. -/
  | mk (i : Fin D.ops.length) : Op (D.ops.get i).arity (D.ops.get i).args (D.ops.get i).res

/-- Predicate symbols of arity `(n, w)`: the declarations with that arity. -/
inductive Rel : (n : ℕ) → (Fin n → D.Srt) → Type
  /-- The `i`-th declared predicate. -/
  | mk (i : Fin D.preds.length) : Rel (D.preds.get i).arity (D.preds.get i).args

variable {D}

/-- The position of an operation symbol. -/
def Op.idx {n : ℕ} {w : Fin n → D.Srt} {s : D.Srt} : D.Op n w s → Fin D.ops.length
  | .mk i => i

/-- The position of a predicate symbol. -/
def Rel.idx {n : ℕ} {w : Fin n → D.Srt} : D.Rel n w → Fin D.preds.length
  | .mk i => i

variable (D)

/-- The first-order signature of a finite CASL signature. -/
def toSignature : FOL.Signature where
  S := D.Srt
  Op := D.Op
  Rel := D.Rel

/-- A morphism of finite signatures: index maps on sorts, operations and predicates respecting
arities.

Source: `cofi-2004-casl-reference-manual` in `references.bib`, Part III §2.1 (printed
page 126, PDF page 140: many-sorted signature morphisms), without partial operations. -/
@[ext]
structure Mor (D D' : FinSig) where
  /-- The sort map. -/
  sorts : D.Srt → D'.Srt
  /-- The operation map. -/
  ops : Fin D.ops.length → Fin D'.ops.length
  /-- The predicate map. -/
  preds : Fin D.preds.length → Fin D'.preds.length
  /-- Operations are mapped to operations of the renamed arity. -/
  ops_ar : ∀ i, (D'.ops.get (ops i)).ar = (D.ops.get i).ar.map sorts
  /-- Predicates are mapped to predicates of the renamed arity. -/
  preds_ar : ∀ i, (D'.preds.get (preds i)).ar = (D.preds.get i).ar.map sorts

variable {D}

namespace Mor

/-- The identity morphism. -/
def id (D : FinSig) : Mor D D where
  sorts := _root_.id
  ops := _root_.id
  preds := _root_.id
  ops_ar _ := rfl
  preds_ar _ := rfl

/-- Composition of morphisms. -/
def comp {D D' D'' : FinSig} (m : Mor D D') (m' : Mor D' D'') : Mor D D'' where
  sorts := m'.sorts ∘ m.sorts
  ops := m'.ops ∘ m.ops
  preds := m'.preds ∘ m.preds
  ops_ar i := (m'.ops_ar (m.ops i)).trans (congrArg (OpAr.map m'.sorts) (m.ops_ar i))
  preds_ar i := (m'.preds_ar (m.preds i)).trans (congrArg (PredAr.map m'.sorts) (m.preds_ar i))

variable {D' : FinSig} (m : Mor D D')

/-- The operation-symbol map. -/
def opMap :
    ∀ {n : ℕ} {w : Fin n → D.Srt} {s : D.Srt}, D.Op n w s → D'.Op n (m.sorts ∘ w) (m.sorts s)
  | _, _, _, .mk i =>
    cast (congrArg (fun a : OpAr D'.nSorts => D'.Op a.1 a.2.1 a.2.2) (m.ops_ar i)) (Op.mk (m.ops i))

/-- The predicate-symbol map. -/
def relMap : ∀ {n : ℕ} {w : Fin n → D.Srt}, D.Rel n w → D'.Rel n (m.sorts ∘ w)
  | _, _, .mk i =>
    cast (congrArg (fun a : PredAr D'.nSorts => D'.Rel a.1 a.2) (m.preds_ar i)) (Rel.mk (m.preds i))

/-- The first-order signature morphism of a morphism of finite signatures. -/
def toHom : D.toSignature ⟶ D'.toSignature :=
  ({ sorts := m.sorts
     ops := fun o => m.opMap o
     rels := fun r => m.relMap r } : FOL.Signature.Hom D.toSignature D'.toSignature)

/-- Casting an operation symbol along an arity equality keeps its position. -/
theorem Op.idx_cast {D : FinSig} {a b : OpAr D.nSorts} (h : a = b) (o : D.Op a.1 a.2.1 a.2.2) :
    (cast (congrArg (fun a : OpAr D.nSorts => D.Op a.1 a.2.1 a.2.2) h) o).idx = o.idx := by
  subst h; rfl

/-- Casting a predicate symbol along an arity equality keeps its position. -/
theorem Rel.idx_cast {D : FinSig} {a b : PredAr D.nSorts} (h : a = b) (r : D.Rel a.1 a.2) :
    (cast (congrArg (fun a : PredAr D.nSorts => D.Rel a.1 a.2) h) r).idx = r.idx := by
  subst h; rfl

theorem opMap_heq {n : ℕ} {w : Fin n → D.Srt} {s : D.Srt} (o : D.Op n w s) :
    HEq (m.opMap o) (Op.mk (D := D') (m.ops o.idx)) := by
  cases o; exact cast_heq _ _

theorem relMap_heq {n : ℕ} {w : Fin n → D.Srt} (r : D.Rel n w) :
    HEq (m.relMap r) (Rel.mk (D := D') (m.preds r.idx)) := by
  cases r; exact cast_heq _ _

theorem opMap_idx {n : ℕ} {w : Fin n → D.Srt} {s : D.Srt} (o : D.Op n w s) :
    (m.opMap o).idx = m.ops o.idx := by
  cases o with | mk i => exact Op.idx_cast (m.ops_ar i) (Op.mk (m.ops i))

theorem relMap_idx {n : ℕ} {w : Fin n → D.Srt} (r : D.Rel n w) :
    (m.relMap r).idx = m.preds r.idx := by
  cases r with | mk i => exact Rel.idx_cast (m.preds_ar i) (Rel.mk (m.preds i))

theorem opMap_comp {D'' : FinSig} (m' : Mor D' D'') {n : ℕ} {w : Fin n → D.Srt} {s : D.Srt}
    (o : D.Op n w s) : (m.comp m').opMap o = m'.opMap (m.opMap o) := by
  apply eq_of_heq
  refine (opMap_heq _ o).trans (HEq.trans ?_ (opMap_heq m' _).symm)
  rw [opMap_idx]; rfl

theorem relMap_comp {D'' : FinSig} (m' : Mor D' D'') {n : ℕ} {w : Fin n → D.Srt}
    (r : D.Rel n w) : (m.comp m').relMap r = m'.relMap (m.relMap r) := by
  apply eq_of_heq
  refine (relMap_heq _ r).trans (HEq.trans ?_ (relMap_heq m' _).symm)
  rw [relMap_idx]; rfl

/-- `toHom` preserves identities. -/
theorem toHom_id (D : FinSig) : (Mor.id D).toHom = 𝟙 D.toSignature := by
  have hops : ∀ {n : ℕ} {w : Fin n → D.Srt} {s : D.Srt} (o : D.Op n w s), (Mor.id D).opMap o = o
    | _, _, _, .mk _ => rfl
  have hrels : ∀ {n : ℕ} {w : Fin n → D.Srt} (r : D.Rel n w), (Mor.id D).relMap r = r
    | _, _, .mk _ => rfl
  change (⟨⟨_root_.id, fun o => (Mor.id D).opMap o⟩, fun r => (Mor.id D).relMap r⟩ :
      FOL.Signature.Hom D.toSignature D.toSignature) = ⟨⟨_root_.id, fun o => o⟩, fun r => r⟩
  congr 1
  · congr 1
    funext n w s o
    exact hops o
  · funext n w r
    exact hrels r

/-- `toHom` preserves composition. -/
theorem toHom_comp {D'' : FinSig} (m' : Mor D' D'') : (m.comp m').toHom = m.toHom ≫ m'.toHom := by
  change (⟨⟨m'.sorts ∘ m.sorts, fun o => (m.comp m').opMap o⟩, fun r => (m.comp m').relMap r⟩ :
      FOL.Signature.Hom D.toSignature D''.toSignature) =
    ⟨⟨m'.sorts ∘ m.sorts, fun o => m'.opMap (m.opMap o)⟩, fun r => m'.relMap (m.relMap r)⟩
  congr 1
  · congr 1
    funext n w s o
    exact opMap_comp m m' o
  · funext n w r
    exact relMap_comp m m' r

end Mor

/-! ### Sentences -/

/-- Terms over a finite signature. -/
abbrev Tm (D : FinSig) {k : ℕ} (Γ : Fin k → D.Srt) (s : D.Srt) : Type :=
  EQ.Term D.toSignature.toSignature Γ s

/-- Formulas over a finite signature. -/
abbrev Fm (D : FinSig) {k : ℕ} (Γ : Fin k → D.Srt) : Type :=
  FOL.Formula D.toSignature Γ

variable {k : ℕ} {Γ : Fin k → D.Srt}

/-- Application of the `i`-th declared operation. -/
def app (i : Fin D.ops.length) (args : ∀ j, Tm D Γ ((D.ops.get i).args j)) :
    Tm D Γ (D.ops.get i).res :=
  .app (Op.mk i) args

/-- The atom of the `i`-th declared predicate. -/
def pred (i : Fin D.preds.length) (args : ∀ j, Tm D Γ ((D.preds.get i).args j)) : Fm D Γ :=
  .rel (Rel.mk i) args

/-- `false`. -/
def ff : Fm D Γ := .not .tt

/-- Implication `φ ⇒ ψ`, as `¬(φ ∧ ¬ψ)`. -/
def imp (φ ψ : Fm D Γ) : Fm D Γ := .not (.and φ (.not ψ))

/-- Disjunction `φ ∨ ψ`, as `¬(¬φ ∧ ¬ψ)`. -/
def or (φ ψ : Fm D Γ) : Fm D Γ := .not (.and (.not φ) (.not ψ))

/-- Equivalence `φ ⇔ ψ`. -/
def iff (φ ψ : Fm D Γ) : Fm D Γ := .and (imp φ ψ) (imp ψ φ)

/-- Existential quantification of the first variable of an extended context, as `¬∀¬`. -/
def ex {Δ : Fin (k + 1) → D.Srt} (h : Δ ∘ Fin.succ = Γ) (φ : Fm D Δ) : Fm D Γ :=
  .not (.all h (.not φ))

/-- The universal closure of a formula: a CASL axiom `∀ x₁ … xₖ • φ`. The variable `0` is
bound innermost. -/
def closed (Γ : Fin k → D.Srt) (φ : Fm D Γ) : FOL.Sentence D.toSignature :=
  EQtoFOL.closeAll (Sg := D.toSignature) Γ φ

theorem holds_closed (M : FOL.Structure D.toSignature) (φ : Fm D Γ) :
    (closed Γ φ).Holds M ↔ ∀ ρ, φ.Holds M ρ :=
  EQtoFOL.holds_closeAll M Γ φ

theorem holds_imp (M : FOL.Structure D.toSignature) (φ ψ : Fm D Γ) (ρ) :
    (imp φ ψ).Holds M ρ ↔ (φ.Holds M ρ → ψ.Holds M ρ) := by
  simp only [imp, FOL.Formula.Holds]
  tauto

theorem holds_or (M : FOL.Structure D.toSignature) (φ ψ : Fm D Γ) (ρ) :
    (or φ ψ).Holds M ρ ↔ (φ.Holds M ρ ∨ ψ.Holds M ρ) := by
  simp only [or, FOL.Formula.Holds]
  tauto

/-! ### Single-sorted structures -/

/-- A structure for a finite signature with every sort interpreted by `A`, from interpretations
of the operations and predicates by position, applied to the list of arguments. -/
def model1 (D : FinSig) (A : Type) (op : Fin D.ops.length → List A → A)
    (rel : Fin D.preds.length → List A → Prop) : FOL.Structure D.toSignature where
  carrier _ := A
  op o args := op o.idx (List.ofFn args)
  rel r args := rel r.idx (List.ofFn args)

end FinSig

end Silmaril.Logic.Institution.Hets.CASL

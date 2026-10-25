module

public import Silmaril.Logic.Institution.Faithful
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# The institution of unsorted first-order logic with equality

Goguen–Roşu's `FOLE` (Example 3.2(5)), the one-sorted special case of
`Silmaril.Logic.Institution.Examples.FOL`, in its classical form: carriers are **nonempty**
(this is the "usual institution of single-sorted classical first-order logic" of
Mossakowski–Diaconescu–Tarlecki, Example 4.7, and the `FOL` of the Hets logic graph for Common
Logic). Signatures are arity-indexed families of operation and relation symbols; formulas use de
Bruijn variables, with `true`, `¬`, `∧`, `∀`, equations and relational atoms.

* `UFOL.institution`, `UFOL.inst`: the institution, with satisfaction condition
  `UFOL.Formula.holds_map`.
* `UFOL.Formula.holds_iso`, `UFOL.isoInvariant`: satisfaction is invariant under isomorphism
  of structures, so comorphisms into another logic that reach structures up to isomorphism are
  faithful (`Silmaril.Logic.Institution.Corridor.IsoExpansive.elemExpansive`).

Its relation to many-sorted first-order logic is the simple theoroidal comorphism
`Silmaril.Logic.Institution.Examples.ufolToFol`, and to Common Logic the comorphism
`Silmaril.Logic.CommonLogic.FromFOL.folToCl`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Example 3.2(4)–(5),
p. 8; `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Example 4.7; `goguen-burstall-1992` in `references.bib`, Appendix A2,
Definitions 62–65 (the one-sorted case).
-/

namespace Silmaril.Logic.Institution.Examples.UFOL

open CategoryTheory

/-- An unsorted first-order signature: operation and relation symbols of each arity. -/
structure Signature : Type 1 where
  /-- The operation symbols of arity `n`. -/
  Op : ℕ → Type
  /-- The relation symbols of arity `n`. -/
  Rel : ℕ → Type

/-- An arity-preserving map of symbols. -/
structure Signature.Hom (Sg Sg' : Signature) : Type where
  /-- The operation-symbol map. -/
  ops : ∀ {n : ℕ}, Sg.Op n → Sg'.Op n
  /-- The relation-symbol map. -/
  rels : ∀ {n : ℕ}, Sg.Rel n → Sg'.Rel n

instance : Category.{0} Signature where
  Hom := Signature.Hom
  id _ := ⟨fun o => o, fun r => r⟩
  comp f g := ⟨fun o => g.ops (f.ops o), fun r => g.rels (f.rels r)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- An unsorted first-order structure with a nonempty carrier. -/
structure Structure (Sg : Signature) : Type 1 where
  /-- The carrier. -/
  carrier : Type
  /-- The carrier is nonempty. -/
  nonempty : Nonempty carrier
  /-- The interpretation of operation symbols. -/
  op : ∀ {n : ℕ}, Sg.Op n → (Fin n → carrier) → carrier
  /-- The interpretation of relation symbols. -/
  rel : ∀ {n : ℕ}, Sg.Rel n → (Fin n → carrier) → Prop

/-- Homomorphisms of structures: maps commuting with operations and preserving relations. -/
structure Structure.Hom {Sg : Signature} (M N : Structure Sg) : Type where
  /-- The map of carriers. -/
  map : M.carrier → N.carrier
  /-- Operations commute with the map. -/
  map_op : ∀ {n : ℕ} (o : Sg.Op n) (args : Fin n → M.carrier), map (M.op o args) = N.op o (map ∘ args)
  /-- Relations are preserved. -/
  map_rel : ∀ {n : ℕ} (r : Sg.Rel n) (args : Fin n → M.carrier), M.rel r args → N.rel r (map ∘ args)

instance (Sg : Signature) : Category.{0} (Structure Sg) where
  Hom := Structure.Hom
  id _ := ⟨id, fun _ _ => rfl, fun _ _ h => h⟩
  comp f g := ⟨g.map ∘ f.map, fun o args =>
      (congrArg g.map (f.map_op o args)).trans (g.map_op o _),
    fun r args h => g.map_rel r (f.map ∘ args) (f.map_rel r args h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The reduct functor along a signature morphism. -/
def Structure.reduct {Sg Sg' : Signature} (σ : Sg ⟶ Sg') : Structure Sg' ⥤ Structure Sg where
  obj M := ⟨M.carrier, M.nonempty, fun o => M.op (σ.ops o), fun r => M.rel (σ.rels r)⟩
  map h := ⟨h.map, fun o => h.map_op (σ.ops o), fun r => h.map_rel (σ.rels r)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Terms over `k` de Bruijn variables. -/
inductive Term (Sg : Signature) (k : ℕ) : Type
  | var (i : Fin k)
  | app {n : ℕ} (o : Sg.Op n) (args : Fin n → Term Sg k)

/-- Formulas over `k` de Bruijn variables: equations, relational atoms, `true`, `¬`, `∧`, and
`∀` binding variable `0`. -/
inductive Formula (Sg : Signature) : ℕ → Type
  | eq {k : ℕ} (t u : Term Sg k) : Formula Sg k
  | rel {k n : ℕ} (r : Sg.Rel n) (args : Fin n → Term Sg k) : Formula Sg k
  | tt {k : ℕ} : Formula Sg k
  | not {k : ℕ} (φ : Formula Sg k) : Formula Sg k
  | and {k : ℕ} (φ ψ : Formula Sg k) : Formula Sg k
  | all {k : ℕ} (φ : Formula Sg (k + 1)) : Formula Sg k

/-- Sentences: closed formulas. -/
abbrev Sentence (Sg : Signature) : Type := Formula Sg 0

variable {Sg Sg' Sg'' : Signature}

/-- Translation of terms. -/
def Term.map (σ : Sg ⟶ Sg') {k : ℕ} : Term Sg k → Term Sg' k
  | .var i => .var i
  | .app o args => .app (σ.ops o) (fun j => (args j).map σ)

/-- Evaluation of terms. -/
def Term.eval (M : Structure Sg) {k : ℕ} (ρ : Fin k → M.carrier) : Term Sg k → M.carrier
  | .var i => ρ i
  | .app o args => M.op o (fun j => (args j).eval M ρ)

/-- Translation of formulas. -/
def Formula.map (σ : Sg ⟶ Sg') : {k : ℕ} → Formula Sg k → Formula Sg' k
  | _, .eq t u => .eq (t.map σ) (u.map σ)
  | _, .rel r args => .rel (σ.rels r) (fun j => (args j).map σ)
  | _, .tt => .tt
  | _, .not φ => .not (φ.map σ)
  | _, .and φ ψ => .and (φ.map σ) (ψ.map σ)
  | _, .all φ => .all (φ.map σ)

/-- Tarskian satisfaction under an assignment of the de Bruijn variables. -/
def Formula.Holds (M : Structure Sg) : {k : ℕ} → Formula Sg k → (Fin k → M.carrier) → Prop
  | _, .eq t u, ρ => t.eval M ρ = u.eval M ρ
  | _, .rel r args, ρ => M.rel r (fun j => (args j).eval M ρ)
  | _, .tt, _ => True
  | _, .not φ, ρ => ¬ φ.Holds M ρ
  | _, .and φ ψ, ρ => φ.Holds M ρ ∧ ψ.Holds M ρ
  | _, .all φ, ρ => ∀ x : M.carrier, φ.Holds M (Fin.cons x ρ)

/-- Satisfaction of a sentence. -/
def Sentence.Holds (M : Structure Sg) (φ : Sentence Sg) : Prop := Formula.Holds M φ Fin.elim0

theorem Term.map_id {k : ℕ} (t : Term Sg k) : t.map (𝟙 Sg) = t := by
  induction t with
  | var i => rfl
  | app o args ih => exact congrArg (Term.app o) (funext ih)

theorem Term.map_comp (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'') {k : ℕ} (t : Term Sg k) :
    t.map (σ ≫ τ) = (t.map σ).map τ := by
  induction t with
  | var i => rfl
  | app o args ih => exact congrArg (Term.app (τ.ops (σ.ops o))) (funext ih)

theorem Term.eval_map (σ : Sg ⟶ Sg') (M : Structure Sg') {k : ℕ} (ρ : Fin k → M.carrier)
    (t : Term Sg k) : (t.map σ).eval M ρ = t.eval ((Structure.reduct σ).obj M) ρ := by
  induction t with
  | var i => rfl
  | app o args ih => exact congrArg (M.op (σ.ops o)) (funext ih)

theorem Formula.map_id {k : ℕ} (φ : Formula Sg k) : φ.map (𝟙 Sg) = φ := by
  induction φ with
  | eq t u => exact congrArg₂ Formula.eq (Term.map_id t) (Term.map_id u)
  | rel r args => exact congrArg (Formula.rel r) (funext fun j => Term.map_id (args j))
  | tt => rfl
  | not φ ih => exact congrArg Formula.not ih
  | and φ ψ ih₁ ih₂ => exact congrArg₂ Formula.and ih₁ ih₂
  | all φ ih => exact congrArg Formula.all ih

theorem Formula.map_comp (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'') {k : ℕ} (φ : Formula Sg k) :
    φ.map (σ ≫ τ) = (φ.map σ).map τ := by
  induction φ with
  | eq t u => exact congrArg₂ Formula.eq (Term.map_comp σ τ t) (Term.map_comp σ τ u)
  | rel r args =>
    exact congrArg (Formula.rel (τ.rels (σ.rels r))) (funext fun j => Term.map_comp σ τ (args j))
  | tt => rfl
  | not φ ih => exact congrArg Formula.not ih
  | and φ ψ ih₁ ih₂ => exact congrArg₂ Formula.and ih₁ ih₂
  | all φ ih => exact congrArg Formula.all ih

/-- The satisfaction condition for formulas. -/
theorem Formula.holds_map (σ : Sg ⟶ Sg') (M : Structure Sg') {k : ℕ} (φ : Formula Sg k)
    (ρ : Fin k → M.carrier) :
    (φ.map σ).Holds M ρ ↔ φ.Holds ((Structure.reduct σ).obj M) ρ := by
  induction φ with
  | eq t u =>
    exact Iff.of_eq (congrArg₂ (· = ·) (Term.eval_map σ M ρ t) (Term.eval_map σ M ρ u))
  | rel r args =>
    exact Iff.of_eq (congrArg (M.rel (σ.rels r)) (funext fun j => Term.eval_map σ M ρ (args j)))
  | tt => exact Iff.rfl
  | not φ ih => exact not_congr (ih ρ)
  | and φ ψ ih₁ ih₂ => exact and_congr (ih₁ ρ) (ih₂ ρ)
  | all φ ih => exact forall_congr' fun x => ih (Fin.cons x ρ)

/-- Terms commute with isomorphisms of structures. -/
theorem Term.eval_iso {M N : Structure Sg} (e : M ≅ N) {k : ℕ} (ρ : Fin k → M.carrier)
    (t : Term Sg k) : e.hom.map (t.eval M ρ) = t.eval N (e.hom.map ∘ ρ) := by
  induction t with
  | var i => rfl
  | app o args ih =>
    exact (e.hom.map_op o _).trans (congrArg (N.op o) (funext ih))

/-- Satisfaction is invariant under isomorphism of structures. -/
theorem Formula.holds_iso {M N : Structure Sg} (e : M ≅ N) {k : ℕ} (φ : Formula Sg k)
    (ρ : Fin k → M.carrier) : φ.Holds M ρ ↔ φ.Holds N (e.hom.map ∘ ρ) := by
  have hinv : ∀ x, e.inv.map (e.hom.map x) = x := fun x =>
    congrFun (congrArg Structure.Hom.map e.hom_inv_id) x
  have hinv' : ∀ y, e.hom.map (e.inv.map y) = y := fun y =>
    congrFun (congrArg Structure.Hom.map e.inv_hom_id) y
  have hsurj : Function.Surjective e.hom.map := fun y => ⟨e.inv.map y, hinv' y⟩
  induction φ with
  | eq t u =>
    show t.eval M ρ = u.eval M ρ ↔ t.eval N (e.hom.map ∘ ρ) = u.eval N (e.hom.map ∘ ρ)
    rw [← Term.eval_iso e ρ t, ← Term.eval_iso e ρ u]
    exact ⟨congrArg e.hom.map, fun h => by rw [← hinv (t.eval M ρ), h, hinv]⟩
  | rel r args =>
    show M.rel r (fun j => (args j).eval M ρ) ↔ N.rel r (fun j => (args j).eval N (e.hom.map ∘ ρ))
    have hargs : (fun j => (args j).eval N (e.hom.map ∘ ρ)) =
        e.hom.map ∘ (fun j => (args j).eval M ρ) :=
      funext fun j => (Term.eval_iso e ρ (args j)).symm
    rw [hargs]
    refine ⟨e.hom.map_rel r _, fun h => ?_⟩
    have h' := e.inv.map_rel r _ h
    have hc : e.inv.map ∘ e.hom.map ∘ (fun j => (args j).eval M ρ) =
        fun j => (args j).eval M ρ := funext fun j => hinv _
    rwa [hc] at h'
  | tt => exact Iff.rfl
  | not φ ih => exact not_congr (ih ρ)
  | and φ ψ ih₁ ih₂ => exact and_congr (ih₁ ρ) (ih₂ ρ)
  | all φ ih =>
    show (∀ x, φ.Holds M (Fin.cons x ρ)) ↔ ∀ y, φ.Holds N (Fin.cons y (e.hom.map ∘ ρ))
    rw [hsurj.forall]
    refine forall_congr' fun x => ?_
    rw [← Fin.comp_cons]
    exact ih (Fin.cons x ρ)

/-- The room of unsorted first-order logic over a signature. -/
def room (Sg : Signature) : Room.{0, 0, 1} :=
  ⟨Sentence Sg, Cat.of (Structure Sg), fun (M : Structure Sg) φ => Sentence.Holds M φ⟩

/-- The corridor of a signature morphism. -/
def corridor (σ : Sg ⟶ Sg') : room Sg ⟶ room Sg' :=
  ⟨Formula.map σ, Structure.reduct σ, fun (M : Structure Sg') φ => Formula.holds_map σ M φ Fin.elim0⟩

theorem corridor_id (Sg : Signature) : corridor (𝟙 Sg) = 𝟙 (room Sg) :=
  Room.hom_ext (funext fun φ => Formula.map_id φ) rfl

theorem corridor_comp (σ : Sg ⟶ Sg') (τ : Sg' ⟶ Sg'') :
    corridor (σ ≫ τ) = corridor σ ≫ corridor τ :=
  Room.hom_ext (funext fun φ => Formula.map_comp σ τ φ) rfl

/-- Unsorted first-order logic with equality as an institution.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, Example 3.2(5). -/
def institution : Signature ⥤ Room.{0, 0, 1} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

/-- Unsorted first-order logic as a bundled institution. -/
def inst : Inst.{1, 0, 0, 0, 1} := ⟨Signature, institution⟩

/-- Satisfaction of unsorted first-order sentences is invariant under isomorphism. -/
theorem isoInvariant (Sg : Signature) : (institution.obj Sg).IsoInvariant := by
  rintro M N ⟨e⟩ φ
  have h := Formula.holds_iso (M := M) (N := N) e φ Fin.elim0
  have h0 : (e.hom.map ∘ Fin.elim0 : Fin 0 → N.carrier) = Fin.elim0 := funext fun i => i.elim0
  rw [h0] at h
  exact h

end Silmaril.Logic.Institution.Examples.UFOL

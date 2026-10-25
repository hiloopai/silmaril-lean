module

public import Silmaril.Logic.Metamath.Peano.Axioms
public import Silmaril.Logic.Metamath.Model.Env
public import Silmaril.Logic.Metamath.Model.Consistency

@[expose] public section

/-!
# The standard model of `peano.mm`

The standard model of Peano arithmetic, as an environment model
(`Silmaril.Logic.Metamath.Model.Env`) over the natural numbers `ℕ` and an
infinite type `N` of object-variable names (`Peano.stdModel`):

* `var` denotes names, `term` finitely supported functions from environments
  `N → ℕ` to `ℕ`, and `wff` finitely supported formulas;
* the operator typecodes denote finitely supported functions into the
  corresponding operations: `BINOP` into `ℕ → ℕ → ℕ`, `LOGBINOP` into
  `Prop → Prop → Prop`, `BINPRED` into `ℕ → ℕ → Prop` and `QUANT` into
  generalized quantifiers `(ℕ → Prop) → Prop`;
* the constants denote zero, successor, addition, multiplication, equality,
  order, the connectives and the two quantifiers; `quant x phi` applies the
  quantifier to the formula as a predicate of the value of `x`;
* `|- phi` holds when `phi` is valid.

Every axiom of `peano.mm` holds in the standard model (`Peano.isModel_PA`),
including the schemes quantified over arbitrary binary operations, predicates
and quantifiers. Hence every tree theorem of `PA` is true in the model
(`Peano.sound`), and, the grammar being unambiguous, so is every string
theorem of the flattened system. The model is not trivial, so `PA` is
consistent at the tree and string levels (`Peano.tConsistent`,
`Peano.nonUniversal`, `Peano.theory_ne_top`); for instance it does not prove
`|- = 0 S 0` (`Peano.not_derivable_zero_eq_one`).
-/

namespace Silmaril.Logic.Metamath.Peano

open Silmaril.Logic.Metamath Grammar Grammar.TAssertion Silmaril.Logic.SetTheory Function Env

section Ops

variable {N : Type} [DecidableEq N]

/-- Apply a term whose values are binary functions to two terms. -/
def app₂ {A B R : Type} (f : Term ℕ N (A → B → R)) (a : Term ℕ N A) (b : Term ℕ N B) :
    Term ℕ N R :=
  Term.map₂ (fun g p => g p.1 p.2) f (Term.map₂ Prod.mk a b)

/-- Apply a quantifier to a formula as a predicate of the value of the name `x`. -/
def opQuant (q : Term ℕ N ((ℕ → Prop) → Prop)) (x : N) (φ : Term ℕ N Prop) :
    Term ℕ N Prop :=
  Term.map₂ (fun Q P => Q P) q (φ.bind x id)

@[simp] theorem app₂_apply {A B R : Type} (f : Term ℕ N (A → B → R)) (a : Term ℕ N A)
    (b : Term ℕ N B) (E : SetTheory.Env ℕ N) : (app₂ f a b).1 E = f.1 E (a.1 E) (b.1 E) := rfl

@[simp] theorem opQuant_apply (q : Term ℕ N ((ℕ → Prop) → Prop)) (x : N)
    (φ : Term ℕ N Prop)
    (E : SetTheory.Env ℕ N) : (opQuant q x φ).1 E = q.1 E fun m => φ.1 (update E x m) := rfl

omit [DecidableEq N] in
@[simp] theorem const_apply {R : Type} (r : R) (E : SetTheory.Env ℕ N) :
    (Term.const r : Term ℕ N R).1 E = r := rfl

omit [DecidableEq N] in
@[simp] theorem map_apply {A R : Type} (g : A → R) (a : Term ℕ N A) (E : SetTheory.Env ℕ N) :
    (a.map g).1 E = g (a.1 E) := rfl

omit [DecidableEq N] in
@[simp] theorem name_apply {R : Type} (x : N) (g : ℕ → R) (E : SetTheory.Env ℕ N) :
    (Term.name x g).1 E = g (E x) := rfl

theorem notFree_app₂ {A B R : Type} {x : N} {f : Term ℕ N (A → B → R)} {a : Term ℕ N A}
    {b : Term ℕ N B} (hf : NotFree x f.1) (ha : NotFree x a.1) (hb : NotFree x b.1) :
    NotFree x (app₂ f a b).1 :=
  Term.notFree_map₂ hf (Term.notFree_map₂ ha hb)

theorem notFree_opQuant {x y : N} (hxy : y ≠ x) {q : Term ℕ N ((ℕ → Prop) → Prop)}
    {φ : Term ℕ N Prop} (hq : NotFree y q.1) (hφ : NotFree y φ.1) :
    NotFree y (opQuant q x φ).1 :=
  Term.notFree_map₂ hq (Term.notFree_bind hxy hφ)

theorem notFree_const {R : Type} (r : R) (x : N) : NotFree x (Term.const r : Term ℕ N R).1 :=
  fun _ _ => rfl

end Ops

/-- The kinds of the typecodes in the standard model. -/
abbrev kind : C → Kind.{0}
  | .var => .name
  | .term => .term ℕ 0
  | .wff => .formula
  | .binop => .term (ℕ → ℕ → ℕ) fun _ _ => 0
  | .logbinop => .term (Prop → Prop → Prop) fun _ _ => True
  | .binpred => .term (ℕ → ℕ → Prop) fun _ _ => True
  | .quant => .term ((ℕ → Prop) → Prop) fun _ => True
  | _ => .term PUnit PUnit.unit

variable (N : Type) [DecidableEq N]

/-- The standard environment model of `peano.mm` with names `N`. -/
abbrev envModel : EnvModel grammar ℕ N where
  kind := kind
  op {s} o a := match s, o, a with
    | _, ⟨.binopPlus, rfl⟩, _ => Term.const (· + ·)
    | _, ⟨.binopTimes, rfl⟩, _ => Term.const (· * ·)
    | _, ⟨.tvar, rfl⟩, a => Term.name (a ⟨0, by decide⟩) id
    | _, ⟨.tzero, rfl⟩, _ => Term.const 0
    | _, ⟨.tsucc, rfl⟩, a => (a ⟨0, by decide⟩).map Nat.succ
    | _, ⟨.tbinop, rfl⟩, a =>
      app₂ (a ⟨2, by decide⟩) (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.logbinopOr, rfl⟩, _ => Term.const Or
    | _, ⟨.logbinopAnd, rfl⟩, _ => Term.const And
    | _, ⟨.logbinopImplies, rfl⟩, _ => Term.const fun p q => p → q
    | _, ⟨.logbinopIff, rfl⟩, _ => Term.const Iff
    | _, ⟨.binpredEquals, rfl⟩, _ => Term.const (· = ·)
    | _, ⟨.binpredLessThan, rfl⟩, _ => Term.const (· < ·)
    | _, ⟨.quantAll, rfl⟩, _ => Term.const fun P => ∀ n, P n
    | _, ⟨.quantEx, rfl⟩, _ => Term.const fun P => ∃ n, P n
    | _, ⟨.wffAtom, rfl⟩, a =>
      app₂ (a ⟨2, by decide⟩) (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wffNot, rfl⟩, a => (a ⟨0, by decide⟩).map Not
    | _, ⟨.wffLogbinop, rfl⟩, a =>
      app₂ (a ⟨0, by decide⟩) (a ⟨2, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wffQuant, rfl⟩, a =>
      opQuant (a ⟨1, by decide⟩) (a ⟨0, by decide⟩) (a ⟨2, by decide⟩)
  fresh_op {s t} a o args h := by
    obtain ⟨l, rfl⟩ := o
    refine Kind.fresh_of_ignores (by cases l <;> rfl) fun x hx => ?_
    have hj := fun j => (h j).of_name hx
    cases l with
    | tvar => exact Term.notFree_name ((hj ⟨0, by decide⟩).1 _ rfl)
    | tsucc => exact Term.notFree_map (hj ⟨0, by decide⟩).2
    | tbinop =>
      exact notFree_app₂ (hj ⟨2, by decide⟩).2 (hj ⟨0, by decide⟩).2
        (hj ⟨1, by decide⟩).2
    | wffAtom =>
      exact notFree_app₂ (hj ⟨2, by decide⟩).2 (hj ⟨0, by decide⟩).2
        (hj ⟨1, by decide⟩).2
    | wffNot => exact Term.notFree_map (hj ⟨0, by decide⟩).2
    | wffLogbinop =>
      exact notFree_app₂ (hj ⟨0, by decide⟩).2 (hj ⟨2, by decide⟩).2
        (hj ⟨1, by decide⟩).2
    | wffQuant =>
      exact notFree_opQuant ((hj ⟨0, by decide⟩).1 _ rfl) (hj ⟨1, by decide⟩).2
        (hj ⟨2, by decide⟩).2
    | _ => exact notFree_const _ _
  IsTrue {_ s} _ a := match s, a with
    | .wff, (φ : Term ℕ N Prop) => Valid φ.1
    | _, _ => False

variable [Infinite N]

/-- The standard model of `peano.mm`. -/
abbrev stdModel : Model grammar := (envModel N).toModel

/-! ## Computing values -/

section Values

variable {N} {ctx : V → C → Prop} (ρ : (stdModel N).Valuation ctx)

/-- The sorting context of values. -/
local notation "HS" t:max s:max => grammar.HasSort (grammar.synCtx ctx) t s

theorem value_tvar {a : Tree L V} (h : HS (.node .tvar [a]) .term) :
    (stdModel N).value ρ _ h =
      Term.name ((stdModel N).value ρ a (show HS a .var from h.child ⟨0, by decide⟩)) id := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_tzero (h : HS (.node .tzero []) .term) :
    (stdModel N).value ρ _ h = Term.const 0 := by
  unfold Model.value; rw [eval_node]

theorem value_tsucc {a : Tree L V} (h : HS (.node .tsucc [a]) .term) :
    (stdModel N).value ρ _ h =
      ((stdModel N).value ρ a (show HS a .term from h.child ⟨0, by decide⟩) :
        Term ℕ N ℕ).map Nat.succ := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_tbinop {a b c : Tree L V} (h : HS (.node .tbinop [a, b, c]) .term) :
    (stdModel N).value ρ _ h =
      app₂ ((stdModel N).value ρ c (show HS c .binop from h.child ⟨2, by decide⟩))
      ((stdModel N).value ρ a (show HS a .term from h.child ⟨0, by decide⟩))
      ((stdModel N).value ρ b (show HS b .term from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_binopPlus (h : HS (.node .binopPlus []) .binop) :
    (stdModel N).value ρ _ h = Term.const (· + ·) := by
  unfold Model.value; rw [eval_node]

theorem value_binopTimes (h : HS (.node .binopTimes []) .binop) :
    (stdModel N).value ρ _ h = Term.const (· * ·) := by
  unfold Model.value; rw [eval_node]

theorem value_wffAtom {a b c : Tree L V} (h : HS (.node .wffAtom [a, b, c]) .wff) :
    (stdModel N).value ρ _ h =
      app₂ ((stdModel N).value ρ c (show HS c .binpred from h.child ⟨2, by decide⟩))
      ((stdModel N).value ρ a (show HS a .term from h.child ⟨0, by decide⟩))
      ((stdModel N).value ρ b (show HS b .term from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_binpredEquals (h : HS (.node .binpredEquals []) .binpred) :
    (stdModel N).value ρ _ h = Term.const (· = ·) := by
  unfold Model.value; rw [eval_node]

theorem value_binpredLessThan (h : HS (.node .binpredLessThan []) .binpred) :
    (stdModel N).value ρ _ h = Term.const (· < ·) := by
  unfold Model.value; rw [eval_node]

theorem value_wffNot {a : Tree L V} (h : HS (.node .wffNot [a]) .wff) :
    (stdModel N).value ρ _ h =
      ((stdModel N).value ρ a (show HS a .wff from h.child ⟨0, by decide⟩) :
        Term ℕ N Prop).map Not := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wffLogbinop {a b c : Tree L V} (h : HS (.node .wffLogbinop [a, b, c]) .wff) :
    (stdModel N).value ρ _ h =
      app₂ ((stdModel N).value ρ a (show HS a .logbinop from h.child ⟨0, by decide⟩))
      ((stdModel N).value ρ c (show HS c .wff from h.child ⟨2, by decide⟩))
      ((stdModel N).value ρ b (show HS b .wff from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_logbinopOr (h : HS (.node .logbinopOr []) .logbinop) :
    (stdModel N).value ρ _ h = Term.const Or := by
  unfold Model.value; rw [eval_node]

theorem value_logbinopAnd (h : HS (.node .logbinopAnd []) .logbinop) :
    (stdModel N).value ρ _ h = Term.const And := by
  unfold Model.value; rw [eval_node]

theorem value_logbinopImplies (h : HS (.node .logbinopImplies []) .logbinop) :
    (stdModel N).value ρ _ h = Term.const fun p q => p → q := by
  unfold Model.value; rw [eval_node]

theorem value_logbinopIff (h : HS (.node .logbinopIff []) .logbinop) :
    (stdModel N).value ρ _ h = Term.const Iff := by
  unfold Model.value; rw [eval_node]

theorem value_wffQuant {a b c : Tree L V} (h : HS (.node .wffQuant [a, b, c]) .wff) :
    (stdModel N).value ρ _ h =
      opQuant ((stdModel N).value ρ b (show HS b .quant from h.child ⟨1, by decide⟩))
      ((stdModel N).value ρ a (show HS a .var from h.child ⟨0, by decide⟩))
      ((stdModel N).value ρ c (show HS c .wff from h.child ⟨2, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_quantAll (h : HS (.node .quantAll []) .quant) :
    (stdModel N).value ρ _ h = Term.const fun P => ∀ n, P n := by
  unfold Model.value; rw [eval_node]

theorem value_quantEx (h : HS (.node .quantEx []) .quant) :
    (stdModel N).value ρ _ h = Term.const fun P => ∃ n, P n := by
  unfold Model.value; rw [eval_node]

end Values

theorem holds_iff {ctx : V → C → Prop} (ρ : (stdModel N).Valuation ctx) (t : Tree L V) :
    (stdModel N).Holds ρ (T.pf t) ↔ ∃ h : grammar.HasSort (grammar.synCtx ctx) t .wff,
      Valid ((stdModel N).value ρ t h : Term ℕ N Prop).1 := by
  constructor
  · rintro ⟨s, hs, ht, htrue⟩
    obtain rfl : .wff = s := Option.some.inj hs
    exact ⟨ht, htrue⟩
  · rintro ⟨ht, htrue⟩
    exact ⟨.wff, rfl, ht, htrue⟩

/-- A well-formed assertion at `|-` holds when the value of its conclusion is
valid under every valuation satisfying its hypotheses. -/
theorem satisfies_of_valid {A : TAssertion L C V} {t : Tree L V} (hA : A.WellFormed grammar)
    (hc : A.concl = T.pf t)
    (h : ∀ ρ : (stdModel N).Valuation A.ctx, (stdModel N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (stdModel N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
        Valid ((stdModel N).value ρ t ht : Term ℕ N Prop).1) :
    (stdModel N).Satisfies A := by
  intro ρ hdv hess
  obtain ⟨s, hs, ht⟩ := hA.concl_wellTyped
  rw [hc] at hs ht ⊢
  obtain rfl : .wff = s := Option.some.inj hs
  exact (holds_iff N ρ _).2 ⟨ht.synCtx rfl, h ρ hdv hess _⟩

end Silmaril.Logic.Metamath.Peano

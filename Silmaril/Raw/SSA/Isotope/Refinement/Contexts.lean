module

public import Silmaril.Raw.SSA.Isotope.Refinement.Quantities
public import Silmaril.SSA.Isotope.Types.Thms
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Quantitative contexts of the written refinement calculus

The context lists in `complete-refinement-ssa.tex`, §Variable Quantities, are
represented newest first by finite indices.  All variables are bound indices;
a context therefore represents the paper's free variables without choosing
names.  Zero usage is not the least quantity and must not be treated as one.
-/

namespace Silmaril.Isotope.Refinement

universe u

/-- The permitted uses of a value of a type.  They are always nonzero. -/
class HasQuantity (τ : Type u) where
  quantity : τ → Quantity

export HasQuantity (quantity)

/-- Linearity of the type formers, as specified in the paper. -/
class TypeQuantity (τ : Type u) [TypeFormers τ] extends HasQuantity τ where
  product_quantity (A B : τ) : quantity (product A B) = quantity A ⊓ quantity B
  coproduct_quantity (A B : τ) : quantity (coprod A B) = quantity A ⊓ quantity B
  unit_quantity : quantity (unit : τ) = ⊤
  empty_quantity : quantity (empty : τ) = ⊤

/-- A finite context of types annotated by extended usage quantities. -/
abbrev QCtx (τ : Type u) (n : Nat) := Fin n → τ × Usage

namespace QCtx

variable {τ : Type u} {n m : Nat}

def nil : QCtx τ 0 := Fin.elim0

def snoc (Γ : QCtx τ n) (A : τ) (q : Usage := .used ⊤) : QCtx τ (n + 1) :=
  Fin.cases (A, q) Γ

@[simp] theorem snoc_zero (Γ : QCtx τ n) (A : τ) (q : Usage) :
    snoc Γ A q 0 = (A, q) := rfl

@[simp] theorem snoc_succ (Γ : QCtx τ n) (A : τ) (q : Usage) (i : Fin n) :
    snoc Γ A q i.succ = Γ i := rfl

variable [HasQuantity τ]

/-- Usage after accounting for the type's own linearity. -/
def effective (Γ : QCtx τ n) (i : Fin n) : Usage :=
  Usage.effective (Γ i).2 (quantity (Γ i).1)

/-- Context linearity ignores zero-usage variables, exactly as in the paper. -/
def linearity (Γ : QCtx τ n) : Quantity :=
  Finset.univ.inf (fun i => Usage.linearity (Γ i).2 (quantity (Γ i).1))

@[simp] theorem le_linearity_iff {q : Quantity} {Γ : QCtx τ n} :
    q ≤ linearity Γ ↔ ∀ i, q ≤ Usage.linearity (Γ i).2 (quantity (Γ i).1) := by
  simp [linearity]

@[simp] theorem linearity_nil : linearity (nil : QCtx τ 0) = ⊤ := by
  simp [linearity]

/-- All variables in a context may be discarded. -/
def Discardable (Γ : QCtx τ n) : Prop := ∀ i, Usage.zero ≤ effective Γ i

/-- Weakening to a singleton variable.  The selected slot is used once and
all other slots are discarded.  This is the finite-index form of the paper's
`Γ ⊢ x : A¹` premise. -/
def VarAllowed (Γ : QCtx τ n) (i : Fin n) : Prop :=
  Usage.effective (.used .linear) (quantity (Γ i).1) ≤ effective Γ i ∧
    ∀ j, j ≠ i → Usage.zero ≤ effective Γ j

/-- Native ordered context weakening, including the variable-index map.
`cons` preserves a variable and may restrict its permitted uses; `skip`
requires actual discardability. -/
inductive Weakening : {n m : Nat} → QCtx τ n → QCtx τ m → (Fin m → Fin n) → Prop
  | nil : Weakening nil nil Fin.elim0
  | cons {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
      {A : τ} {q q' : Usage} (h : Weakening Γ Δ ρ)
      (hq : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A)) :
      Weakening (Γ.snoc A q) (Δ.snoc A q') (Fin.cases 0 (fun i => (ρ i).succ))
  | skip {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
      {A : τ} {q : Usage} (h : Weakening Γ Δ ρ)
      (hq : Usage.zero ≤ Usage.effective q (quantity A)) :
      Weakening (Γ.snoc A q) Δ (fun i => (ρ i).succ)

/-- The three permitted ways to apportion one variable. -/
inductive SlotSplit (A : τ) : Usage → Usage → Usage → Prop
  | left (q : Usage) : SlotSplit A q q .zero
  | right (q : Usage) : SlotSplit A q .zero q
  | both (q : Usage) (h : (.used .relevant : Usage) ≤ Usage.effective q (quantity A)) :
      SlotSplit A q q q

theorem SlotSplit.symm {A : τ} {q ql qr : Usage} (h : SlotSplit A q ql qr) :
    SlotSplit A q qr ql := by
  cases h with
  | left => exact .right _
  | right => exact .left _
  | both hq => exact .both _ hq

/-- Context splitting retains the same types on both sides. -/
def Split (Γ Γl Γr : QCtx τ n) : Prop :=
  ∀ i, (Γl i).1 = (Γ i).1 ∧ (Γr i).1 = (Γ i).1 ∧
    SlotSplit (Γ i).1 (Γ i).2 (Γl i).2 (Γr i).2

namespace Split

theorem nil : Split (QCtx.nil : QCtx τ 0) QCtx.nil QCtx.nil := fun i => Fin.elim0 i

theorem snoc {Γ Γl Γr : QCtx τ n} (h : Split Γ Γl Γr) {A : τ}
    {q ql qr : Usage} (hq : SlotSplit A q ql qr) :
    Split (Γ.snoc A q) (Γl.snoc A ql) (Γr.snoc A qr) := by
  intro i
  exact Fin.cases ⟨rfl, rfl, hq⟩ (fun j => h j) i

theorem symm {Γ Γl Γr : QCtx τ n} (h : Split Γ Γl Γr) : Split Γ Γr Γl := by
  intro i
  obtain ⟨hl, hr, hs⟩ := h i
  exact ⟨hr, hl, hs.symm⟩

end Split
end QCtx
end Silmaril.Isotope.Refinement

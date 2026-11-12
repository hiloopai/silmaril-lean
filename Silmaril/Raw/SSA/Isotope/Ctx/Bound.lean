module

public import Silmaril.Raw.SSA.Isotope.Ctx
public import Mathlib.Data.Fin.Basic

@[expose] public section

universe u

namespace Silmaril.Isotope

/-- Bound contexts are the anonymous-only specialization of shared snoc
contexts, indexed by their length. -/
inductive BoundCtx (τ : Type u) : Nat → Type u where
  | nil : BoundCtx τ 0
  | snoc {n : Nat} : BoundCtx τ n → τ → BoundCtx τ (n + 1)

namespace BoundCtx

variable {τ : Type u} {n m k : Nat}

/-- The corresponding shared context. Every slot is anonymous. -/
def toCtx {n : Nat} : BoundCtx τ n → Isotope.Ctx Empty τ
  | .nil => .nil
  | .snoc Γ A => .snoc Γ.toCtx none A

@[simp] theorem length_toCtx (Γ : BoundCtx τ n) : Γ.toCtx.length = n := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp [toCtx, Ctx.length, ih]

/-- Index zero is the newest snoc slot; successors walk toward older slots. -/
def get {n : Nat} : BoundCtx τ n → Fin n → τ
  | .snoc Γ A, ι => Fin.cases A Γ.get ι

/-- Reconstruct a snoc context from its newest-first `Fin` view. -/
def ofFin : {n : Nat} → (Fin n → τ) → BoundCtx τ n
  | 0, _ => .nil
  | _n + 1, f => .snoc (ofFin (fun ι => f ι.succ)) (f 0)

@[simp] theorem get_ofFin : ∀ {n : Nat} (f : Fin n → τ), (ofFin f).get = f
  | 0, f => funext fun ι => Fin.elim0 ι
  | n + 1, f => by
      funext ι
      refine Fin.cases rfl (fun j => ?_) ι
      exact congrFun (get_ofFin (fun k : Fin n => f k.succ)) j

@[simp] theorem ofFin_get (Γ : BoundCtx τ n) : ofFin Γ.get = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp [ofFin, get, ih]

/-- Precise equivalence between anonymous snoc contexts and newest-first
finite-index lookup functions. -/
def finEquiv (τ : Type u) (n : Nat) : BoundCtx τ n ≃ (Fin n → τ) where
  toFun := get
  invFun := ofFin
  left_inv := ofFin_get
  right_inv := get_ofFin

/-- Types in newest-first order, matching de Bruijn value contexts. -/
def toList {n : Nat} : BoundCtx τ n → List τ
  | .nil => []
  | .snoc Γ A => A :: Γ.toList

@[simp] theorem length_toList (Γ : BoundCtx τ n) : Γ.toList.length = n := by
  induction Γ with
  | nil => rfl
  | snoc Γ A ih => simp [toList, ih]

@[simp] theorem getElem?_toList (Γ : BoundCtx τ n) (i : Fin n) :
    Γ.toList[i.val]? = some (Γ.get i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | snoc Γ A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa [toList, get] using ih j

/-- A bound-variable map preserving the type at every selected slot. -/
def Ren (Γ : BoundCtx τ n) (Δ : BoundCtx τ m) (ρ : Fin n → Fin m) : Prop :=
  ∀ i, Δ.get (ρ i) = Γ.get i

namespace Ren

theorem id (Γ : BoundCtx τ n) : Ren Γ Γ id := fun _ => rfl

theorem comp {Γ : BoundCtx τ n} {Δ : BoundCtx τ m} {Θ : BoundCtx τ k}
    {ρ : Fin n → Fin m} {σ : Fin m → Fin k} (hρ : Ren Γ Δ ρ) (hσ : Ren Δ Θ σ) :
    Ren Γ Θ (σ ∘ ρ) := fun i => (hσ (ρ i)).trans (hρ i)

/-- Extend a renaming with a common newest binder. -/
theorem up {Γ : BoundCtx τ n} {Δ : BoundCtx τ m} {ρ : Fin n → Fin m}
    (hρ : Ren Γ Δ ρ) (A : τ) :
    Ren (.snoc Γ A) (.snoc Δ A) (Fin.cases 0 (fun i => (ρ i).succ)) :=
  Fin.cases rfl (fun i => hρ i)

/-- Weaken by inserting a newest bound variable. -/
theorem succ (Γ : BoundCtx τ n) (A : τ) : Ren Γ (.snoc Γ A) Fin.succ := fun _ => rfl

end Ren

/-- A type-preserving index map packaged with its preservation proof. -/
structure Renaming (Γ : BoundCtx τ n) (Δ : BoundCtx τ m) where
  toFun : Fin n → Fin m
  typed : Ren Γ Δ toFun

namespace Renaming

def id (Γ : BoundCtx τ n) : Renaming Γ Γ := ⟨fun i => i, Ren.id Γ⟩

def comp {Γ : BoundCtx τ n} {Δ : BoundCtx τ m} {Θ : BoundCtx τ k}
    (ρ : Renaming Γ Δ) (σ : Renaming Δ Θ) : Renaming Γ Θ :=
  ⟨σ.toFun ∘ ρ.toFun, ρ.typed.comp σ.typed⟩

def up {Γ : BoundCtx τ n} {Δ : BoundCtx τ m} (ρ : Renaming Γ Δ) (A : τ) :
    Renaming (.snoc Γ A) (.snoc Δ A) :=
  ⟨Fin.cases 0 (fun i => (ρ.toFun i).succ), ρ.typed.up A⟩

def succ (Γ : BoundCtx τ n) (A : τ) : Renaming Γ (.snoc Γ A) :=
  ⟨Fin.succ, Ren.succ Γ A⟩

def underBinder (Γ : BoundCtx τ n) (X Y : τ) :
    Renaming (.snoc Γ Y) (.snoc (.snoc Γ X) Y) := (succ Γ X).up Y

def underTwoBinders (Γ : BoundCtx τ n) (X Y Z : τ) :
    Renaming (.snoc (.snoc Γ Y) Z) (.snoc (.snoc (.snoc Γ X) Y) Z) where
  toFun := Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))
  typed := Fin.cases rfl (Fin.cases rfl (fun _ => rfl))

end Renaming

end BoundCtx
end Silmaril.Isotope

module

public import Silmaril.SSA.Isotope.Types.Defs
public import Silmaril.SSA.Isotope.Types.Thms
public import Silmaril.Raw.SSA.Isotope.Ctx.Bound

/-!
# Type and instruction interpretations

Semantic capabilities follow the independent type formers. Sequential terms
need only products and unit. Instruction interpretation does not impose an
effect annotation; purity compatibility is an additional property.
-/

@[expose] public section

universe u v w q

namespace Silmaril

/-- Interpret free type syntax over an arbitrary interpretation of its atoms. -/
def Ty.denote {α : Type u} (F : α → Type v) : Ty α → Type v
  | .base a => F a
  | .product A B => denote F A × denote F B
  | .unit => PUnit
  | .coprod A B => Sum (denote F A) (denote F B)
  | .empty => PEmpty

namespace Isotope.Semantics

variable {τ : Type u}

class ProductModel (D : τ → Type v) [HasProduct τ] where
  productEquiv (A B : τ) : D (product A B) ≃ D A × D B

class UnitModel (D : τ → Type v) [HasUnit τ] where
  unitEquiv : D (unit : τ) ≃ PUnit

class CoproductModel (D : τ → Type v) [HasCoproduct τ] where
  coprodEquiv (A B : τ) : D (coprod A B) ≃ Sum (D A) (D B)

class EmptyModel (D : τ → Type v) [HasEmpty τ] where
  emptyEquiv : D (empty : τ) ≃ PEmpty

instance {α : Type u} (F : α → Type v) : ProductModel (Ty.denote F) where
  productEquiv _ _ := Equiv.refl _

instance {α : Type u} (F : α → Type v) : UnitModel (Ty.denote F) where
  unitEquiv := Equiv.refl _

instance {α : Type u} (F : α → Type v) : CoproductModel (Ty.denote F) where
  coprodEquiv _ _ := Equiv.refl _

instance {α : Type u} (F : α → Type v) : EmptyModel (Ty.denote F) where
  emptyEquiv := Equiv.refl _

/-- Typed primitive evaluation, independent of the effect signature. -/
structure InstructionModel (D : τ → Type v) (Φ : Type q) (m : Type v → Type v)
    [HasTy Φ τ] where
  eval (f : Φ) : D (instrSrc f) → m (D (instrTrg f))

/-- Pure implementations induce a model in any monad. -/
def InstructionModel.ofPure (D : τ → Type v) (Φ : Type q) (m : Type v → Type v)
    [HasTy Φ τ] [Pure m] (eval : (f : Φ) → D (instrSrc f) → D (instrTrg f)) :
    InstructionModel D Φ m := ⟨fun f x => pure (eval f x)⟩

/-- Compatibility with a separately chosen bottom-effect judgment. -/
def InstructionModel.RespectsPure {D : τ → Type v} {Φ : Type q} {m : Type v → Type v}
    [HasTy Φ τ] [Pure m] (M : InstructionModel D Φ m) {ε : Type w}
    [HasEff Φ ε] [Bot ε] : Prop :=
  ∀ f, (instrEff f : ε) = ⊥ → ∃ g : D (instrSrc f) → D (instrTrg f),
    ∀ x, M.eval f x = pure (g x)

/-- Values assigned to visible free names; shadowed slots cannot be observed. -/
abbrev FreeEnv (D : τ → Type v) {ν : Type w} [DecidableEq ν] (Γ : Ctx ν τ) :=
  ∀ (x : ν) (A : τ), Γ.lookup x = some A → D A

/-- Environments for bound variables, in the context's newest-first order. -/
abbrev BoundEnv (D : τ → Type v) {n : Nat} (β : BoundCtx τ n) :=
  (i : Fin n) → D (β.get i)

def BoundEnv.snoc {D : τ → Type v} {n : Nat} {β : BoundCtx τ n} {A : τ}
    (ρ : BoundEnv D β) (a : D A) : BoundEnv D (.snoc β A) := Fin.cases a ρ

@[simp] theorem BoundEnv.snoc_zero {D : τ → Type v} {n : Nat}
    {β : BoundCtx τ n} {A : τ} (ρ : BoundEnv D β) (a : D A) :
    snoc ρ a 0 = a := rfl

@[simp] theorem BoundEnv.snoc_succ {D : τ → Type v} {n : Nat}
    {β : BoundCtx τ n} {A : τ} (ρ : BoundEnv D β) (a : D A) (i : Fin n) :
    snoc ρ a i.succ = ρ i := rfl

end Isotope.Semantics
end Silmaril

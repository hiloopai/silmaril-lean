module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fin.Basic

/-!
# Module contexts visible to a Wasm function, and their embeddings

The signatures of the function-level institutions (`Silmaril.Wasm.FnInst.Core`) are built on a
**module context**: for each kind of module-level entity (types, functions, tables, memories,
globals, tags, data and element segments) a number of entries and a declaration for each.
Functions count imported and defined functions alike (Wasm's single function index space),
public and private alike; the declaration of a function records its type and whether it is
imported.

An **embedding** `C ⟶ C'` renumbers each index space injectively and keeps declarations (an
imported function may become a defined one, which is what linking or `wasm-merge` does).
Embeddings form a category with the empty context `Ctx.empty` as initial object
(`Ctx.ofEmpty`, unique by `Ctx.Hom.ext`).

Indices are `Fin (C.n k)`, so contexts live in `Type` and every institution built on them is an
`Institution₀`.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst

open CategoryTheory

/-- The kinds of module-level entities a function body can refer to. -/
inductive Kind where
  | type | func | table | mem | global | tag | data | elem
  deriving DecidableEq, Repr

/-- Wasm value types. -/
inductive ValTy where
  | i32 | i64 | f32 | f64 | v128 | funcref | externref
  deriving DecidableEq, Repr

/-- A function type `params → results`. -/
structure FnTy where
  params : List ValTy
  results : List ValTy
  deriving DecidableEq, Repr

/-- The declaration of a function: its type, and whether it is imported. -/
structure FuncDecl where
  ty : FnTy
  imported : Bool
  deriving DecidableEq, Repr

/-- The declaration of an entity of each kind. Tables record their element type and minimum
size, memories their minimum size in pages, globals their type and mutability, data segments
their length, element segments their reference type. -/
def Decl : Kind → Type
  | .type => FnTy
  | .func => FuncDecl
  | .table => ValTy × ℕ
  | .mem => ℕ
  | .global => ValTy × Bool
  | .tag => FnTy
  | .data => ℕ
  | .elem => ValTy

/-- How a declaration may change along an embedding: functions keep their type and may go from
imported to defined; every other declaration is kept. -/
def Decl.Emb : (k : Kind) → Decl k → Decl k → Prop
  | .func, d, d' => d.ty = d'.ty ∧ (d'.imported = true → d.imported = true)
  | .type, d, d' => d = d'
  | .table, d, d' => d = d'
  | .mem, d, d' => d = d'
  | .global, d, d' => d = d'
  | .tag, d, d' => d = d'
  | .data, d, d' => d = d'
  | .elem, d, d' => d = d'

theorem Decl.Emb.refl : ∀ (k : Kind) (d : Decl k), Decl.Emb k d d
  | .func, _ => ⟨rfl, id⟩
  | .type, _ => rfl
  | .table, _ => rfl
  | .mem, _ => rfl
  | .global, _ => rfl
  | .tag, _ => rfl
  | .data, _ => rfl
  | .elem, _ => rfl

theorem Decl.Emb.trans : ∀ (k : Kind) {d₁ d₂ d₃ : Decl k},
    Decl.Emb k d₁ d₂ → Decl.Emb k d₂ d₃ → Decl.Emb k d₁ d₃
  | .func, _, _, _, h₁, h₂ => ⟨h₁.1.trans h₂.1, fun h => h₁.2 (h₂.2 h)⟩
  | .type, _, _, _, h₁, h₂ => Eq.trans h₁ h₂
  | .table, _, _, _, h₁, h₂ => Eq.trans h₁ h₂
  | .mem, _, _, _, h₁, h₂ => Eq.trans h₁ h₂
  | .global, _, _, _, h₁, h₂ => Eq.trans h₁ h₂
  | .tag, _, _, _, h₁, h₂ => Eq.trans h₁ h₂
  | .data, _, _, _, h₁, h₂ => Eq.trans h₁ h₂
  | .elem, _, _, _, h₁, h₂ => Eq.trans h₁ h₂

/-- A module context: the number of entities of each kind and their declarations. -/
structure Ctx where
  /-- Number of entities of each kind (indices are `Fin (n k)`). -/
  n : Kind → ℕ
  /-- The declaration of each entity. -/
  decl : ∀ k, Fin (n k) → Decl k

namespace Ctx

/-- Indices of kind `k`. -/
abbrev Idx (C : Ctx) (k : Kind) : Type := Fin (C.n k)

/-- The type of function `f`. -/
abbrev fty (C : Ctx) (f : C.Idx .func) : FnTy := (C.decl .func f).ty

/-- An embedding of module contexts: injective renumbering of every index space that keeps
declarations (up to `Decl.Emb`). -/
structure Hom (C C' : Ctx) where
  /-- The renumbering. -/
  map : ∀ k, C.Idx k → C'.Idx k
  /-- Renumbering is injective. -/
  inj : ∀ k, Function.Injective (map k)
  /-- Declarations are kept. -/
  decl : ∀ k i, Decl.Emb k (C.decl k i) (C'.decl k (map k i))

@[ext] theorem Hom.ext {C C' : Ctx} {σ τ : Hom C C'} (h : σ.map = τ.map) : σ = τ := by
  cases σ; cases τ; cases h; rfl

instance : Category Ctx where
  Hom := Hom
  id C := ⟨fun _ => id, fun _ => Function.injective_id, fun k i => Decl.Emb.refl k _⟩
  comp σ τ := ⟨fun k => τ.map k ∘ σ.map k, fun k => (τ.inj k).comp (σ.inj k),
    fun k i => Decl.Emb.trans k (σ.decl k i) (τ.decl k _)⟩

@[simp] theorem id_map (C : Ctx) (k : Kind) (i : C.Idx k) : (𝟙 C : Hom C C).map k i = i := rfl

@[simp] theorem comp_map {C C' C'' : Ctx} (σ : C ⟶ C') (τ : C' ⟶ C'') (k : Kind) (i : C.Idx k) :
    (σ ≫ τ : Hom C C'').map k i = (τ : Hom C' C'').map k ((σ : Hom C C').map k i) := rfl

/-- Embeddings keep function types. -/
theorem Hom.fty {C C' : Ctx} (σ : C ⟶ C') (f : C.Idx .func) :
    C'.fty ((σ : Hom C C').map .func f) = C.fty f :=
  ((σ : Hom C C').decl .func f).1.symm

/-- The empty context: no types, functions, tables, memories, globals, tags or segments. -/
def empty : Ctx := ⟨fun _ => 0, fun _ i => i.elim0⟩

/-- The unique embedding of the empty context. -/
def ofEmpty (C : Ctx) : empty ⟶ C :=
  (⟨fun _ i => i.elim0, fun _ i => i.elim0, fun _ i => i.elim0⟩ : Hom empty C)

instance (C : Ctx) : Subsingleton (empty ⟶ C) :=
  ⟨fun _ _ => Hom.ext (funext fun _ => funext fun i => i.elim0)⟩

end Ctx

end Silmaril.Wasm.FnInst

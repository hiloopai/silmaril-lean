module

public import Silmaril.Wasm.Unified.Syntax.Defs
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Feature signatures

A **feature signature** is a set of opcodes of the universal syntax, each with a syntactic
type (`OpTy`: how many immediates, how many nested blocks, whether it carries a handler table).
Stack typing is not part of a signature; it is the *validation* half of a model
(`Silmaril.Wasm.Unified.Model`).

* `FSig`: opcodes `ops : Set Opcode` and typing `ty : Opcode → OpTy` (read on `ops`).
  `FSig.Op S` is the subtype of its opcodes and `FSig.Code S = UCode S.Op` its syntax.
* `FSig.Hom S S'`: a **renaming** of opcodes `S.Op → S'.Op` that preserves typing. Signatures
  and renamings form a category (`FSig.category`).
* `FSig.Sub S S'`: inclusion of feature sets with equal typing (Lime below 3.0, 3.0 below FX).
  `FSig.incl` is the inclusion morphism; inclusions compose (`incl_comp`) and are the unique
  morphisms acting as the identity on opcodes (`incl_unique`), so the inclusion order is a
  thin subcategory.
* `FSig.toUniv`: a signature's code as universal code (`UInstr.mapCode Subtype.val`).
-/

@[expose] public section

namespace Silmaril.Wasm.Unified

open CategoryTheory

/-- The syntactic type of an opcode: numbers of immediates and of nested blocks, and whether it
carries a handler table. -/
structure OpTy where
  /-- Number of immediates. -/
  imms : Nat
  /-- Number of nested blocks. -/
  blocks : Nat
  /-- Whether the opcode carries a handler table. -/
  handlers : Bool
  deriving DecidableEq, Repr, Inhabited

/-- A **feature signature**: a set of opcodes with their syntactic types. -/
structure FSig where
  /-- The opcodes of the signature. -/
  ops : Set Opcode
  /-- Their syntactic types (only read on `ops`). -/
  ty : Opcode → OpTy

namespace FSig

/-- The opcodes of a signature, as a type. -/
abbrev Op (S : FSig) : Type := {o : Opcode // o ∈ S.ops}

/-- The syntax of a signature: instruction sequences over its opcodes. -/
abbrev Code (S : FSig) : Type := UCode S.Op

/-- **Signature morphisms**: renamings of opcodes that preserve their syntactic types. -/
@[ext] structure Hom (S S' : FSig) where
  /-- The opcode renaming. -/
  f : S.Op → S'.Op
  /-- Typing is preserved. -/
  ty : ∀ o, S'.ty (f o).1 = S.ty o.1

/-- The category of feature signatures and opcode renamings. -/
instance category : Category FSig where
  Hom := Hom
  id _ := ⟨id, fun _ => rfl⟩
  comp σ τ := ⟨τ.f ∘ σ.f, fun o => (τ.ty (σ.f o)).trans (σ.ty o)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_f (S : FSig) : (𝟙 S : S ⟶ S).f = id := rfl

@[simp] theorem comp_f {S S' S'' : FSig} (σ : S ⟶ S') (τ : S' ⟶ S'') :
    (σ ≫ τ).f = τ.f ∘ σ.f := rfl

@[ext] theorem hom_ext {S S' : FSig} {σ τ : S ⟶ S'} (h : σ.f = τ.f) : σ = τ := Hom.ext h

/-- **Inclusion of feature signatures**: more opcodes, the same typing on the smaller set. -/
def Sub (S S' : FSig) : Prop := S.ops ⊆ S'.ops ∧ ∀ o ∈ S.ops, S'.ty o = S.ty o

theorem Sub.refl (S : FSig) : Sub S S := ⟨fun _ h => h, fun _ _ => rfl⟩

theorem Sub.trans {S S' S'' : FSig} (h : Sub S S') (h' : Sub S' S'') : Sub S S'' :=
  ⟨fun _ ho => h'.1 (h.1 ho), fun o ho => (h'.2 o (h.1 ho)).trans (h.2 o ho)⟩

/-- The inclusion morphism. -/
def incl {S S' : FSig} (h : Sub S S') : S ⟶ S' :=
  ⟨fun o => ⟨o.1, h.1 o.2⟩, fun o => h.2 o.1 o.2⟩

@[simp] theorem incl_refl (S : FSig) : incl (Sub.refl S) = 𝟙 S := rfl

theorem incl_comp {S S' S'' : FSig} (h : Sub S S') (h' : Sub S' S'') :
    incl h ≫ incl h' = incl (h.trans h') := rfl

/-- Inclusions are the only morphisms that keep every opcode. -/
theorem incl_unique {S S' : FSig} (h : Sub S S') (σ : S ⟶ S') (hσ : ∀ o, (σ.f o).1 = o.1) :
    σ = incl h :=
  hom_ext (funext fun o => Subtype.ext (hσ o))

/-- A signature's code as universal code. -/
def toUniv (S : FSig) : S.Code → UCode Opcode := UInstr.mapCode Subtype.val

/-- Renaming along an inclusion does not change the universal code. -/
theorem toUniv_incl {S S' : FSig} (h : Sub S S') (c : S.Code) :
    S'.toUniv (UInstr.mapCode (incl h).f c) = S.toUniv c := by
  unfold toUniv
  rw [UInstr.mapCode_map]
  rfl

end FSig

end Silmaril.Wasm.Unified

module

public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSA
public import Silmaril.Raw.SSA.Isotope.SSA.FiniteSum

/-!
# Finite scoped flat regions

These regions contain expression evaluation, branch selection, and jumps to
finite labels. CFG binding is kept in a separate finite graph representation.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA

/-- A region with finitely many ambient labels and scoped positional expressions. -/
inductive Flat (Φ : Type u) (labels : Nat) : Nat → Type u where
  | br {n : Nat} (label : Fin labels) (arg : LetCase.LocallyNameless.Tm Empty Φ n) :
      Flat Φ labels n
  | let₁ {n : Nat} (value : LetCase.LocallyNameless.Tm Empty Φ n)
      (body : Flat Φ labels (n + 1)) : Flat Φ labels n
  | let₂ {n : Nat} (value : LetCase.LocallyNameless.Tm Empty Φ n)
      (body : Flat Φ labels (n + 2)) : Flat Φ labels n
  | case {n : Nat} (discr : LetCase.LocallyNameless.Tm Empty Φ n)
      (left right : Flat Φ labels (n + 1)) : Flat Φ labels n
  deriving Repr

namespace Flat

variable {Φ : Type u} {labels n : Nat}

/-- Forget only the finite index bounds, retaining the existing region syntax. -/
def erase {n : Nat} : Flat Φ labels n → Region Φ
  | .br i a => .br i.val (Morphism.CaseSSA.erase a)
  | .let₁ a b => .let₁ (Morphism.CaseSSA.erase a) (erase b)
  | .let₂ a b => .let₂ (Morphism.CaseSSA.erase a) (erase b)
  | .case e l r => .case (Morphism.CaseSSA.erase e) (erase l) (erase r)

variable {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- Every jump supplies the exact argument type of its selected label. -/
inductive HasType (L : Fin labels → τ) : {n : Nat} → BoundCtx τ n → Flat Φ labels n → Prop where
  | br {n : Nat} {β : BoundCtx τ n} {i : Fin labels}
      {a : LetCase.LocallyNameless.Tm Empty Φ n}
      (ha : LetCase.LocallyNameless.HasType Φ .nil β a (L i)) : HasType L β (.br i a)
  | let₁ {n : Nat} {β : BoundCtx τ n} {a : LetCase.LocallyNameless.Tm Empty Φ n}
      {b : Flat Φ labels (n + 1)} {A : τ}
      (ha : LetCase.LocallyNameless.HasType Φ .nil β a A)
      (hb : HasType L (.snoc β A) b) : HasType L β (.let₁ a b)
  | let₂ {n : Nat} {β : BoundCtx τ n} {a : LetCase.LocallyNameless.Tm Empty Φ n}
      {b : Flat Φ labels (n + 2)} {A B : τ}
      (ha : LetCase.LocallyNameless.HasType Φ .nil β a (Silmaril.product A B))
      (hb : HasType L (.snoc (.snoc β A) B) b) : HasType L β (.let₂ a b)
  | case {n : Nat} {β : BoundCtx τ n} {e : LetCase.LocallyNameless.Tm Empty Φ n}
      {l r : Flat Φ labels (n + 1)} {A B : τ}
      (he : LetCase.LocallyNameless.HasType Φ .nil β e (Silmaril.coprod A B))
      (hl : HasType L (.snoc β A) l) (hr : HasType L (.snoc β B) r) :
      HasType L β (.case e l r)

/-- The scoped presentation preserves the existing region judgment exactly. -/
theorem HasType.erase {L : Fin labels → τ} {β : BoundCtx τ n} {r : Flat Φ labels n}
    (h : HasType L β r) : Region.HasType β.toList r.erase (List.ofFn L) := by
  induction h with
  | br ha => exact .br (SSA.FiniteSum.at_ofFn _ _) (Morphism.CaseSSA.erase_hasType ha)
  | let₁ ha _ ih => exact .let₁ (Morphism.CaseSSA.erase_hasType ha) ih
  | let₂ ha _ ih => exact .let₂ (Morphism.CaseSSA.erase_hasType ha) ih
  | case he _ _ ihl ihr => exact .case (Morphism.CaseSSA.erase_hasType he) ihl ihr

/-- Existing exact region typing reflects through the finite scoped presentation. -/
theorem hasType_of_erase {L : Fin labels → τ} {β : BoundCtx τ n} {r : Flat Φ labels n}
    (h : Region.HasType β.toList r.erase (List.ofFn L)) : HasType L β r := by
  induction r with
  | br i a =>
      cases h with
      | br hi ha =>
          have he := Option.some.inj ((SSA.FiniteSum.at_ofFn L i).symm.trans hi)
          exact .br (he.symm ▸ Morphism.CaseSSA.hasType_of_erase ha)
  | let₁ a b ih => cases h with
      | let₁ ha hb => exact .let₁ (Morphism.CaseSSA.hasType_of_erase ha) (ih hb)
  | let₂ a b ih => cases h with
      | let₂ ha hb => exact .let₂ (Morphism.CaseSSA.hasType_of_erase ha) (ih hb)
  | case e l r ihl ihr => cases h with
      | case he hl hr => exact .case (Morphism.CaseSSA.hasType_of_erase he) (ihl hl) (ihr hr)

theorem erase_hasType_iff {L : Fin labels → τ} {β : BoundCtx τ n} {r : Flat Φ labels n} :
    Region.HasType β.toList r.erase (List.ofFn L) ↔ HasType L β r :=
  ⟨hasType_of_erase, HasType.erase⟩

end Flat

/-- A finite graph: each block receives its own argument above a shared captured
context. Labels enumerate internal blocks first, then external exits. -/
structure FiniteCFG (Φ : Type u) (blocks exits captured : Nat) where
  entry : Flat Φ (blocks + exits) captured
  block : Fin blocks → Flat Φ (blocks + exits) (captured + 1)

namespace FiniteCFG

variable {Φ : Type u} {blocks exits captured : Nat}

/-- Embed the finite graph into the existing mutually recursive CFG syntax. -/
def erase (g : FiniteCFG Φ blocks exits captured) : Region Φ :=
  .cfg g.entry.erase blocks (fun i => (g.block i).erase)

/-- Block argument types may vary independently with the block index. -/
structure HasType {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    (β : BoundCtx τ captured) (R : Fin blocks → τ) (E : Fin exits → τ)
    (g : FiniteCFG Φ blocks exits captured) : Prop where
  entry : Flat.HasType (SSA.FiniteSum.append R E) β g.entry
  block : ∀ i, Flat.HasType (SSA.FiniteSum.append R E) (.snoc β (R i)) (g.block i)

/-- The finite graph has the standard CFG judgment with the chosen heterogeneous
block parameters and the corresponding external label list. -/
theorem HasType.erase {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    {β : BoundCtx τ captured} {R : Fin blocks → τ} {E : Fin exits → τ}
    {g : FiniteCFG Φ blocks exits captured} (h : HasType β R E g) :
    Region.HasType β.toList g.erase (List.ofFn E) := by
  apply Region.HasType.cfg R
  · simpa using h.entry.erase
  · intro i
    simpa [BoundCtx.toList] using (h.block i).erase

/-- The existing CFG judgment chooses an internal parameter family. The finite
presentation records exactly that family, without requiring it to be unique. -/
theorem erase_hasType_iff {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    {β : BoundCtx τ captured} {E : Fin exits → τ}
    {g : FiniteCFG Φ blocks exits captured} :
    Region.HasType β.toList g.erase (List.ofFn E) ↔
      ∃ R : Fin blocks → τ, HasType β R E g := by
  constructor
  · intro h
    cases h with
    | cfg R he hb =>
        refine ⟨R, ⟨?_, ?_⟩⟩
        · apply Flat.hasType_of_erase
          simpa using he
        · intro i
          apply Flat.hasType_of_erase
          simpa [BoundCtx.toList] using hb i
  · rintro ⟨R, h⟩
    exact h.erase

end FiniteCFG
end Silmaril.Isotope.LambdaSSA

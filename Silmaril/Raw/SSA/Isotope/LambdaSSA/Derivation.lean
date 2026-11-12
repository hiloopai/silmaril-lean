module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.RegionScope
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSA
public import Silmaril.Raw.SSA.Isotope.SSA.FiniteSum
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Derivation

/-! # Exact typing data for nested SSA regions

Value typing reuses let-case's exact derivations through its lossless scoped
SSA expression correspondence. Region constructors retain their intermediate
types as data, so compilers can recurse without choosing data from a proposition.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ]

inductive Derivation (Φ : Type v) [HasTy Φ τ] :
    {labels n : Nat} → (Fin labels → τ) → BoundCtx τ n → Region Φ → Type (max u v) where
  | br {labels n : Nat} {L : Fin labels → τ} {β : BoundCtx τ n}
      (i : Fin labels) {arg : LambdaSSA.Tm Φ} (h : arg.Scoped n)
      (da : LetCase.LocallyNameless.Derivation Φ .nil β (Morphism.CaseSSA.ofScoped arg h) (L i)) :
      Derivation Φ L β (.br i.val arg)
  | let₁ {labels n : Nat} {L : Fin labels → τ} {β : BoundCtx τ n}
      {arg : LambdaSSA.Tm Φ} {body : Region Φ} {A : τ} (h : arg.Scoped n)
      (da : LetCase.LocallyNameless.Derivation Φ .nil β (Morphism.CaseSSA.ofScoped arg h) A)
      (db : Derivation Φ L (.snoc β A) body) : Derivation Φ L β (.let₁ arg body)
  | let₂ {labels n : Nat} {L : Fin labels → τ} {β : BoundCtx τ n}
      {arg : LambdaSSA.Tm Φ} {body : Region Φ} {A B : τ} (h : arg.Scoped n)
      (da : LetCase.LocallyNameless.Derivation Φ .nil β (Morphism.CaseSSA.ofScoped arg h) (product A B))
      (db : Derivation Φ L (.snoc (.snoc β A) B) body) : Derivation Φ L β (.let₂ arg body)
  | case {labels n : Nat} {L : Fin labels → τ} {β : BoundCtx τ n}
      {arg : LambdaSSA.Tm Φ} {left right : Region Φ} {A B : τ} (h : arg.Scoped n)
      (da : LetCase.LocallyNameless.Derivation Φ .nil β (Morphism.CaseSSA.ofScoped arg h) (coprod A B))
      (dl : Derivation Φ L (.snoc β A) left) (dr : Derivation Φ L (.snoc β B) right) :
      Derivation Φ L β (.case arg left right)
  | cfg {labels n count : Nat} {L : Fin labels → τ} {β : BoundCtx τ n}
      {entry : Region Φ} {blocks : Fin count → Region Φ} (R : Fin count → τ)
      (de : Derivation Φ (SSA.FiniteSum.append R L) β entry)
      (db : ∀ i, Derivation Φ (SSA.FiniteSum.append R L) (.snoc β (R i)) (blocks i)) :
      Derivation Φ L β (.cfg entry count blocks)

namespace Derivation

variable {Φ : Type v} [HasTy Φ τ]

theorem toHasType {labels n : Nat} {L : Fin labels → τ} {β : BoundCtx τ n} {r : Region Φ}
    (d : Derivation Φ L β r) : Region.HasType β.toList r (List.ofFn L) := by
  induction d with
  | br i h arg =>
    exact .br (SSA.FiniteSum.at_ofFn _ i)
      ((Morphism.CaseSSA.ofScoped_hasType_iff h).mp arg.toHasType)
  | let₁ h arg body ih =>
    exact .let₁
      ((Morphism.CaseSSA.ofScoped_hasType_iff h).mp arg.toHasType) ih
  | let₂ h arg body ih =>
    exact .let₂
      ((Morphism.CaseSSA.ofScoped_hasType_iff h).mp arg.toHasType) ih
  | case h arg left right ihl ihr =>
    exact .case
      ((Morphism.CaseSSA.ofScoped_hasType_iff h).mp arg.toHasType) ihl ihr
  | cfg R entry blocks ihe ihb =>
    apply Region.HasType.cfg R
    · simpa only [SSA.FiniteSum.ofFn_append] using ihe
    · intro i
      simpa only [SSA.FiniteSum.ofFn_append, BoundCtx.toList] using ihb i

theorem scope {labels n : Nat} {L : Fin labels → τ} {β : BoundCtx τ n} {r : Region Φ}
    (d : Derivation Φ L β r) : r.Scoped labels n := by
  simpa only [List.length_ofFn, BoundCtx.length_toList] using d.toHasType.scoped

/-- This data presentation covers every exactly typed raw region. Existence
does not pretend to be an executable extraction from a proposition. -/
theorem ofHasType {labels n : Nat} {L : Fin labels → τ} {β : BoundCtx τ n} {r : Region Φ}
    (h : Region.HasType β.toList r (List.ofFn L)) : Nonempty (Derivation Φ L β r) := by
  classical
  have hs : r.Scoped labels n := by
    simpa only [List.length_ofFn, BoundCtx.length_toList] using h.scoped
  induction r generalizing labels n with
  | br label arg =>
    cases h with
    | br hl ha =>
      have eq := Option.some.inj ((SSA.FiniteSum.at_ofFn L ⟨label, hs.1⟩).symm.trans hl)
      obtain ⟨da⟩ := LetCase.LocallyNameless.Derivation.ofHasType
        ((Morphism.CaseSSA.ofScoped_hasType_iff hs.2).mpr (eq.symm ▸ ha))
      exact ⟨.br ⟨label, hs.1⟩ hs.2 da⟩
  | let₁ arg body ih =>
    cases h with
    | let₁ ha hb =>
      obtain ⟨da⟩ := LetCase.LocallyNameless.Derivation.ofHasType
        ((Morphism.CaseSSA.ofScoped_hasType_iff hs.1).mpr ha)
      obtain ⟨db⟩ := ih (L := L) (β := .snoc β _) (by simpa only [BoundCtx.toList] using hb) hs.2
      exact ⟨.let₁ hs.1 da db⟩
  | let₂ arg body ih =>
    cases h with
    | let₂ ha hb =>
      obtain ⟨da⟩ := LetCase.LocallyNameless.Derivation.ofHasType
        ((Morphism.CaseSSA.ofScoped_hasType_iff hs.1).mpr ha)
      obtain ⟨db⟩ := ih (L := L) (β := .snoc (.snoc β _) _) (by simpa only [BoundCtx.toList] using hb) hs.2
      exact ⟨.let₂ hs.1 da db⟩
  | case arg left right ihl ihr =>
    cases h with
    | case he hl hr =>
      obtain ⟨da⟩ := LetCase.LocallyNameless.Derivation.ofHasType
        ((Morphism.CaseSSA.ofScoped_hasType_iff hs.1).mpr he)
      obtain ⟨dl⟩ := ihl (L := L) (β := .snoc β _) (by simpa only [BoundCtx.toList] using hl) hs.2.1
      obtain ⟨dr⟩ := ihr (L := L) (β := .snoc β _) (by simpa only [BoundCtx.toList] using hr) hs.2.2
      exact ⟨.case hs.1 da dl dr⟩
  | cfg entry count blocks ihe ihb =>
    cases h with
    | cfg R he hb =>
      obtain ⟨de⟩ := ihe (L := SSA.FiniteSum.append R L)
        (by simpa only [SSA.FiniteSum.ofFn_append] using he) hs.1
      have db : ∀ i, Nonempty (Derivation Φ (SSA.FiniteSum.append R L) (.snoc β (R i)) (blocks i)) :=
        fun i => ihb i (by simpa only [SSA.FiniteSum.ofFn_append, BoundCtx.toList] using hb i) (hs.2 i)
      exact ⟨.cfg R de (fun i => Classical.choice (db i))⟩

@[simp] theorem nonempty_iff {labels n : Nat} {L : Fin labels → τ}
    {β : BoundCtx τ n} {r : Region Φ} :
    Nonempty (Derivation Φ L β r) ↔ Region.HasType β.toList r (List.ofFn L) :=
  ⟨fun ⟨d⟩ => d.toHasType, ofHasType⟩

end Derivation
end Silmaril.Isotope.LambdaSSA.Region

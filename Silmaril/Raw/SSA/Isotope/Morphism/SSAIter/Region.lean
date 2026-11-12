module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.RegionScope
public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Encode

/-! # Nested SSA regions as structured iteration

Each CFG binder introduces its own tagged dispatcher. Its blocks may themselves
contain arbitrary CFG binders. A completed inner dispatcher returns to its
surrounding region through the same label-emission interface as a direct jump.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open SSA.FiniteSum (sumTy append)

variable {Φ : Type u}

/-- Scoped raw expressions use the existing lossless SSA/let-case conversion. -/
def encodeExpr {n : Nat} (a : LambdaSSA.Tm Φ) (h : a.Scoped n) : Tm Empty Φ n :=
  CaseIter.embed (CaseSSA.ofScoped a h)

/-- A CFG takes an encoded entry and one encoded body per internal label. -/
def encodeDispatch {blocks n : Nat} (entry : Tm Empty Φ n)
    (body : Fin blocks → Tm Empty Φ (n + 1)) : Tm Empty Φ n :=
  .case entry (.bv 0)
    (.iter (.bv 0) (dispatch (.bv 0) (fun i => (body i).underBinder)).underBinder)

/-- The emitter is polymorphic in binder depth, allowing jumps after arbitrary
local definitions. Recursion is over the original SSA syntax. -/
def encodeRegionWith {labels n : Nat}
    (emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n)
    (r : LambdaSSA.Region Φ) (h : r.Scoped labels n) : Tm Empty Φ n :=
  match r with
  | .br label arg => emit ⟨label, h.1⟩ (encodeExpr arg h.2)
  | .let₁ value body => .let₁ (encodeExpr value h.1) (encodeRegionWith emit body h.2)
  | .let₂ value body => .let₂ (encodeExpr value h.1) (encodeRegionWith emit body h.2)
  | .case discr left right => .case (encodeExpr discr h.1)
      (encodeRegionWith emit left h.2.1) (encodeRegionWith emit right h.2.2)
  | .cfg entry count blocks =>
    dispatch (encodeDispatch
      (encodeRegionWith (emitCFG (blocks := count) (exits := labels)) entry h.1)
      (fun i => encodeRegionWith (emitCFG (blocks := count) (exits := labels)) (blocks i) (h.2 i)))
      (fun i => emit i (.bv 0))

def encodeRegion {labels n : Nat} (r : LambdaSSA.Region Φ) (h : r.Scoped labels n) :
    Tm Empty Φ n := encodeRegionWith (fun i a => inject i a) r h

variable {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

theorem encodeExpr_hasType {n : Nat} {β : BoundCtx τ n} {a : LambdaSSA.Tm Φ}
    (hscope : a.Scoped n) {A : τ} (h : LambdaSSA.Tm.HasType β.toList a A) :
    HasType Φ .nil β (encodeExpr a hscope) A :=
  CaseIter.embed_hasType ((CaseSSA.ofScoped_hasType_iff hscope).mpr h)

theorem encodeDispatch_hasType {blocks n : Nat} {β : BoundCtx τ n}
    {R : Fin blocks → τ} {O : τ} {entry : Tm Empty Φ n}
    {body : Fin blocks → Tm Empty Φ (n + 1)}
    (he : HasType Φ .nil β entry (Silmaril.coprod O (sumTy R)))
    (hb : ∀ i, HasType Φ .nil (.snoc β (R i)) (body i) (Silmaril.coprod O (sumTy R))) :
    HasType Φ .nil β (encodeDispatch entry body) O :=
  .case he .bv (.iter .bv (dispatch_hasType R .bv (fun i => (hb i).underBinder)).underBinder)

/-- Exact typing is preserved for every nested CFG, without choosing uniform
block argument types or requiring reducible control flow. -/
theorem encodeRegionWith_hasType {labels n : Nat} {r : LambdaSSA.Region Φ}
    (hscope : r.Scoped labels n) {L : Fin labels → τ} {β : BoundCtx τ n} {O : τ}
    {emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n}
    (hemit : ∀ {n : Nat} {β : BoundCtx τ n} {i : Fin labels} {a : Tm Empty Φ n},
      HasType Φ .nil β a (L i) → HasType Φ .nil β (emit i a) O)
    (h : LambdaSSA.Region.HasType β.toList r (List.ofFn L)) :
    HasType Φ .nil β (encodeRegionWith emit r hscope) O := by
  induction r generalizing labels n O with
  | br label arg =>
    cases h with
    | br hl ha =>
      have eq := Option.some.inj ((SSA.FiniteSum.at_ofFn L ⟨label, hscope.1⟩).symm.trans hl)
      exact hemit (encodeExpr_hasType hscope.2 (eq.symm ▸ ha))
  | let₁ value body ih =>
    cases h with
    | let₁ ha hb => exact .let₁ (encodeExpr_hasType hscope.1 ha) (ih hscope.2 hemit hb)
  | let₂ value body ih =>
    cases h with
    | let₂ ha hb => exact .let₂ (encodeExpr_hasType hscope.1 ha) (ih hscope.2 hemit hb)
  | case discr left right ihl ihr =>
    cases h with
    | case he hl hr =>
      exact .case (encodeExpr_hasType hscope.1 he)
        (ihl hscope.2.1 hemit hl) (ihr hscope.2.2 hemit hr)
  | cfg entry count blocks ihe ihb =>
    cases h with
    | cfg R he hb =>
      apply dispatch_hasType L
      · apply encodeDispatch_hasType (R := R)
        · apply ihe hscope.1 (emitCFG_hasType R L)
          simpa only [SSA.FiniteSum.ofFn_append] using he
        · intro i
          apply ihb i (hscope.2 i) (emitCFG_hasType R L)
          simpa only [SSA.FiniteSum.ofFn_append, BoundCtx.toList] using hb i
      · intro i
        exact hemit .bv

theorem encodeRegion_hasType {labels n : Nat} {r : LambdaSSA.Region Φ}
    (hscope : r.Scoped labels n) {L : Fin labels → τ} {β : BoundCtx τ n}
    (h : LambdaSSA.Region.HasType β.toList r (List.ofFn L)) :
    HasType Φ .nil β (encodeRegion r hscope) (sumTy L) :=
  encodeRegionWith_hasType hscope (fun {_n _β i _a} ha => inject_hasType L i ha) h

end Silmaril.Isotope.Morphism.SSAIter

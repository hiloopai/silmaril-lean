module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Flat
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter
public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Sum

/-!
# Finite CFGs as a single let-iter loop

Each internal block has its own argument type, stored in a tagged loop state.
The entry region executes once. An entry exit returns directly; an internal
entry jump starts a loop whose dispatcher chooses the next block by its tag.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open SSA.FiniteSum (sumTy append)

variable {Φ : Type u} {labels n blocks exits captured : Nat}

/-- Translate a flat region, parameterized by how its jumps return a result.
The emitter works uniformly at every binder depth. -/
def encodeFlatWith (emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n) :
    {n : Nat} → LambdaSSA.Flat Φ labels n → Tm Empty Φ n
  | _, .br i a => emit i (CaseIter.embed a)
  | _, .let₁ a b => .let₁ (CaseIter.embed a) (encodeFlatWith emit b)
  | _, .let₂ a b => .let₂ (CaseIter.embed a) (encodeFlatWith emit b)
  | _, .case e l r => .case (CaseIter.embed e) (encodeFlatWith emit l) (encodeFlatWith emit r)

/-- A flat region returns its target label and corresponding payload. -/
def encodeFlat (r : LambdaSSA.Flat Φ labels n) : Tm Empty Φ n :=
  encodeFlatWith (fun i a => inject i a) r

/-- External targets return on the left; internal targets continue on the right. -/
def emitCFG (i : Fin (blocks + exits)) (a : Tm Empty Φ n) : Tm Empty Φ n :=
  Fin.addCases (fun j => .inr (inject j a)) (fun j => .inl (inject j a)) i

/-- One dispatch step runs the block selected by the current tagged state.
The current state binder is inserted below each block's payload binder. -/
def loopBody (g : LambdaSSA.FiniteCFG Φ blocks exits captured) : Tm Empty Φ (captured + 1) :=
  dispatch (.bv 0) (fun i => (encodeFlatWith emitCFG (g.block i)).underBinder)

/-- Encode arbitrary finite control flow, including irreducible cycles and exits
from the entry region. No ordering or acyclicity condition is imposed on blocks. -/
def encodeCFG (g : LambdaSSA.FiniteCFG Φ blocks exits captured) : Tm Empty Φ captured :=
  .case (encodeFlatWith emitCFG g.entry) (.bv 0)
    (.iter (.bv 0) (loopBody g).underBinder)

variable {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- Translation is typed whenever each emitted jump has the common result type. -/
theorem encodeFlatWith_hasType {L : Fin labels → τ} {O : τ}
    {emit : {n : Nat} → Fin labels → Tm Empty Φ n → Tm Empty Φ n}
    (hemit : ∀ {n : Nat} {β : BoundCtx τ n} {i : Fin labels} {a : Tm Empty Φ n},
      HasType Φ .nil β a (L i) → HasType Φ .nil β (emit i a) O)
    {β : BoundCtx τ n} {r : LambdaSSA.Flat Φ labels n} (h : r.HasType L β) :
    HasType Φ .nil β (encodeFlatWith emit r) O := by
  induction h with
  | br ha => exact hemit (CaseIter.embed_hasType ha)
  | let₁ ha _ ih => exact .let₁ (CaseIter.embed_hasType ha) ih
  | let₂ ha _ ih => exact .let₂ (CaseIter.embed_hasType ha) ih
  | case he _ _ ihl ihr => exact .case (CaseIter.embed_hasType he) ihl ihr

theorem encodeFlat_hasType {L : Fin labels → τ} {β : BoundCtx τ n}
    {r : LambdaSSA.Flat Φ labels n} (h : r.HasType L β) :
    HasType Φ .nil β (encodeFlat r) (sumTy L) :=
  encodeFlatWith_hasType (fun {_n _β i _a} ha => inject_hasType L i ha) h

theorem emitCFG_hasType (R : Fin blocks → τ) (E : Fin exits → τ)
    {β : BoundCtx τ n} {i : Fin (blocks + exits)} {a : Tm Empty Φ n}
    (h : HasType Φ .nil β a (append R E i)) :
    HasType Φ .nil β (emitCFG i a) (Silmaril.coprod (sumTy E) (sumTy R)) := by
  revert h
  refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i
  · simpa [emitCFG] using
      (HasType.inr (B := sumTy R) (A := sumTy E) (inject_hasType R j (by simpa using h)))
  · simpa [emitCFG] using
      (HasType.inl (B := sumTy R) (inject_hasType E j (by simpa using h)))

/-- The loop state is the heterogeneous sum of internal block argument types. -/
theorem loopBody_hasType {β : BoundCtx τ captured} {R : Fin blocks → τ}
    {E : Fin exits → τ} {g : LambdaSSA.FiniteCFG Φ blocks exits captured}
    (h : g.HasType β R E) :
    HasType Φ .nil (.snoc β (sumTy R)) (loopBody g)
      (Silmaril.coprod (sumTy E) (sumTy R)) := by
  apply dispatch_hasType R HasType.bv
  intro i
  exact (encodeFlatWith_hasType (emitCFG_hasType R E) (h.block i)).underBinder

/-- Exact typing of the complete graph encoding. External exit payloads retain
their own types, and may be returned before the first loop iteration. -/
theorem encodeCFG_hasType {β : BoundCtx τ captured} {R : Fin blocks → τ}
    {E : Fin exits → τ} {g : LambdaSSA.FiniteCFG Φ blocks exits captured}
    (h : g.HasType β R E) : HasType Φ .nil β (encodeCFG g) (sumTy E) := by
  exact .case (encodeFlatWith_hasType (emitCFG_hasType R E) h.entry) .bv
    (.iter .bv (loopBody_hasType h).underBinder)

end Silmaril.Isotope.Morphism.SSAIter

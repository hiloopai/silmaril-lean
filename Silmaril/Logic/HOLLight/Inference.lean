module

public import Silmaril.Logic.HOLLight.ContextDeduction
public import Silmaril.Logic.Metatheory.InferenceMorphism
public import Cslib.Foundations.Logic.Operators

@[expose] public section

/-!
# HOL Light as CSLib inference systems

The system tags below retain the signature and explicit object theory. The
fixed-context tag additionally retains the hypotheses. Their derivations are
the existing kernel judgment, without an additional proof grammar.
-/

namespace Silmaril.Logic.HOLLight

open Cslib.Logic Cslib.Logic.InferenceSystem
open Silmaril.Logic.Metatheory

/-- A locally closed Boolean HOL term with its independently checked typing. -/
abbrev Formula (sig : Signature) := Checked sig [] .bool

namespace Formula

@[ext] theorem ext {sig : Signature} {p q : Formula sig}
    (h : p.term = q.term) : p = q := by
  cases p
  cases q
  cases h
  rfl

instance {sig : Signature} : DecidableEq (Formula sig) := fun p q =>
  if h : p.term = q.term then isTrue (ext h)
  else isFalse (fun h' => h (congrArg Checked.term h'))

/-- The designated false atom for CSLib propositional logic over HOL formulas. -/
instance {sig : Signature} : Bot (Formula sig) := ⟨⟨Tm.falsity, HasType.falsity⟩⟩

@[simp] theorem bot_term {sig : Signature} : (⊥ : Formula sig).term = Tm.falsity := rfl

instance {sig : Signature} : Top (Formula sig) := ⟨⟨Tm.truth, HasType.truth⟩⟩

instance {sig : Signature} : HasAnd (Formula sig) :=
  ⟨fun p q => ⟨Tm.conj p.term q.term, p.typing.conj q.typing⟩⟩

instance {sig : Signature} : HasOr (Formula sig) :=
  ⟨fun p q => ⟨Tm.disj p.term q.term, p.typing.disj q.typing⟩⟩

instance {sig : Signature} : HasImp (Formula sig) :=
  ⟨fun p q => ⟨Tm.imp p.term q.term, p.typing.imp q.typing⟩⟩

instance {sig : Signature} : HasNot (Formula sig) :=
  ⟨fun p => ⟨Tm.neg p.term, p.typing.neg⟩⟩

@[simp] theorem top_term {sig : Signature} : (⊤ : Formula sig).term = Tm.truth := rfl

end Formula

/-- A sequent with raw syntax; derivability guarantees all formulas are typed. -/
structure Sequent where
  hyps : Hyps
  conclusion : Tm

/-- The kernel with a fixed signature and object theory. -/
structure KernelSystem (sig : Signature) (theory : Theory) where

/-- The kernel with a fixed signature, theory, and hypothesis context. -/
structure ContextSystem (sig : Signature) (theory : Theory) (H : Hyps) where

instance {sig : Signature} {theory : Theory} :
    InferenceSystem (KernelSystem sig theory) Sequent where
  derivation s := Derives sig theory s.hyps s.conclusion

instance {sig : Signature} {theory : Theory} {H : Hyps} :
    InferenceSystem (ContextSystem sig theory H) Tm where
  derivation p := Derives sig theory H p

instance {sig : Signature} {theory : Theory} {H : Hyps} :
    InferenceSystem (ContextSystem sig theory H) (Formula sig) where
  derivation p := Derives sig theory H p.term

@[simp] theorem sequent_derivable_iff {sig : Signature} {theory : Theory} {s : Sequent} :
    DerivableIn (KernelSystem sig theory) s ↔ Derives sig theory s.hyps s.conclusion :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp] theorem context_derivable_iff {sig : Signature} {theory : Theory} {H : Hyps} {p : Tm} :
    DerivableIn (ContextSystem sig theory H) p ↔ Derives sig theory H p :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp] theorem formula_derivable_iff {sig : Signature} {theory : Theory}
    {H : Hyps} {p : Formula sig} :
    DerivableIn (ContextSystem sig theory H) p ↔ Derives sig theory H p.term :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- Enlarging a well-typed context is an inference-system morphism. -/
def ContextSystem.weaken {sig : Signature} {theory : Theory} {H K : Hyps}
    (hK : TypedHyps sig [] K) (hHK : H ⊆ K) :
    InferenceMorphism (ContextSystem sig theory H) (ContextSystem sig theory K) Tm Tm where
  map := id
  mapDerivation := fun h => h.weaken hHK hK

/-- A context can be replaced by any typed context deriving all its hypotheses. -/
def ContextSystem.substituteHyps {sig : Signature} {theory : Theory} {H K : Hyps}
    (hK : TypedHyps sig [] K) (proofs : ∀ p ∈ H, Derives sig theory K p) :
    InferenceMorphism (ContextSystem sig theory H) (ContextSystem sig theory K) Tm Tm where
  map := id
  mapDerivation := fun h => h.substituteHyps hK proofs

/-- Discharge a fixed context into a single antecedent in the empty-context system. -/
noncomputable def ContextSystem.discharge {sig : Signature} {theory : Theory} {H : Hyps}
    (typed : TypedHyps sig [] H) :
    InferenceMorphism (ContextSystem sig theory H) (ContextSystem sig theory ∅) Tm Tm where
  map p := Tm.imp (Tm.andAll H) p
  mapDerivation h := (Derives.andAll_imp_iff typed h.typing).mpr h

/-- The finite-context deduction theorem in CSLib's derivability interface. -/
theorem ContextSystem.deduction_iff {sig : Signature} {theory : Theory} {H : Hyps}
    (typed : TypedHyps sig [] H) (p : Formula sig) :
    DerivableIn (ContextSystem sig theory ∅) (Tm.imp (Tm.andAll H) p.term) ↔
      DerivableIn (ContextSystem sig theory H) p := by
  simpa using Derives.andAll_imp_iff (theory := theory) typed p.typing

end Silmaril.Logic.HOLLight

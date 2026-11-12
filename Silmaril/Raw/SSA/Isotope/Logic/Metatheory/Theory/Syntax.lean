module

public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-!
# Indexed syntax and translations

A sort may be a scope, a context/type/effect judgment, or the single sort of
untyped syntax. Designated one-hole contexts can change sorts, so binders and
typed term constructors do not need to be encoded as endomorphisms.
-/

namespace Silmaril.Logic.Metatheory

universe u v w x y z

/-- Syntax with its admissible one-hole contexts. -/
structure IndexedSyntax where
  Index : Type u
  Term : Index → Type v
  Context : {i j : Index} → (Term i → Term j) → Prop

namespace IndexedSyntax

/-- Relations compare terms in the same syntax fiber. -/
abbrev Relation (S : IndexedSyntax.{u, v}) :=
  {i : S.Index} → S.Term i → S.Term i → Prop

/-- A conclusion of a theory: two terms with one common sort. -/
abbrev Judgment (S : IndexedSyntax.{u, v}) := Σ i : S.Index, S.Term i × S.Term i

/-- Single-sorted syntax, with explicitly chosen one-hole contexts. -/
abbrev untyped (α : Type v) (context : (α → α) → Prop) : IndexedSyntax.{0, v} where
  Index := Unit
  Term _ := α
  Context := context

/-- Indexed syntax when no congruence requirements have been specified. -/
abbrev ofFamily {I : Type u} (term : I → Type v) : IndexedSyntax.{u, v} where
  Index := I
  Term := term
  Context _ := False

/-- A translation may change sorts as well as the terms in each fiber. -/
structure Translation (S : IndexedSyntax.{u, v}) (T : IndexedSyntax.{w, x}) where
  sort : S.Index → T.Index
  term : {i : S.Index} → S.Term i → T.Term (sort i)

namespace Translation

variable {S : IndexedSyntax.{u, v}} {T : IndexedSyntax.{w, x}}
  {U : IndexedSyntax.{y, z}}

def id (S : IndexedSyntax.{u, v}) : Translation S S where
  sort i := i
  term a := a

def comp (g : Translation T U) (f : Translation S T) : Translation S U where
  sort i := g.sort (f.sort i)
  term a := g.term (f.term a)

/-- Apply a syntax translation to both sides of a theory judgment. -/
def judgment (f : Translation S T) : S.Judgment → T.Judgment
  | ⟨i, a, b⟩ => ⟨f.sort i, f.term a, f.term b⟩

/-- Compatibility needed to transport generated congruences. Theory morphisms
themselves only need to preserve the theory's relation. -/
def Contextual (f : Translation S T) : Prop :=
  ∀ {i j} (c : S.Term i → S.Term j), S.Context c →
    ∃ d : T.Term (f.sort i) → T.Term (f.sort j),
      T.Context d ∧ ∀ a, f.term (c a) = d (f.term a)

theorem id_contextual (S : IndexedSyntax.{u, v}) : (id S).Contextual := by
  intro i j c hc
  exact ⟨c, hc, fun _ => rfl⟩

theorem Contextual.comp {f : Translation S T} {g : Translation T U}
    (hg : g.Contextual) (hf : f.Contextual) : (g.comp f).Contextual := by
  intro i j c hc
  obtain ⟨d, hd, hfd⟩ := hf c hc
  obtain ⟨e, he, hge⟩ := hg d hd
  refine ⟨e, he, ?_⟩
  intro a
  change g.term (f.term (c a)) = e (g.term (f.term a))
  rw [hfd, hge]

end Translation

end IndexedSyntax

end Silmaril.Logic.Metatheory

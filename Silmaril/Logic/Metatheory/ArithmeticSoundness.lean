module

public import Silmaril.Logic.Metatheory.Consistency

@[expose] public section

/-!
# Arithmetical soundness and ω-consistency

An arithmetic language (`ArithLanguage`) has sentences, a class of Σ₁
sentences and truth in the standard model ℕ. The language itself is a
parameter: first-order arithmetic, the language of Metamath's `peano.mm`, or
the arithmetic fragment of a set theory.

A system is interpreted by a translation `tr` of arithmetic sentences into its
conclusions, and its derivability is a predicate `Der` on conclusions. The
system is arithmetically sound for `tr` when every arithmetic sentence whose
translation it derives is true in ℕ (`ArithSound`), and Σ₁-sound when this
holds for Σ₁ sentences (`Sigma1Sound`). For a CSLib inference system `S` take
`Der := InferenceSystem.DerivableIn S`, and for an object of
`InferenceSystemCat` take `Der := S.Provable`.

The general criterion (`arithSound_of_model`): a semantics for which the
system is sound and which agrees with ℕ on translated sentences makes the
system arithmetically sound. In Metamath this is applied to a model whose
interpretation of the arithmetic language is isomorphic to the standard one
(`Silmaril.Logic.Metamath.Model.arithSound_of_iso`).

With formulas in one free variable, numeral instances, negation and
existential quantification obeying the Tarski clauses (`OmegaLanguage`), a
system is ω-consistent when it never derives `∃ x φ(x)` together with every
`¬ φ(n)` (`OmegaLanguage.OmegaConsistent`). Arithmetical soundness implies
ω-consistency, and ω-consistency implies consistency.
-/

namespace Silmaril.Logic.Metatheory

universe u v

/-- An arithmetic language: sentences, the Σ₁ sentences, and truth in ℕ. -/
structure ArithLanguage where
  Sentence : Type u
  IsSigma1 : Sentence → Prop
  TrueInNat : Sentence → Prop

namespace ArithLanguage

variable (A : ArithLanguage.{u}) {α : Type v} (Der : α → Prop) (tr : A.Sentence → α)

/-- Every arithmetic sentence whose translation is derivable is true in ℕ. -/
def ArithSound : Prop := ∀ φ, Der (tr φ) → A.TrueInNat φ

/-- Every Σ₁ sentence whose translation is derivable is true in ℕ. -/
def Sigma1Sound : Prop := ∀ φ, A.IsSigma1 φ → Der (tr φ) → A.TrueInNat φ

variable {A Der tr}

theorem ArithSound.sigma1Sound (h : A.ArithSound Der tr) : A.Sigma1Sound Der tr :=
  fun φ _ hφ => h φ hφ

/-- Fewer derivable conclusions preserve arithmetical soundness. -/
theorem ArithSound.mono {Der' : α → Prop} (hle : ∀ a, Der' a → Der a)
    (h : A.ArithSound Der tr) : A.ArithSound Der' tr :=
  fun φ hφ => h φ (hle _ hφ)

theorem Sigma1Sound.mono {Der' : α → Prop} (hle : ∀ a, Der' a → Der a)
    (h : A.Sigma1Sound Der tr) : A.Sigma1Sound Der' tr :=
  fun φ hs hφ => h φ hs (hle _ hφ)

/-- A semantics for which the system is sound and which agrees with ℕ on the
translated sentences makes the system arithmetically sound. -/
theorem arithSound_of_model (Sat : α → Prop) (sound : ∀ a, Der a → Sat a)
    (agree : ∀ φ, Sat (tr φ) → A.TrueInNat φ) : A.ArithSound Der tr :=
  fun φ hφ => agree φ (sound _ hφ)

/-- An arithmetically sound system does not derive the translation of a false
sentence. -/
theorem ArithSound.not_der (h : A.ArithSound Der tr) {φ : A.Sentence} (hφ : ¬ A.TrueInNat φ) :
    ¬ Der (tr φ) :=
  fun hd => hφ (h φ hd)

/-- A Σ₁-sound system does not derive the translation of a false Σ₁ sentence. -/
theorem Sigma1Sound.not_der (h : A.Sigma1Sound Der tr) {φ : A.Sentence} (hs : A.IsSigma1 φ)
    (hφ : ¬ A.TrueInNat φ) : ¬ Der (tr φ) :=
  fun hd => hφ (h φ hs hd)

/-- A Σ₁-sound CSLib inference system with a false Σ₁ sentence is consistent. -/
theorem Sigma1Sound.consistent {S : Type*} [Cslib.Logic.InferenceSystem S α]
    {tr : A.Sentence → α} (h : A.Sigma1Sound (Cslib.Logic.InferenceSystem.DerivableIn S) tr)
    {φ : A.Sentence} (hs : A.IsSigma1 φ) (hφ : ¬ A.TrueInNat φ) : Consistent S α :=
  ⟨tr φ, h.not_der hs hφ⟩

end ArithLanguage

/-- An arithmetic language with formulas in one free variable, their
instances at numerals, negation and existential quantification, obeying the
Tarski clauses in ℕ. -/
structure OmegaLanguage extends ArithLanguage.{u} where
  Formula : Type u
  inst : Formula → ℕ → Sentence
  neg : Sentence → Sentence
  ex : Formula → Sentence
  true_neg : ∀ φ, TrueInNat (neg φ) ↔ ¬ TrueInNat φ
  true_ex : ∀ φ, TrueInNat (ex φ) ↔ ∃ n, TrueInNat (inst φ n)

namespace OmegaLanguage

variable (A : OmegaLanguage.{u}) {α : Type v} (Der : α → Prop) (tr : A.Sentence → α)

/-- The system never derives `∃ x φ(x)` together with every `¬ φ(n)`. -/
def OmegaConsistent : Prop := ∀ φ, Der (tr (A.ex φ)) → ∃ n, ¬ Der (tr (A.neg (A.inst φ n)))

variable {A Der tr}

/-- Arithmetical soundness implies ω-consistency. -/
theorem omegaConsistent_of_arithSound (h : A.ArithSound Der tr) : A.OmegaConsistent Der tr := by
  intro φ hex
  obtain ⟨n, hn⟩ := (A.true_ex φ).1 (h _ hex)
  exact ⟨n, fun hneg => (A.true_neg _).1 (h _ hneg) hn⟩

/-- An ω-consistent system does not derive everything. -/
theorem OmegaConsistent.exists_not_der (h : A.OmegaConsistent Der tr) (φ : A.Formula)
    (hex : Der (tr (A.ex φ))) : ∃ a, ¬ Der a :=
  let ⟨_, hn⟩ := h φ hex
  ⟨_, hn⟩

/-- An ω-consistent system is consistent: if it derived everything it would
derive `∃ x φ(x)` and every `¬ φ(n)`. -/
theorem OmegaConsistent.not_forall (h : A.OmegaConsistent Der tr) (φ : A.Formula) :
    ¬ ∀ a, Der a :=
  fun hall => let ⟨_, hn⟩ := h φ (hall _); hn (hall _)

end OmegaLanguage

end Silmaril.Logic.Metatheory

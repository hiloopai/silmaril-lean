module

public import Mathlib.Order.Closure
public import Mathlib.Data.List.Perm.Subperm

/-!
# Structural rules and structural closures of list-sequent relations

A relation `R : List C → C → Prop` reads `R Γ c` as "the list of premises `Γ` yields `c`". Here
nothing is assumed of `R`: every structural rule is a separate, named property, and every
closure adds exactly the rules it is asked to add.

**Rules** (properties of `R`):

* `Reflexive R`: `c ∈ Γ → R Γ c` (membership, not an arbitrary `R Γ c`).
* `WeakensAlong W R`: `W Γ Δ → R Γ c → R Δ c`, for a *weakening policy* `W`. The policies are
  kept distinct: `List.Sublist` (`WeakSublist`: insert premises, keep order and multiplicity),
  `List.Subperm` (`WeakSubperm`: also reorder), and list inclusion `⊆` (`WeakSubset`: set-like
  premises, which also gives exchange and contraction).
* `Exchange R` (permutations of `Γ`) and `Contraction R` (`a :: a :: Γ` to `a :: Γ`).
* `Cut R`: finite multi-cut. From premises `Γᵢ ⊢ cᵢ` (`i < n`) and `[c₀, …, cₙ₋₁] ⊢ c`,
  conclude `Γ₀ ++ … ++ Γₙ₋₁ ⊢ c`. Contexts are concatenated, never shared, so cut adds no
  weakening or contraction of its own: weakening by an arbitrary context is a separate rule.
* `Substitutive act R`: invariance under substitution (structurality), for an action
  `act : Sub → C → C` of substitutions on formulas. A logic says which substitutions are
  allowed through the type `Sub`: well-formed type instantiations and type-respecting term
  instantiations in HOL, syntax rewrites (an injective variable renaming with a template for each
  syntax rule) in Metamath. Side conditions such as Metamath's disjoint-variable conditions are
  part of the sentences or of `Sub`, never of this definition.

**Closures.** `Rules C` selects which rules to close under (`refl`, `cut`: switches; `weak`:
the weakening policy, `⊥` for none). `Derives rs R` is the inductive closure of `R` under the
selected rules. Special cases: `reflRules`, `cutRules`, `weakRules W`, and the joint
`jointRules W` (reflexivity, cut and weakening along `W`). `Derives` is the least closed relation
above `R` (`Silmaril.Logic.Consequence.Structural.Thms`), which makes `closure rs` a Mathlib
`ClosureOperator` on `List C → C → Prop` whose closed elements form a complete lattice.

`R` is a bare relation so this module does not depend on the core `Silmaril.Consequence.System`
(`System (List C) C` is the same type). The witness-carrying version is in
`Silmaril.Logic.Consequence.Structural.Witness`.
-/

@[expose] public section

namespace Silmaril.Consequence.Structural

universe u v

variable {C : Type u}

/-- A list-sequent relation: `R Γ c` reads "premises `Γ` yield `c`". -/
abbrev Rel (C : Type u) : Type u := List C → C → Prop

/-! ## Structural rules -/

/-- Reflexivity (identity axiom): a premise is a consequence. -/
def Reflexive (R : Rel C) : Prop := ∀ ⦃Γ c⦄, c ∈ Γ → R Γ c

/-- Weakening along the policy `W`: if `W Γ Δ` then `Γ ⊢ c` gives `Δ ⊢ c`. -/
def WeakensAlong (W : List C → List C → Prop) (R : Rel C) : Prop :=
  ∀ ⦃Γ Δ c⦄, W Γ Δ → R Γ c → R Δ c

/-- Weakening along sublists: premises may be inserted anywhere, order and multiplicity kept. -/
abbrev WeakSublist (R : Rel C) : Prop := WeakensAlong List.Sublist R

/-- Weakening along sub-permutations: premises may be inserted and reordered. -/
abbrev WeakSubperm (R : Rel C) : Prop := WeakensAlong List.Subperm R

/-- Weakening along list inclusion (`∀ x ∈ Γ, x ∈ Δ`): premises behave as a set. -/
abbrev WeakSubset (R : Rel C) : Prop := WeakensAlong (fun Γ Δ : List C => Γ ⊆ Δ) R

/-- Exchange: premises may be permuted. -/
def Exchange (R : Rel C) : Prop := ∀ ⦃Γ Δ c⦄, Γ.Perm Δ → R Γ c → R Δ c

/-- Contraction of a duplicated head premise. -/
def Contraction (R : Rel C) : Prop := ∀ ⦃a Γ c⦄, R (a :: a :: Γ) c → R (a :: Γ) c

/-- **Substitution (structurality)** along an action of substitutions on formulas: substituting
in the premises and in the conclusion of a consequence gives a consequence. -/
def Substitutive {Sub : Type v} (act : Sub → C → C) (R : Rel C) : Prop :=
  ∀ (s : Sub) ⦃Γ c⦄, R Γ c → R (Γ.map (act s)) (act s c)

/-- Finite multi-cut with concatenated contexts: from `Γᵢ ⊢ cᵢ` for every `(Γᵢ, cᵢ)` in `ps` and
`[c₀, …] ⊢ c`, conclude `Γ₀ ++ … ⊢ c`. -/
def Cut (R : Rel C) : Prop :=
  ∀ ⦃ps : List (List C × C)⦄ ⦃c⦄,
    (∀ p ∈ ps, R p.1 p.2) → R (ps.map Prod.snd) c → R (ps.flatMap Prod.fst) c

/-! ## Selecting rules -/

/-- Which structural rules a closure adds: reflexivity when `refl` holds, multi-cut when `cut`
holds, and weakening along `weak` (`⊥`: none). -/
structure Rules (C : Type u) where
  /-- Close under reflexivity. -/
  refl : Prop
  /-- Close under weakening along this policy. -/
  weak : List C → List C → Prop
  /-- Close under multi-cut. -/
  cut : Prop

/-- Only reflexivity. -/
def reflRules : Rules C := ⟨True, ⊥, False⟩

/-- Only multi-cut. -/
def cutRules : Rules C := ⟨False, ⊥, True⟩

/-- Only weakening along `W`. -/
def weakRules (W : List C → List C → Prop) : Rules C := ⟨False, W, False⟩

/-- Reflexivity, multi-cut and weakening along `W`. -/
def jointRules (W : List C → List C → Prop) : Rules C := ⟨True, W, True⟩

/-- Reflexivity, multi-cut and weakening along list inclusion: Tarski-style consequence on lists,
whose premises behave as finite sets. -/
abbrev tarskiRules : Rules C := jointRules fun Γ Δ => Γ ⊆ Δ

/-- `R` is closed under the selected rules. -/
structure Closed (rs : Rules C) (R : Rel C) : Prop where
  refl : rs.refl → Reflexive R
  weak : WeakensAlong rs.weak R
  cut : rs.cut → Cut R

/-! ## Inductive closure -/

/-- Derivations from `R` with the selected structural rules (proof-irrelevant). -/
inductive Derives (rs : Rules C) (R : Rel C) : Rel C
  | base {Γ c} : R Γ c → Derives rs R Γ c
  | refl {Γ c} : rs.refl → c ∈ Γ → Derives rs R Γ c
  | weak {Γ Δ c} : rs.weak Γ Δ → Derives rs R Γ c → Derives rs R Δ c
  | cut (ps : List (List C × C)) {c} : rs.cut → (∀ p ∈ ps, Derives rs R p.1 p.2) →
      Derives rs R (ps.map Prod.snd) c → Derives rs R (ps.flatMap Prod.fst) c

end Silmaril.Consequence.Structural

module

public import Silmaril.Semantics.Domain.Omega
public import Silmaril.Calculi.Imp.Denotation


/-! # §2 Least fixed points (pp. 12–22)

Index of §2 of the notes against `Silmaril.Semantics.Domain`. Each numbered item has a
wrapper named after it. Theorems restate the notes' statement and are proved
by the general development; definitions are aliases of the Mathlib or
Silmaril notion, followed by `example`s that check the defining property.

Posets, monotone maps, least elements and fixed points are Mathlib's. Chains
are Mathlib's `OmegaCompletePartialOrder.Chain`, a monotone sequence `ℕ →o D`,
and the lub of a chain `c` is `IsLUB (Set.range c)`. A cpo is Mathlib's
`OmegaCompletePartialOrder`, which records the lub `ωSup` as data; since lubs
are unique this is no extra structure (`ofChainComplete`). Partial functions
`X ⇀ Y` are `X → Part Y`, and the vertical naturals `Ω` are `ℕ∞`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.DenotationalSemantics.LeastFixedPoints

open Silmaril.Calculi

open OmegaCompletePartialOrder Silmaril.Semantics.Domain

universe u

variable {D E : Type*}

/-! ## §2.1 Posets and monotone functions -/

/-- Definition 1 (Partially ordered set, p. 12): a reflexive, transitive and
antisymmetric relation `⊑` on `D`. -/
abbrev definition1 (D : Type u) : Type u := PartialOrder D

/-- Definition 1: the three axioms. -/
example [PartialOrder D] :
    (∀ d : D, d ≤ d) ∧ (∀ d d' d'' : D, d ≤ d' → d' ≤ d'' → d ≤ d'') ∧
      ∀ d d' : D, d ≤ d' → d' ≤ d → d = d' :=
  ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm⟩

/-- Example 1 (Domain of partial functions, p. 12): `X ⇀ Y` is ordered by
`f ⊑ g` iff `graph(f) ⊆ graph(g)`. -/
theorem example1 {X Y : Type*} {f g : X → Part Y} : f ≤ g ↔ graph f ⊆ graph g :=
  partialFun_le_iff

/-- Definition 2 (Monotone function, p. 13). -/
abbrev definition2 [Preorder D] [Preorder E] (f : D → E) : Prop := Monotone f

/-- Definition 2: `∀ d d' ∈ D. d ⊑ d' ⇒ f(d) ⊑ f(d')`. -/
example [Preorder D] [Preorder E] (f : D → E) :
    definition2 f ↔ ∀ d d' : D, d ≤ d' → f d ≤ f d' := Iff.rfl

/-- Example 2 (p. 13): constant functions are monotone. -/
theorem example2 [Preorder D] [Preorder E] (e : E) : Monotone fun _ : D => e :=
  monotone_const

/-- Example 3 (p. 13): `F_{b,c}` on `State ⇀ State` is monotone. -/
theorem example3 {L : Type*} (b : Imp.State L → Bool) (c : Imp.State L → Part (Imp.State L)) :
    Monotone (Imp.whileFun b c) :=
  Imp.whileFun_monotone b c

/-! ## §2.2 Least elements and pre-fixed points -/

/-- Definition 3 (Least element, p. 13): `d ∈ S` and `∀ x ∈ S. d ⊑ x`. -/
abbrev definition3 [PartialOrder D] (S : Set D) (d : D) : Prop := IsLeast S d

/-- Definition 3: the defining property, and uniqueness by antisymmetry. -/
example [PartialOrder D] (S : Set D) (d d' : D) :
    (definition3 S d ↔ d ∈ S ∧ ∀ x ∈ S, d ≤ x) ∧
      (definition3 S d → definition3 S d' → d = d') :=
  ⟨Iff.rfl, IsLeast.unique⟩

/-- Definition 4 (Fixed point, p. 13): `f(d) = d`. -/
abbrev definition4 (f : D → D) (d : D) : Prop := Function.IsFixedPt f d

example (f : D → D) (d : D) : definition4 f d ↔ f d = d := Iff.rfl

/-- Definition 5 ((Least) pre-fixed point, p. 13): `fix(f)` is the least `d`
with `f(d) ⊑ d`. -/
abbrev definition5 [PartialOrder D] (f : D → D) (d : D) : Prop := IsLeastPrefixedPoint f d

/-- Definition 5: `fix(f)` is characterized by (lfp-fix) and (lfp-least). -/
example [PartialOrder D] (f : D → D) (d : D) :
    definition5 f d ↔ f d ≤ d ∧ ∀ x, f x ≤ x → d ≤ x :=
  ⟨fun h => ⟨h.prefixed, fun _ => h.le⟩, fun h => .of_le h.1 h.2⟩

/-- Proposition 1 (Least pre-fixed points are least fixed points, p. 14): if
`f` is monotone, then `fix(f)` is a fixed point of `f`, and the least one. -/
theorem proposition1 [PartialOrder D] {f : D → D} {d : D} (hf : Monotone f)
    (h : IsLeastPrefixedPoint f d) : f d = d ∧ IsLeast (Function.fixedPoints f) d :=
  ⟨h.isFixedPt hf, h.isLeast_fixedPoints hf⟩

/-! ## §2.3 Least upper bounds -/

/-- Definition 6 (Least upper bound of a chain, p. 14): a chain is a monotone
sequence `d₀ ⊑ d₁ ⊑ d₂ ⊑ …`; its lub is `IsLUB (Set.range c)`. -/
abbrev definition6 (D : Type*) [Preorder D] : Type _ := Chain D

/-- Definition 6: the lub is an upper bound, below every upper bound. -/
example [PartialOrder D] (c : definition6 D) (d : D) (h : IsLUB (Set.range c) d) :
    (∀ m, c m ≤ d) ∧ ∀ d', (∀ m, c m ≤ d') → d ≤ d' :=
  ⟨fun m => h.1 ⟨m, rfl⟩, fun _ hd => h.2 (by rintro _ ⟨m, rfl⟩; exact hd m)⟩

/-- Remark 1 (iv) (p. 14): the lub of a chain is unique if it exists. It does
not have to exist: the chain `0 ≤ 1 ≤ 2 ≤ …` in `ℕ` has no upper bound (this is
also `example7`). -/
theorem remark1 [PartialOrder D] :
    (∀ {c : Chain D} {a b : D}, IsLUB (Set.range c) a → IsLUB (Set.range c) b → a = b) ∧
      ¬ BddAbove (Set.range natChain) :=
  ⟨Chain.isLUB_unique, nat_not_bddAbove⟩

/-- Proposition 2 (Monotonicity of lubs, p. 15): if `dₙ ⊑ eₙ` for all `n` then
`⨆ₙ dₙ ⊑ ⨆ₙ eₙ`, provided they exist. -/
theorem proposition2 [PartialOrder D] {d e : Chain D} {a b : D} (hle : ∀ n, d n ≤ e n)
    (ha : IsLUB (Set.range d) a) (hb : IsLUB (Set.range e) b) : a ≤ b :=
  Chain.isLUB_mono hle ha hb

/-- Proposition 3 (Discarding elements, p. 15): `⨆_{n ≥ 0} dₙ = ⨆_{n ≥ 0} d_{N+n}`,
provided either exists. -/
theorem proposition3 [PartialOrder D] (d : Chain D) (N : ℕ) {a : D} :
    IsLUB (Set.range fun n => d (N + n)) a ↔ IsLUB (Set.range d) a :=
  Chain.isLUB_drop_iff d N

/-- Proposition 4 (Eventually constant chain, p. 15): if `dₙ = d_N` for all
`n ≥ N`, then `⨆ₙ dₙ = d_N`. -/
theorem proposition4 [PartialOrder D] {d : Chain D} {N : ℕ} (h : ∀ n, N ≤ n → d n = d N) :
    IsLUB (Set.range d) (d N) :=
  Chain.isLUB_of_eventuallyConstant h

/-- Proposition 5 (Diagonalisation, p. 15): for a doubly indexed family with
`m ≤ m' ∧ n ≤ n' ⇒ d_{m,n} ⊑ d_{m',n'}` (†), the lubs of the rows and of the
columns form chains, and `⨆ₘ ⨆ₙ d_{m,n} = ⨆ₖ d_{k,k} = ⨆ₙ ⨆ₘ d_{m,n}`, assuming
the lubs exist. -/
theorem proposition5 [PartialOrder D] (d : ℕ → ℕ → D)
    (hd : ∀ m m' n n', m ≤ m' → n ≤ n' → d m n ≤ d m' n') {r s : ℕ → D} {δ : D}
    (hr : ∀ m, IsLUB (Set.range (d m)) (r m)) (hs : ∀ n, IsLUB (Set.range (d · n)) (s n))
    (hδ : IsLUB (Set.range fun k => d k k) δ) :
    Monotone r ∧ Monotone s ∧ IsLUB (Set.range r) δ ∧ IsLUB (Set.range s) δ :=
  let d' : ℕ →o ℕ →o D :=
    ⟨fun m => ⟨d m, fun _ _ h => hd _ _ _ _ le_rfl h⟩, fun _ _ h _ => hd _ _ _ _ h le_rfl⟩
  ⟨Chain.row_lub_mono d' hr, Chain.row_lub_mono (Chain.swap d') hs,
    Chain.isLUB_diag d' hr hδ, Chain.isLUB_diag (Chain.swap d') hs hδ⟩

/-! ## §2.4 Complete partial orders and domains -/

/-- Definition 7 (Cpos, p. 16): a poset in which every chain has a lub. -/
abbrev definition7 (D : Type u) : Type u := OmegaCompletePartialOrder D

/-- Definition 7: every chain of a cpo has a lub, and a poset in which every
chain has a lub is a cpo. -/
example [OmegaCompletePartialOrder D] (c : Chain D) : IsLUB (Set.range c) (ωSup c) :=
  isLUB_range_ωSup c

noncomputable example [PartialOrder D] (h : ∀ c : Chain D, ∃ a, IsLUB (Set.range c) a) :
    definition7 D :=
  ofChainComplete h

/-- Definition 8 (Domain, p. 17): a cpo with a least element. -/
abbrev definition8 : Type (u + 1) := DomainCat.{u}

example (D : definition8.{u}) (d : D) : ⊥ ≤ d := bot_le

/-- Example 4 (Domain of partial functions, p. 17): `⊥` is the totally
undefined function, and the lub of `f₀ ⊑ f₁ ⊑ …` is defined at `x` with value
`y` iff some `fₙ` is. -/
theorem example4 {X Y : Type*} (c : Chain (X → Part Y)) (x : X) (y : Y) :
    (⊥ : X → Part Y) x = Part.none ∧ (y ∈ ωSup c x ↔ ∃ n, y ∈ c n x) :=
  ⟨partialFun_bot_apply x, partialFun_mem_ωSup⟩

/-- Example 5 (Finite cpos, p. 17): every chain in a finite poset has a lub. -/
theorem example5 [PartialOrder D] [Finite D] (c : Chain D) : ∃ a, IsLUB (Set.range c) a :=
  let ⟨_, h⟩ := Chain.eventuallyConstant_of_finite c
  ⟨_, Chain.isLUB_of_eventuallyConstant h⟩

/-- Example 5 (p. 17): the finite cpo with two incomparable minimal elements
below a top element has no least element. -/
theorem example5_wedge : ¬ ∃ b : Wedge, IsLeast Set.univ b := wedge_not_isLeast

/-- Example 6 (Flat natural numbers, p. 18): in `ℕ⊥`, `x ⊑ y` iff `x = ⊥` or
`x = y`. -/
theorem example6 {x y : Part ℕ} : x ≤ y ↔ x = ⊥ ∨ x = y := Flat.le_iff_eq_none_or_eq

/-- Example 6 (p. 18): a partial function `X ⇀ ℕ` is the same as a monotone
function from the discrete poset `(X, =)` to `ℕ⊥`. -/
def example6_partialFun (X : Type*) : (X → Part ℕ) ≃ (Discrete X →o Part ℕ) :=
  Flat.partialFunEquiv

/-- Example 7 (Non-example: natural numbers, p. 18): the chain `0 ≤ 1 ≤ 2 ≤ …`
has no upper bound in `ℕ`, so `ℕ` is not a cpo. -/
theorem example7 : ¬ BddAbove (Set.range natChain) := nat_not_bddAbove

/-- Example 8 ('Vertical' extended natural numbers, p. 18): in `Ω = ω + 1` the
chain `0 ⊑ 1 ⊑ 2 ⊑ …` has lub `ω`. -/
theorem example8 : ωSup omegaChain = ⊤ := ωSup_omegaChain

/-- Example 9 (Non-example: no least upper bound, p. 18): with two upper bounds
`ω₁` and `ω₂` adjoined to `ℕ`, the chain `0 ⊑ 1 ⊑ 2 ⊑ …` has both as upper
bounds but no lub. -/
theorem example9 :
    (∀ b, TwoTops.top b ∈ upperBounds (Set.range twoTopsChain)) ∧
      ¬ ∃ a, IsLUB (Set.range twoTopsChain) a :=
  ⟨TwoTops.top_mem_upperBounds, twoTops_no_lub⟩

/-! ## §2.5 Continuous functions -/

/-- Definition 9 (Continuity, p. 19). -/
abbrev definition9 [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E] (f : D → E) :
    Prop :=
  ωScottContinuous f

/-- Definition 9: `f` is continuous iff it is monotone and `f(⨆ₙ dₙ) = ⨆ₙ f(dₙ)`. -/
example [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E] (f : D → E) :
    definition9 f ↔ ∃ hf : Monotone f, ∀ c : Chain D, f (ωSup c) = ωSup (c.map ⟨f, hf⟩) :=
  ωScottContinuous_iff

/-- Definition 10 (Strictness, p. 19): `f(⊥) = ⊥`. -/
abbrev definition10 [Bot D] [Bot E] (f : D → E) : Prop := Strict f

example [Bot D] [Bot E] (f : D → E) : definition10 f ↔ f ⊥ = ⊥ := Iff.rfl

/-- Remark 2 (p. 19): for monotone `f`, `⨆ₙ f(dₙ) ⊑ f(⨆ₙ dₙ)`, so continuity
only needs the converse inequality. -/
theorem remark2 [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E] {f : D → E}
    (hf : Monotone f) :
    (∀ c : Chain D, ωSup (c.map ⟨f, hf⟩) ≤ f (ωSup c)) ∧
      ((∀ c : Chain D, f (ωSup c) ≤ ωSup (c.map ⟨f, hf⟩)) → ωScottContinuous f) :=
  ⟨ωSup_map_le_of_monotone hf, ωScottContinuous_of_le hf⟩

/-- Example 10 (Constant functions, p. 20). -/
theorem example10 [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E] (e : E) :
    ωScottContinuous fun _ : D => e :=
  ωScottContinuous_const e

/-- Example 11 (p. 20): `F_{b,c}` on `State ⇀ State` is continuous. -/
theorem example11 {L : Type*} (b : Imp.State L → Bool) (c : Imp.State L → Part (Imp.State L)) :
    ωScottContinuous (Imp.whileFun b c) :=
  Imp.ωScottContinuous_whileFun b c

/-- Example 12 (Non-example, p. 20): `f : Ω → Ω` with `f(n) = 0` and
`f(ω) = ω` is monotone and strict, but not continuous. -/
theorem example12 :
    (∀ n : ℕ, collapse n = 0) ∧ collapse ⊤ = ⊤ ∧ Monotone collapse ∧ Strict collapse ∧
      ¬ ωScottContinuous collapse :=
  ⟨fun n => by simp [collapse], by simp [collapse], collapse_monotone, collapse_strict,
    collapse_not_continuous⟩

/-! ## §2.6 Kleene's fixed point theorem -/

/-- Theorem 6 (Kleene's fixed point theorem, p. 21): a continuous `f : D → D`
on a domain has a least pre-fixed point, `fix(f) = ⨆ₙ fⁿ(⊥)`. By Proposition 1
it is also the least fixed point. -/
theorem theorem6 [OmegaCompletePartialOrder D] [OrderBot D] (f : D →𝒄 D) :
    (∀ n, kleeneChain f n = f^[n] ⊥) ∧ fix f = ωSup (kleeneChain f) ∧
      IsLeastPrefixedPoint f (fix f) ∧ IsLeast (Function.fixedPoints f) (fix f) :=
  ⟨kleeneChain_apply (f : D →o D), rfl, isLeastPrefixedPoint_fix f, isLeast_fixedPoints_fix f⟩

/-- Example 13 (p. 22): `F_{⟦B⟧,⟦C⟧}` is continuous, and
`⟦while B do C⟧ = fix(F_{⟦B⟧,⟦C⟧})` is its least fixed point. -/
theorem example13 {L : Type*} [DecidableEq L] (b : Imp.Bexp L) (c : Imp.Prog L) :
    Imp.Prog.denote (.while b c) = fix (Imp.F b.denote c.denote) ∧
      IsLeast (Function.fixedPoints (Imp.F b.denote c.denote)) (Imp.Prog.denote (.while b c)) :=
  ⟨Imp.denote_while b c, Imp.isLeast_denote_while b c⟩

/-! ## §2.7 Exercises -/

/-- Exercise 1 (p. 22): the claims of Examples 1 and 4: `X ⇀ Y` is a poset
under graph inclusion, the pointwise union is the lub of a chain, and the
totally undefined function is least. -/
theorem exercise1 {X Y : Type*} :
    (∀ f g : X → Part Y, f ≤ g ↔ graph f ⊆ graph g) ∧
      (∀ (c : Chain (X → Part Y)) x y, y ∈ ωSup c x ↔ ∃ n, y ∈ c n x) ∧
      ∀ f : X → Part Y, ⊥ ≤ f :=
  ⟨fun _ _ => partialFun_le_iff, fun _ _ _ => partialFun_mem_ωSup, fun _ => bot_le⟩

/-- Exercise 2 (p. 22): Remark 1 (iv) and Propositions 2–4 (see `remark1`,
`proposition2`, `proposition3` and `proposition4`), phrased in a cpo. -/
theorem exercise2 [OmegaCompletePartialOrder D] (c c' : Chain D) (N : ℕ) :
    (∀ a, IsLUB (Set.range c) a → a = ωSup c) ∧
      ((∀ n, c n ≤ c' n) → ωSup c ≤ ωSup c') ∧ ωSup (Chain.drop c N) = ωSup c ∧
      ((∀ n, N ≤ n → c n = c N) → ωSup c = c N) :=
  ⟨fun _ h => remark1.1 h (isLUB_range_ωSup c),
    fun h => ωSup_le _ _ fun n => (h n).trans (le_ωSup c' n), Chain.ωSup_drop c N,
    Chain.ωSup_eq_of_eventuallyConstant⟩

/-- Exercise 3 (p. 22): `F_{b,c}` is monotone and continuous. It is strict
exactly when `b` holds everywhere (here `b` is total, since Imp's expressions
always terminate). -/
theorem exercise3 {L : Type*} (b : Imp.State L → Bool) (c : Imp.State L → Part (Imp.State L)) :
    Monotone (Imp.whileFun b c) ∧ ωScottContinuous (Imp.whileFun b c) ∧
      (Strict (Imp.F b c) ↔ ∀ s, b s = true) :=
  ⟨Imp.whileFun_monotone b c, Imp.ωScottContinuous_whileFun b c, Imp.strict_F_iff b c⟩

end Silmaril.Courses.Cambridge.DenotationalSemantics.LeastFixedPoints

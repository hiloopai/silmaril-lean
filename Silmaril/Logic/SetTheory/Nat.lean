module

public import Mathlib.SetTheory.ZFC.Ordinal

@[expose] public section

/-!
# The natural numbers in `ZFSet`

The von Neumann numerals are `0 = ∅` and `n + 1 = suc n`, where the successor
`suc x = x ∪ {x}` (set.mm's `df-suc`) is `insert x x`. The members of Mathlib's
`ZFSet.omega` are exactly the numerals (`mem_omega_iff`), `omega` is the least
set containing `∅` and closed under successor (`omega_subset_of_inductive`),
and induction over `omega` follows (`omega_induction`). The successor is
injective and never empty, so `omega` satisfies Peano's axioms.

For interpreting arithmetic in set theory, addition and multiplication are
characterized as graphs: sets of Kuratowski pairs `⟨⟨m, n⟩, k⟩` that are
functions `ω × ω → ω` satisfying the recursion equations

* `m + 0 = m` and `m + suc n = suc (m + n)` (`IsAddGraph`),
* `m · 0 = 0` and `m · suc n = m · n + m` (`IsMulGraph`, relative to an
  addition graph).

Each characterization has exactly one solution (`existsUnique_isAddGraph`,
`existsUnique_isMulGraph`), and on numerals the solutions compute `Nat.add` and
`Nat.mul` (`pair_mem_addGraph`, `pair_mem_mulGraph`).
-/

namespace Silmaril.Logic.SetTheory

universe u

open ZFSet

/-- The successor `suc x = x ∪ {x}`. -/
def succ (x : ZFSet.{u}) : ZFSet.{u} := insert x x

theorem mem_succ {x y : ZFSet.{u}} : y ∈ succ x ↔ y = x ∨ y ∈ x := mem_insert_iff

theorem self_mem_succ (x : ZFSet.{u}) : x ∈ succ x := mem_insert x x

theorem succ_ne_empty (x : ZFSet.{u}) : succ x ≠ ∅ := fun h =>
  notMem_empty x (h ▸ self_mem_succ x)

/-- The successor is injective, by regularity. -/
theorem succ_injective : Function.Injective (succ : ZFSet.{u} → ZFSet.{u}) := by
  intro x y h
  have hx : x ∈ succ y := h ▸ self_mem_succ x
  have hy : y ∈ succ x := h.symm ▸ self_mem_succ y
  rcases mem_succ.1 hx with hxy | hxy
  · exact hxy
  · rcases mem_succ.1 hy with hyx | hyx
    · exact hyx.symm
    · exact absurd hyx (mem_asymm hxy)

/-- The von Neumann numeral of a natural number. -/
def numeral : ℕ → ZFSet.{u}
  | 0 => ∅
  | n + 1 => succ (numeral n)

@[simp] theorem numeral_zero : numeral.{u} 0 = ∅ := rfl

@[simp] theorem numeral_succ (n : ℕ) : numeral.{u} (n + 1) = succ (numeral n) := rfl

theorem mk_ofNat (n : ℕ) : ZFSet.mk (PSet.ofNat.{u} n) = numeral n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n)) = _
    rw [ih]
    rfl

/-- The members of `omega` are exactly the numerals. -/
theorem mem_omega_iff {x : ZFSet.{u}} : x ∈ omega ↔ ∃ n, numeral n = x := by
  induction x using Quotient.inductionOn with | h p =>
  change ZFSet.mk p ∈ ZFSet.mk PSet.omega ↔ _
  rw [mk_mem_iff, PSet.mem_def]
  constructor
  · rintro ⟨⟨n⟩, h⟩
    exact ⟨n, (mk_ofNat n).symm.trans (ZFSet.sound h).symm⟩
  · rintro ⟨n, h⟩
    exact ⟨⟨n⟩, ZFSet.exact (h.symm.trans (mk_ofNat n).symm)⟩

/-- The members of `omega` are exactly the classes of Mathlib's numerals `PSet.ofNat n`. -/
theorem mem_omega_iff_mk_ofNat {x : ZFSet.{u}} :
    x ∈ omega ↔ ∃ n, ZFSet.mk (PSet.ofNat n) = x := by
  simp only [mk_ofNat, mem_omega_iff]

theorem numeral_mem_omega (n : ℕ) : numeral.{u} n ∈ omega := mem_omega_iff.2 ⟨n, rfl⟩

theorem succ_mem_omega {x : ZFSet.{u}} (h : x ∈ omega) : succ x ∈ omega := omega_succ h

/-- The members of a numeral are the smaller numerals. -/
theorem mem_numeral {x : ZFSet.{u}} {n : ℕ} : x ∈ numeral n ↔ ∃ m < n, numeral m = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [numeral_succ, mem_succ, ih]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n, n.lt_succ_self, rfl⟩
      · exact ⟨m, hm.trans n.lt_succ_self, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
      · exact .inr ⟨m, hm, rfl⟩
      · exact .inl rfl

theorem numeral_mem_numeral_of_lt {m n : ℕ} (h : m < n) : numeral.{u} m ∈ numeral n :=
  mem_numeral.2 ⟨m, h, rfl⟩

theorem numeral_injective : Function.Injective numeral.{u} := by
  intro m n h
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · exact absurd (h ▸ numeral_mem_numeral_of_lt hmn) (mem_irrefl _)
  · exact hmn
  · exact absurd (h ▸ numeral_mem_numeral_of_lt hmn) (mem_irrefl _)

@[simp] theorem numeral_inj {m n : ℕ} : numeral.{u} m = numeral n ↔ m = n :=
  numeral_injective.eq_iff

@[simp] theorem numeral_mem_numeral {m n : ℕ} : numeral.{u} m ∈ numeral n ↔ m < n :=
  ⟨fun h => by
    obtain ⟨k, hk, e⟩ := mem_numeral.1 h
    exact numeral_injective e ▸ hk, numeral_mem_numeral_of_lt⟩

@[simp] theorem numeral_subset_numeral {m n : ℕ} : numeral.{u} m ⊆ numeral n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hmn
    exact mem_irrefl _ (h (numeral_mem_numeral_of_lt (Nat.lt_of_not_le hmn)))
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := mem_numeral.1 hx
    exact numeral_mem_numeral_of_lt (hk.trans_le h)

/-- `omega` is the least set containing `∅` and closed under successor. -/
theorem omega_subset_of_inductive {y : ZFSet.{u}} (h0 : ∅ ∈ y) (hs : ∀ x ∈ y, succ x ∈ y) :
    omega ⊆ y := by
  intro x hx
  obtain ⟨n, rfl⟩ := mem_omega_iff.1 hx
  induction n with
  | zero => exact h0
  | succ n ih => exact hs _ (ih (numeral_mem_omega n))

/-- Induction over `omega`. -/
theorem omega_induction {P : ZFSet.{u} → Prop} (h0 : P ∅) (hs : ∀ x ∈ omega, P x → P (succ x))
    {x : ZFSet.{u}} (hx : x ∈ omega) : P x := by
  obtain ⟨n, rfl⟩ := mem_omega_iff.1 hx
  clear hx
  induction n with
  | zero => exact h0
  | succ n ih => exact hs _ (numeral_mem_omega n) ih

/-- `omega` is transitive. -/
theorem omega_isTransitive : IsTransitive (omega : ZFSet.{u}) := by
  intro x hx y hy
  obtain ⟨n, rfl⟩ := mem_omega_iff.1 hx
  obtain ⟨m, -, rfl⟩ := mem_numeral.1 hy
  exact numeral_mem_omega m

/-! ### Graphs of arithmetic operations -/

/-- The graph `{⟨⟨m, n⟩, f m n⟩}` of a binary operation on numerals. -/
noncomputable def graph (f : ℕ → ℕ → ℕ) : ZFSet.{u} :=
  range fun p : ULift.{u} (ℕ × ℕ) =>
    pair (pair (numeral p.down.1) (numeral p.down.2)) (numeral (f p.down.1 p.down.2))

theorem mem_graph {f : ℕ → ℕ → ℕ} {z : ZFSet.{u}} :
    z ∈ graph f ↔ ∃ m n, pair (pair (numeral m) (numeral n)) (numeral (f m n)) = z := by
  simp only [graph, mem_range]
  exact ⟨fun ⟨⟨m, n⟩, h⟩ => ⟨m, n, h⟩, fun ⟨m, n, h⟩ => ⟨⟨m, n⟩, h⟩⟩

theorem pair_mem_graph_iff {f : ℕ → ℕ → ℕ} {m n : ℕ} {k : ZFSet.{u}} :
    pair (pair (numeral m) (numeral n)) k ∈ graph f ↔ k = numeral (f m n) := by
  rw [mem_graph]
  constructor
  · rintro ⟨m', n', h⟩
    simp only [pair_inj, numeral_inj] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  · rintro rfl
    exact ⟨m, n, rfl⟩

@[simp] theorem pair_mem_graph {f : ℕ → ℕ → ℕ} {m n k : ℕ} :
    pair (pair (numeral.{u} m) (numeral n)) (numeral k) ∈ graph f ↔ k = f m n := by
  rw [pair_mem_graph_iff, numeral_inj]

/-- The graph of a binary operation on numerals is a function `ω × ω → ω`. -/
theorem isFunc_graph (f : ℕ → ℕ → ℕ) : IsFunc (prod omega omega) omega (graph.{u} f) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨m, n, rfl⟩ := mem_graph.1 hz
    exact pair_mem_prod.2 ⟨pair_mem_prod.2 ⟨numeral_mem_omega m, numeral_mem_omega n⟩,
      numeral_mem_omega _⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hz
    obtain ⟨m, rfl⟩ := mem_omega_iff.1 ha
    obtain ⟨n, rfl⟩ := mem_omega_iff.1 hb
    refine ⟨numeral (f m n), pair_mem_graph.2 rfl, fun w hw => ?_⟩
    obtain ⟨m', n', h⟩ := mem_graph.1 hw
    simp only [pair_inj, numeral_inj] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl

/-- A function `ω × ω → ω` containing the graph of `f` on numerals is that graph. -/
theorem eq_graph_of_isFunc {f : ℕ → ℕ → ℕ} {A : ZFSet.{u}}
    (hA : IsFunc (prod omega omega) omega A)
    (hf : ∀ m n, pair (pair (numeral m) (numeral n)) (numeral (f m n)) ∈ A) : A = graph f := by
  ext z
  constructor
  · intro hz
    obtain ⟨p, hp, c, -, rfl⟩ := mem_prod.1 (hA.1 hz)
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hp
    obtain ⟨m, rfl⟩ := mem_omega_iff.1 ha
    obtain ⟨n, rfl⟩ := mem_omega_iff.1 hb
    obtain ⟨w, -, hw⟩ := hA.2 _ hp
    rw [hw c hz, ← hw _ (hf m n)]
    exact pair_mem_graph.2 rfl
  · intro hz
    obtain ⟨m, n, rfl⟩ := mem_graph.1 hz
    exact hf m n

/-- `A` is an addition graph on `ω`: a function `ω × ω → ω` with `m + 0 = m` and
`m + suc n = suc (m + n)`. -/
def IsAddGraph (A : ZFSet.{u}) : Prop :=
  IsFunc (prod omega omega) omega A ∧
    (∀ m ∈ omega, pair (pair m ∅) m ∈ A) ∧
    ∀ m ∈ omega, ∀ n ∈ omega, ∀ k, pair (pair m n) k ∈ A → pair (pair m (succ n)) (succ k) ∈ A

/-- `P` is a multiplication graph on `ω` relative to the addition graph `A`: a function
`ω × ω → ω` with `m · 0 = 0` and `m · suc n = m · n + m`. -/
def IsMulGraph (A P : ZFSet.{u}) : Prop :=
  IsFunc (prod omega omega) omega P ∧
    (∀ m ∈ omega, pair (pair m ∅) ∅ ∈ P) ∧
    ∀ m ∈ omega, ∀ n ∈ omega, ∀ k l, pair (pair m n) k ∈ P → pair (pair k m) l ∈ A →
      pair (pair m (succ n)) l ∈ P

/-- The addition graph. -/
noncomputable abbrev addGraph : ZFSet.{u} := graph (· + ·)

/-- The multiplication graph. -/
noncomputable abbrev mulGraph : ZFSet.{u} := graph (· * ·)

theorem pair_mem_addGraph {m n k : ℕ} :
    pair (pair (numeral.{u} m) (numeral n)) (numeral k) ∈ addGraph ↔ k = m + n :=
  pair_mem_graph

theorem pair_mem_mulGraph {m n k : ℕ} :
    pair (pair (numeral.{u} m) (numeral n)) (numeral k) ∈ mulGraph ↔ k = m * n :=
  pair_mem_graph

theorem isAddGraph_addGraph : IsAddGraph (addGraph.{u}) := by
  refine ⟨isFunc_graph _, fun m hm => ?_, fun m hm n hn k hk => ?_⟩
  · obtain ⟨m, rfl⟩ := mem_omega_iff.1 hm
    exact (pair_mem_addGraph (m := m) (n := 0) (k := m)).2 rfl
  · obtain ⟨m, rfl⟩ := mem_omega_iff.1 hm
    obtain ⟨n, rfl⟩ := mem_omega_iff.1 hn
    rw [pair_mem_graph_iff.1 hk]
    exact (pair_mem_addGraph (m := m) (n := n + 1) (k := m + n + 1)).2 rfl

theorem pair_mem_graph_of_isAddGraph {A : ZFSet.{u}} (hA : IsAddGraph A) (m n : ℕ) :
    pair (pair (numeral m) (numeral n)) (numeral (m + n)) ∈ A := by
  induction n with
  | zero => exact hA.2.1 _ (numeral_mem_omega m)
  | succ n ih => exact hA.2.2 _ (numeral_mem_omega m) _ (numeral_mem_omega n) _ ih

/-- The recursion equations determine the addition graph. -/
theorem IsAddGraph.eq_addGraph {A : ZFSet.{u}} (hA : IsAddGraph A) : A = addGraph :=
  eq_graph_of_isFunc hA.1 (pair_mem_graph_of_isAddGraph hA)

/-- There is exactly one addition graph on `ω`. -/
theorem existsUnique_isAddGraph : ∃! A : ZFSet.{u}, IsAddGraph A :=
  ⟨addGraph, isAddGraph_addGraph, fun _ hA => hA.eq_addGraph⟩

theorem isMulGraph_mulGraph : IsMulGraph addGraph (mulGraph.{u}) := by
  refine ⟨isFunc_graph _, fun m hm => ?_, fun m hm n hn k l hk hl => ?_⟩
  · obtain ⟨m, rfl⟩ := mem_omega_iff.1 hm
    exact (pair_mem_mulGraph (m := m) (n := 0) (k := 0)).2 (Nat.mul_zero m).symm
  · obtain ⟨m, rfl⟩ := mem_omega_iff.1 hm
    obtain ⟨n, rfl⟩ := mem_omega_iff.1 hn
    rw [pair_mem_graph_iff.1 hk] at hl
    rw [pair_mem_graph_iff.1 hl]
    exact (pair_mem_mulGraph (m := m) (n := n + 1) (k := m * n + m)).2 (Nat.mul_succ m n).symm

/-- The recursion equations, relative to any addition graph, determine the multiplication
graph. -/
theorem IsMulGraph.eq_mulGraph {A P : ZFSet.{u}} (hA : IsAddGraph A) (hP : IsMulGraph A P) :
    P = mulGraph := by
  refine eq_graph_of_isFunc hP.1 fun m n => ?_
  induction n with
  | zero => exact hP.2.1 _ (numeral_mem_omega m)
  | succ n ih =>
    exact hP.2.2 _ (numeral_mem_omega m) _ (numeral_mem_omega n) _ _ ih
      (pair_mem_graph_of_isAddGraph hA _ _)

/-- There is exactly one multiplication graph on `ω` relative to the addition graph. -/
theorem existsUnique_isMulGraph : ∃! P : ZFSet.{u}, IsMulGraph addGraph P :=
  ⟨mulGraph, isMulGraph_mulGraph, fun _ hP => hP.eq_mulGraph isAddGraph_addGraph⟩

end Silmaril.Logic.SetTheory

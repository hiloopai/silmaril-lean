module

public import Silmaril.Logic.Metamath.SecondOrder.Semantics

@[expose] public section

/-!
# Validity of the axioms of second-order arithmetic in ω-models

The semantic content of each axiom of `z2.mm`, stated with the operations of
`Silmaril.Logic.Metamath.SecondOrder.Sem` for arbitrary names and values:
the predicate calculus of both sorts and its definitions, the equality and
basic axioms, induction, and the comprehension, Δ⁰₁-comprehension and Σ⁰₁
separation schemes. Disjoint-variable conditions become hypotheses that a
formula or term ignores a name, or that two names are distinct.

Everything except the comprehension schemes is valid in every ω-model. A
comprehension scheme is valid when `𝒮` contains the sets it defines
(`valid_comp`, `valid_dcomp`, `valid_sep`); in the full model it always
does.
-/

namespace Silmaril.Logic.Metamath.SecondOrder.Sem

open Function

variable {𝒮 : Set (Set ℕ)} {N : Type}

/-! ## Propositional calculus -/

theorem valid_mp {φ ψ : Env 𝒮 N → Prop} (h₁ : Valid φ) (h₂ : Valid (imp φ ψ)) : Valid ψ :=
  fun ρ => h₂ ρ (h₁ ρ)

theorem valid_ax1 (φ ψ : Env 𝒮 N → Prop) : Valid (imp φ (imp ψ φ)) := fun _ h _ => h

theorem valid_ax2 (φ ψ χ : Env 𝒮 N → Prop) :
    Valid (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ))) :=
  fun _ h₁ h₂ h₃ => h₁ h₃ (h₂ h₃)

theorem valid_ax3 (φ ψ : Env 𝒮 N → Prop) : Valid (imp (imp (not φ) (not ψ)) (imp ψ φ)) :=
  fun _ h hψ => Classical.byContradiction fun hφ => h hφ hψ

theorem valid_dfBi1 (φ ψ : Env 𝒮 N → Prop) : Valid (imp (iff φ ψ) (imp φ ψ)) :=
  fun _ h => h.1

theorem valid_dfBi2 (φ ψ : Env 𝒮 N → Prop) : Valid (imp (iff φ ψ) (imp ψ φ)) :=
  fun _ h => h.2

theorem valid_dfBi3 (φ ψ : Env 𝒮 N → Prop) : Valid (imp (imp φ ψ) (imp (imp ψ φ) (iff φ ψ))) :=
  fun _ h₁ h₂ => ⟨h₁, h₂⟩

theorem valid_dfAn (φ ψ : Env 𝒮 N → Prop) : Valid (iff (and φ ψ) (not (imp φ (not ψ)))) :=
  fun _ => ⟨fun h h' => h' h.1 h.2, fun h => by
    by_contra hn
    exact h fun hφ hψ => hn ⟨hφ, hψ⟩⟩

/-! ## Equality -/

theorem valid_eqS (a b : Env 𝒮 N → ℕ) : Valid (imp (eq a b) (eq (succ a) (succ b))) :=
  fun _ h => congrArg (· + 1) h

theorem valid_eqpl1 (a b c : Env 𝒮 N → ℕ) : Valid (imp (eq a b) (eq (add a c) (add b c))) :=
  fun _ h => congrArg (· + _) h

theorem valid_eqpl2 (a b c : Env 𝒮 N → ℕ) : Valid (imp (eq a b) (eq (add c a) (add c b))) :=
  fun _ h => congrArg (_ + ·) h

theorem valid_eqmu1 (a b c : Env 𝒮 N → ℕ) : Valid (imp (eq a b) (eq (mul a c) (mul b c))) :=
  fun _ h => congrArg (· * _) h

theorem valid_eqmu2 (a b c : Env 𝒮 N → ℕ) : Valid (imp (eq a b) (eq (mul c a) (mul c b))) :=
  fun _ h => congrArg (_ * ·) h

theorem valid_eqlt1 (a b c : Env 𝒮 N → ℕ) : Valid (imp (eq a b) (imp (lt a c) (lt b c))) :=
  fun ρ (h : a ρ = b ρ) (h' : a ρ < c ρ) => (h ▸ h' : b ρ < c ρ)

theorem valid_eqlt2 (a b c : Env 𝒮 N → ℕ) : Valid (imp (eq a b) (imp (lt c a) (lt c b))) :=
  fun ρ (h : a ρ = b ρ) (h' : c ρ < a ρ) => (h ▸ h' : c ρ < b ρ)

theorem valid_eqel1 (a b : Env 𝒮 N → ℕ) (X : N) :
    Valid (imp (eq a b) (imp (mem a X) (mem b X))) :=
  fun ρ (h : a ρ = b ρ) (h' : a ρ ∈ (ρ (.inr X)).1) => (h ▸ h' : b ρ ∈ (ρ (.inr X)).1)

theorem valid_eqel2 (X Y : N) (a : Env 𝒮 N → ℕ) :
    Valid (imp (seq X Y) (imp (mem a X) (mem a Y))) :=
  fun ρ h h' => by
    simp only [mem, seq] at h h' ⊢
    rw [← h]
    exact h'

/-! ## Basic axioms of arithmetic -/

theorem valid_S0 (a : Env 𝒮 N → ℕ) : Valid (not (eq (succ a) zero)) :=
  fun _ h => Nat.succ_ne_zero _ h

theorem valid_Sinj (a b : Env 𝒮 N → ℕ) : Valid (imp (eq (succ a) (succ b)) (eq a b)) :=
  fun _ h => Nat.succ.inj h

theorem valid_pl0 (a : Env 𝒮 N → ℕ) : Valid (eq (add a zero) a) := fun _ => Nat.add_zero _

theorem valid_plS (a b : Env 𝒮 N → ℕ) : Valid (eq (add a (succ b)) (succ (add a b))) :=
  fun _ => rfl

theorem valid_mu0 (a : Env 𝒮 N → ℕ) : Valid (eq (mul a zero) zero) := fun _ => Nat.mul_zero _

theorem valid_muS (a b : Env 𝒮 N → ℕ) : Valid (eq (mul a (succ b)) (add (mul a b) a)) :=
  fun _ => rfl

theorem valid_lt0 (a : Env 𝒮 N → ℕ) : Valid (not (lt a zero)) := fun _ => Nat.not_lt_zero _

theorem valid_ltS (a b : Env 𝒮 N → ℕ) :
    Valid (iff (lt a (succ b)) (imp (not (lt a b)) (eq a b))) := by
  intro ρ
  simp only [iff, lt, succ, imp, not, eq]
  omega

variable [DecidableEq N]

section Update

theorem update_inl_inr (ρ : Env 𝒮 N) (x X : N) (n : Val 𝒮 N (.inl x)) :
    update ρ (.inl x) n (.inr X) = ρ (.inr X) :=
  update_of_ne Sum.inr_ne_inl _ _

theorem update_inr_inl (ρ : Env 𝒮 N) (x X : N) (A : Val 𝒮 N (.inr X)) :
    update ρ (.inr X) A (.inl x) = ρ (.inl x) :=
  update_of_ne Sum.inl_ne_inr _ _

theorem update_inl_ne (ρ : Env 𝒮 N) {x y : N} (h : y ≠ x) (n : Val 𝒮 N (.inl x)) :
    update ρ (.inl x) n (.inl y) = ρ (.inl y) :=
  update_of_ne (fun e => h (Sum.inl_injective e)) _ _

theorem update_inr_ne (ρ : Env 𝒮 N) {X Y : N} (h : Y ≠ X) (A : Val 𝒮 N (.inr X)) :
    update ρ (.inr X) A (.inr Y) = ρ (.inr Y) :=
  update_of_ne (fun e => h (Sum.inr_injective e)) _ _

end Update

/-! ## Quantifiers over numbers -/

theorem valid_gen {φ : Env 𝒮 N → Prop} (x : N) (h : Valid φ) : Valid (all x φ) :=
  fun _ _ => h _

theorem valid_ax4 (x : N) (φ ψ : Env 𝒮 N → Prop) :
    Valid (imp (all x (imp φ ψ)) (imp (all x φ) (all x ψ))) :=
  fun _ h₁ h₂ n => h₁ n (h₂ n)

theorem valid_ax5 {x : N} {φ : Env 𝒮 N → Prop} (h : Ignores φ (.inl x)) :
    Valid (imp φ (all x φ)) :=
  fun ρ hφ n => (h ρ n).symm ▸ hφ

theorem valid_ax6 (x y : N) : Valid (not (all x (not (eq (var (𝒮 := 𝒮) x) (var y))))) := by
  intro ρ h
  by_cases hxy : y = x
  · subst hxy
    exact h 0 rfl
  · refine h (ρ (.inl y)) ?_
    simp only [eq, var, update_self, update_inl_ne ρ hxy]

omit [DecidableEq N] in
theorem valid_ax7 (a b c : Env 𝒮 N → ℕ) : Valid (imp (eq a b) (imp (eq a c) (eq b c))) :=
  fun ρ (h₁ : a ρ = b ρ) (h₂ : a ρ = c ρ) => (h₁ ▸ h₂ : b ρ = c ρ)

theorem valid_ax10 (x : N) (φ : Env 𝒮 N → Prop) :
    Valid (imp (not (all x φ)) (all x (not (all x φ)))) :=
  fun _ h n h' => h fun m => by simpa only [update_idem] using h' m

theorem valid_ax11 (x y : N) (φ : Env 𝒮 N → Prop) :
    Valid (imp (all x (all y φ)) (all y (all x φ))) := by
  intro ρ h m n
  by_cases hxy : x = y
  · subst hxy
    simpa only [update_idem] using h m n
  · have hne : (Sum.inl x : N ⊕ N) ≠ .inl y := fun e => hxy (Sum.inl_injective e)
    have := h n m
    rwa [update_comm hne] at this

theorem valid_ax12 (x y : N) (φ : Env 𝒮 N → Prop) :
    Valid (imp (eq (var x) (var y)) (imp (all y φ) (all x (imp (eq (var x) (var y)) φ)))) := by
  intro ρ hxy h n hn
  by_cases e : y = x
  · subst e
    exact h n
  · simp only [eq, var, update_self, update_inl_ne ρ e] at hn hxy
    subst hn
    have hρ : update ρ (.inl x) (ρ (.inl y)) = ρ := by
      rw [← hxy]
      exact update_eq_self _ _
    have := h (ρ (.inl y))
    rwa [show update ρ (.inl y) (ρ (.inl y)) = ρ from update_eq_self _ _, ← hρ] at this

theorem valid_ax13 (x y z : N) :
    Valid (imp (not (eq (var (𝒮 := 𝒮) x) (var y))) (imp (eq (var y) (var z))
      (all x (eq (var y) (var z))))) := by
  intro ρ h₁ h₂ n
  simp only [not, eq, var] at h₁ h₂ ⊢
  by_cases hy : y = x
  · subst hy
    exact absurd rfl h₁
  by_cases hz : z = x
  · subst hz
    exact absurd h₂.symm h₁
  rw [update_inl_ne ρ hy, update_inl_ne ρ hz]
  exact h₂

theorem valid_tex {x : N} {a : Env 𝒮 N → ℕ} (h : Ignores a (.inl x)) :
    Valid (not (all x (not (eq (var x) a)))) := fun ρ h' =>
  h' (a ρ) (by simp only [eq, var, update_self, h ρ])

theorem valid_dfEx (x : N) (φ : Env 𝒮 N → Prop) :
    Valid (iff (ex x φ) (not (all x (not φ)))) :=
  fun _ => ⟨fun ⟨n, h⟩ h' => h' n h, fun h => by
    by_contra hn
    exact h fun n hφ => hn ⟨n, hφ⟩⟩

/-! ## Quantifiers over sets -/

theorem valid_sgen {φ : Env 𝒮 N → Prop} (X : N) (h : Valid φ) : Valid (sall X φ) :=
  fun _ _ => h _

theorem valid_s4 (X : N) (φ ψ : Env 𝒮 N → Prop) :
    Valid (imp (sall X (imp φ ψ)) (imp (sall X φ) (sall X ψ))) :=
  fun _ h₁ h₂ A => h₁ A (h₂ A)

theorem valid_s5 {X : N} {φ : Env 𝒮 N → Prop} (h : Ignores φ (.inr X)) :
    Valid (imp φ (sall X φ)) :=
  fun ρ hφ A => (h ρ A).symm ▸ hφ

theorem valid_s6 (X Y : N) : Valid (not (sall X (not (seq (𝒮 := 𝒮) X Y)))) := by
  intro ρ h
  by_cases hXY : Y = X
  · subst hXY
    exact h (ρ (.inr Y)) rfl
  · refine h (ρ (.inr Y)) ?_
    simp only [seq, update_self, update_inr_ne ρ hXY]

omit [DecidableEq N] in
theorem valid_s7 (X Y Z : N) :
    Valid (imp (seq (𝒮 := 𝒮) X Y) (imp (seq X Z) (seq Y Z))) :=
  fun ρ (h₁ : ρ (.inr X) = ρ (.inr Y)) (h₂ : ρ (.inr X) = ρ (.inr Z)) =>
    (h₁ ▸ h₂ : ρ (.inr Y) = ρ (.inr Z))

theorem valid_s10 (X : N) (φ : Env 𝒮 N → Prop) :
    Valid (imp (not (sall X φ)) (sall X (not (sall X φ)))) :=
  fun _ h A h' => h fun B => by simpa only [update_idem] using h' B

theorem valid_s11 (X Y : N) (φ : Env 𝒮 N → Prop) :
    Valid (imp (sall X (sall Y φ)) (sall Y (sall X φ))) := by
  intro ρ h B A
  by_cases hXY : X = Y
  · subst hXY
    simpa only [update_idem] using h B A
  · have hne : (Sum.inr X : N ⊕ N) ≠ .inr Y := fun e => hXY (Sum.inr_injective e)
    have := h A B
    rwa [update_comm hne] at this

theorem valid_s12 (X Y : N) (φ : Env 𝒮 N → Prop) :
    Valid (imp (seq X Y) (imp (sall Y φ) (sall X (imp (seq X Y) φ)))) := by
  intro ρ hXY h A hA
  by_cases e : Y = X
  · subst e
    exact h A
  · simp only [seq, update_self, update_inr_ne ρ e] at hA hXY
    subst hA
    have hρ : update ρ (.inr X) (ρ (.inr Y)) = ρ := by
      rw [← hXY]
      exact update_eq_self _ _
    have := h (ρ (.inr Y))
    rwa [show update ρ (.inr Y) (ρ (.inr Y)) = ρ from update_eq_self _ _, ← hρ] at this

theorem valid_s13 (X Y Z : N) :
    Valid (imp (not (seq (𝒮 := 𝒮) X Y)) (imp (seq Y Z) (sall X (seq Y Z)))) := by
  intro ρ h₁ h₂ A
  simp only [not, seq] at h₁ h₂ ⊢
  by_cases hY : Y = X
  · subst hY
    exact absurd rfl h₁
  by_cases hZ : Z = X
  · subst hZ
    exact absurd h₂.symm h₁
  rw [update_inr_ne ρ hY, update_inr_ne ρ hZ]
  exact h₂

theorem valid_ns11 (x X : N) (φ : Env 𝒮 N → Prop) :
    Valid (imp (all x (sall X φ)) (sall X (all x φ))) := fun ρ h A n => by
  have := h n A
  rwa [update_comm Sum.inl_ne_inr] at this

theorem valid_sn11 (x X : N) (φ : Env 𝒮 N → Prop) :
    Valid (imp (sall X (all x φ)) (all x (sall X φ))) := fun ρ h n A => by
  have := h A n
  rwa [update_comm Sum.inr_ne_inl] at this

theorem valid_dfSex (X : N) (φ : Env 𝒮 N → Prop) :
    Valid (iff (sex X φ) (not (sall X (not φ)))) :=
  fun _ => ⟨fun ⟨A, h⟩ h' => h' A h, fun h => by
    by_contra hn
    exact h fun A hφ => hn ⟨A, hφ⟩⟩

theorem valid_dfSeq (x X Y : N) :
    Valid (iff (seq (𝒮 := 𝒮) X Y) (all x (iff (mem (var x) X) (mem (var x) Y)))) := by
  intro ρ
  simp only [iff, seq, all, mem, var, update_self, update_inl_inr]
  constructor
  · intro h n
    rw [h]
  · intro h
    exact Subtype.ext (Set.ext h)

/-! ## Induction -/

/-- The induction scheme is valid in every ω-model, for every formula. -/
theorem valid_ind {x y : N} (hxy : x ≠ y) {φ : Env 𝒮 N → Prop} (hy : Ignores φ (.inl y)) :
    Valid (imp (all x (imp (eq (var x) zero) φ))
      (imp (all y (imp (all x (imp (eq (var x) (var y)) φ))
        (all x (imp (eq (var x) (succ (var y))) φ)))) (all x φ))) := by
  intro ρ h₀ hs
  have hyx : y ≠ x := Ne.symm hxy
  have hne : (Sum.inl x : N ⊕ N) ≠ .inl y := fun e => hxy (Sum.inl_injective e)
  have key : ∀ m n, φ (update (update ρ (.inl y) m) (.inl x) n) ↔ φ (update ρ (.inl x) n) :=
    fun m n => by rw [← update_comm hne, hy]
  intro n
  induction n with
  | zero => exact h₀ 0 (by simp only [eq, var, zero, update_self])
  | succ k ih =>
    have := hs k (fun n hn => by
      simp only [eq, var, update_self, update_inl_ne _ hyx] at hn
      rw [key, hn]
      exact ih) (k + 1) (by simp only [eq, var, succ, update_self, update_inl_ne _ hyx])
    exact (key k (k + 1)).1 this

/-! ## Comprehension -/

theorem sex_comp_iff {x X : N} {φ : Env 𝒮 N → Prop} (hφ : Ignores φ (.inr X)) (ρ : Env 𝒮 N) :
    sex X (all x (iff (mem (var x) X) φ)) ρ ↔ {n | φ (update ρ (.inl x) n)} ∈ 𝒮 := by
  simp only [sex, all, iff, mem, var, update_self, update_inl_inr, update_self]
  constructor
  · rintro ⟨A, hA⟩
    have : A.1 = {n | φ (update ρ (.inl x) n)} := Set.ext fun n => by
      rw [hA n, ← update_comm Sum.inl_ne_inr, hφ]
      rfl
    exact this ▸ A.2
  · intro h
    refine ⟨⟨_, h⟩, fun n => ?_⟩
    rw [← update_comm Sum.inl_ne_inr, hφ]
    rfl

/-- Comprehension for `φ` holds when `𝒮` contains every set `φ` defines. -/
theorem valid_comp {x X : N} {φ : Env 𝒮 N → Prop} (hφ : Ignores φ (.inr X))
    (h : ∀ ρ : Env 𝒮 N, {n | φ (update ρ (.inl x) n)} ∈ 𝒮) :
    Valid (sex X (all x (iff (mem (var x) X) φ))) :=
  fun ρ => (sex_comp_iff hφ ρ).2 (h ρ)

/-- Δ⁰₁-comprehension for `φ` and `ψ` holds when `𝒮` contains the sets `φ`
defines where it is equivalent to `ψ`. -/
theorem valid_dcomp {x X : N} {φ ψ : Env 𝒮 N → Prop} (hφ : Ignores φ (.inr X))
    (h : ∀ ρ : Env 𝒮 N, (∀ n, φ (update ρ (.inl x) n) ↔ ψ (update ρ (.inl x) n)) →
      {n | φ (update ρ (.inl x) n)} ∈ 𝒮) :
    Valid (imp (all x (iff φ ψ)) (sex X (all x (iff (mem (var x) X) φ)))) :=
  fun ρ hρ => (sex_comp_iff hφ ρ).2 (h ρ hρ)

/-- Separation for `φ` and `ψ` holds when `𝒮` contains a separating set. -/
theorem valid_sep {x X : N} {φ ψ : Env 𝒮 N → Prop} (hφ : Ignores φ (.inr X))
    (hψ : Ignores ψ (.inr X))
    (h : ∀ ρ : Env 𝒮 N, (∀ n, ¬ (φ (update ρ (.inl x) n) ∧ ψ (update ρ (.inl x) n))) →
      ∃ A ∈ 𝒮, ∀ n, (φ (update ρ (.inl x) n) → n ∈ A) ∧ (ψ (update ρ (.inl x) n) → n ∉ A)) :
    Valid (imp (all x (not (and φ ψ)))
      (sex X (all x (and (imp φ (mem (var x) X)) (imp ψ (not (mem (var x) X))))))) := by
  intro ρ hρ
  obtain ⟨A, hA, hsep⟩ := h ρ hρ
  refine ⟨⟨A, hA⟩, fun n => ?_⟩
  simp only [Sem.and, imp, not, mem, var, update_self, update_inl_inr, update_self]
  rw [← update_comm Sum.inl_ne_inr, hφ, hψ]
  exact hsep n

end Silmaril.Logic.Metamath.SecondOrder.Sem

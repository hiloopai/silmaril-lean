module

public import Silmaril.Logic.SecondOrderArithmetic.Systems
public import Silmaril.Logic.SecondOrderArithmetic.Semantics
public import Silmaril.Logic.SecondOrderArithmetic.Henkin
public import Silmaril.Logic.SecondOrderArithmetic.Defs

/-! Every axiom of every second-order arithmetic subsystem is valid in the full standard model
(ℕ with every subset of ℕ). Proofs for `Silmaril.Logic.SecondOrderArithmetic.FullStandard`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.SecondOrderArithmetic

open Function Silmaril.Logic.SecondOrderArithmetic

variable {N : Type} [DecidableEq N] {𝒮 : Set (Set ℕ)}

theorem term_eval_update_inr (t : Term N) (ρ : Env 𝒮 N) (X : N) (A : ↥𝒮) :
    t.eval (update ρ (.inr X) A) = t.eval ρ := by
  induction t with
  | var y => simp [Term.eval]
  | zero => rfl
  | succ t ih => simp [Term.eval, ih]
  | add t u ih ih' => simp [Term.eval, ih, ih']
  | mul t u ih ih' => simp [Term.eval, ih, ih']

theorem term_eval_update_inl (t : Term N) (ρ : Env 𝒮 N) {x : N} (h : x ∉ t.names) (v : ℕ) :
    t.eval (update ρ (.inl x) v) = t.eval ρ := by
  induction t with
  | var y =>
    have : x ≠ y := by simpa [Term.names] using h
    simp [Term.eval, Ne.symm this]
  | zero => rfl
  | succ t ih => simp [Term.eval, ih (by simpa [Term.names] using h)]
  | add t u ih ih' =>
    simp only [Term.names, Finset.mem_union, not_or] at h
    simp [Term.eval, ih h.1, ih' h.2]
  | mul t u ih ih' =>
    simp only [Term.names, Finset.mem_union, not_or] at h
    simp [Term.eval, ih h.1, ih' h.2]

theorem eval_update_inl : ∀ (φ : Formula N) (ρ : Env 𝒮 N) {x : N} (_ : x ∉ φ.names) (v : ℕ),
    φ.eval (update ρ (.inl x) v) ↔ φ.eval ρ
  | .equal t u, ρ, x, h, v | .less t u, ρ, x, h, v => by
    simp only [Formula.names, Finset.mem_union, not_or] at h
    simp [Formula.eval, term_eval_update_inl t ρ h.1, term_eval_update_inl u ρ h.2]
  | .member t X, ρ, x, h, v => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    simp [Formula.eval, term_eval_update_inl t ρ h.2]
  | .setEqual X Y, ρ, x, h, v => by simp [Formula.eval]
  | .neg φ, ρ, x, h, v => by
    simp only [Formula.names] at h; simp [Formula.eval, eval_update_inl φ ρ h v]
  | .imp φ ψ, ρ, x, h, v | .iff φ ψ, ρ, x, h, v | .conj φ ψ, ρ, x, h, v => by
    simp only [Formula.names, Finset.mem_union, not_or] at h
    simp [Formula.eval, eval_update_inl φ ρ h.1 v, eval_update_inl ψ ρ h.2 v]
  | .all y φ, ρ, x, h, v => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have hxy : (Sum.inl x : N ⊕ N) ≠ .inl y := by simpa using h.1
    exact forall_congr' fun n => by rw [update_comm hxy]; exact eval_update_inl φ _ h.2 v
  | .ex y φ, ρ, x, h, v => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have hxy : (Sum.inl x : N ⊕ N) ≠ .inl y := by simpa using h.1
    exact exists_congr fun n => by rw [update_comm hxy]; exact eval_update_inl φ _ h.2 v
  | .setAll Y φ, ρ, x, h, v => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have hxy : (Sum.inl x : N ⊕ N) ≠ .inr Y := by simp
    exact forall_congr' fun A => by rw [update_comm hxy]; exact eval_update_inl φ _ h.2 v
  | .setEx Y φ, ρ, x, h, v => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have hxy : (Sum.inl x : N ⊕ N) ≠ .inr Y := by simp
    exact exists_congr fun A => by rw [update_comm hxy]; exact eval_update_inl φ _ h.2 v

theorem eval_update_inr : ∀ (φ : Formula N) (ρ : Env 𝒮 N) {X : N} (_ : X ∉ φ.names) (A : ↥𝒮),
    φ.eval (update ρ (.inr X) A) ↔ φ.eval ρ
  | .equal t u, ρ, X, h, A | .less t u, ρ, X, h, A => by
    simp [Formula.eval, term_eval_update_inr]
  | .member t Y, ρ, X, h, A => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have : (Sum.inr Y : N ⊕ N) ≠ .inr X := by simpa using Ne.symm h.1
    simp [Formula.eval, term_eval_update_inr, update_of_ne this]
  | .setEqual Y Z, ρ, X, h, A => by
    simp only [Formula.names, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    have h1 : (Sum.inr Y : N ⊕ N) ≠ .inr X := by simpa using Ne.symm h.1
    have h2 : (Sum.inr Z : N ⊕ N) ≠ .inr X := by simpa using Ne.symm h.2
    simp [Formula.eval, update_of_ne h1, update_of_ne h2]
  | .neg φ, ρ, X, h, A => by
    simp only [Formula.names] at h; simp [Formula.eval, eval_update_inr φ ρ h A]
  | .imp φ ψ, ρ, X, h, A | .iff φ ψ, ρ, X, h, A | .conj φ ψ, ρ, X, h, A => by
    simp only [Formula.names, Finset.mem_union, not_or] at h
    simp [Formula.eval, eval_update_inr φ ρ h.1 A, eval_update_inr ψ ρ h.2 A]
  | .all y φ, ρ, X, h, A => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have hxy : (Sum.inr X : N ⊕ N) ≠ .inl y := by simp
    exact forall_congr' fun n => by rw [update_comm hxy]; exact eval_update_inr φ _ h.2 A
  | .ex y φ, ρ, X, h, A => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have hxy : (Sum.inr X : N ⊕ N) ≠ .inl y := by simp
    exact exists_congr fun n => by rw [update_comm hxy]; exact eval_update_inr φ _ h.2 A
  | .setAll Y φ, ρ, X, h, A => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have hxy : (Sum.inr X : N ⊕ N) ≠ .inr Y := by simpa using h.1
    exact forall_congr' fun B => by rw [update_comm hxy]; exact eval_update_inr φ _ h.2 A
  | .setEx Y φ, ρ, X, h, A => by
    simp only [Formula.names, Finset.mem_insert, not_or] at h
    have hxy : (Sum.inr X : N ⊕ N) ≠ .inr Y := by simpa using h.1
    exact exists_congr fun B => by rw [update_comm hxy]; exact eval_update_inr φ _ h.2 A

/-- Every base axiom holds in every ω-model, at every environment. -/
theorem baseAxiom_valid {p : Formula N} (h : BaseAxiom p) (ρ : Env 𝒮 N) : p.eval ρ := by
  cases h with
  | ax1 | ax2 | ax3 | dfBi1 | dfBi2 | dfBi3 | dfAn => simp only [Formula.eval]; tauto
  | ax4 φ ψ x => simp only [Formula.eval]; exact fun h1 h2 n => h1 n (h2 n)
  | ax5 φ x hx => simp only [Formula.eval]; exact fun h n => (eval_update_inl φ ρ hx n).2 h
  | ax6 x y =>
    simp only [Formula.eval, Term.eval, not_forall, not_not]
    by_cases hxy : x = y
    · subst hxy; exact ⟨0, rfl⟩
    · refine ⟨ρ (.inl y), ?_⟩
      have : (Sum.inl y : N ⊕ N) ≠ .inl x := by simpa using Ne.symm hxy
      simp [update_of_ne this]
  | ax7 t u v => simp only [Formula.eval]; omega
  | ax10 φ x =>
    simp only [Formula.eval]
    intro h n h'
    exact h fun m => by simpa [update_idem] using h' m
  | ax11 φ x y =>
    simp only [Formula.eval]
    intro h m n
    by_cases hxy : x = y
    · subst hxy; simpa [update_idem] using h m n
    · have e : (Sum.inl x : N ⊕ N) ≠ .inl y := by simpa using hxy
      have := h n m; rwa [update_comm e] at this
  | ax12 φ x y =>
    simp only [Formula.eval, Term.eval]
    intro hxy hall n hn
    by_cases h : x = y
    · subst h; simpa using hall n
    · have hne : (Sum.inl y : N ⊕ N) ≠ .inl x := by simpa using Ne.symm h
      rw [update_self, update_of_ne hne] at hn
      have : update ρ (.inl x) n = ρ := by
        rw [show n = ρ (.inl x) by rw [hn, hxy]]; exact update_eq_self _ _
      rw [this]; simpa [update_eq_self] using hall (ρ (.inl y))
  | ax13 x y z =>
    simp only [Formula.eval, Term.eval]
    intro hxy hyz n
    by_cases h1 : x = y
    · subst h1; exact absurd rfl hxy
    by_cases h2 : x = z
    · subst h2; exact absurd hyz.symm (fun h => hxy (h ▸ rfl))
    have e1 : (Sum.inl y : N ⊕ N) ≠ .inl x := by simpa using Ne.symm h1
    have e2 : (Sum.inl z : N ⊕ N) ≠ .inl x := by simpa using Ne.symm h2
    simpa [update_of_ne e1, update_of_ne e2] using hyz
  | axTex x t ht =>
    simp only [Formula.eval, Term.eval, not_forall, not_not]
    exact ⟨t.eval ρ, by simp [term_eval_update_inl t ρ ht]⟩
  | dfEx φ x => simp only [Formula.eval]; exact ⟨fun ⟨n, h⟩ h' => h' n h, fun h => by
      by_contra h'; exact h fun n hn => h' ⟨n, hn⟩⟩
  | axS4 φ ψ X => simp only [Formula.eval]; exact fun h1 h2 A => h1 A (h2 A)
  | axS5 φ X hX => simp only [Formula.eval]; exact fun h A => (eval_update_inr φ ρ hX A).2 h
  | axS6 X Y =>
    simp only [Formula.eval, not_forall, not_not]
    by_cases hXY : X = Y
    · subst hXY; exact ⟨ρ (.inr X), rfl⟩
    · refine ⟨ρ (.inr Y), ?_⟩
      have : (Sum.inr Y : N ⊕ N) ≠ .inr X := by simpa using Ne.symm hXY
      simp [update_of_ne this]
  | axS7 X Y Z => simp only [Formula.eval]; intro h1 h2; exact h1.symm.trans h2
  | axS10 φ X =>
    simp only [Formula.eval]
    intro h A h'
    exact h fun B => by simpa [update_idem] using h' B
  | axS11 φ X Y =>
    simp only [Formula.eval]
    intro h B A
    by_cases hXY : X = Y
    · subst hXY; simpa [update_idem] using h B A
    · have e : (Sum.inr X : N ⊕ N) ≠ .inr Y := by simpa using hXY
      have := h A B; rwa [update_comm e] at this
  | axS12 φ X Y =>
    simp only [Formula.eval]
    intro hXY hall A hA
    by_cases h : X = Y
    · subst h; simpa using hall A
    · have hne : (Sum.inr Y : N ⊕ N) ≠ .inr X := by simpa using Ne.symm h
      rw [update_self, update_of_ne hne] at hA
      have : update ρ (.inr X) A = ρ := by
        rw [show A = ρ (.inr X) by rw [hA, hXY]]; exact update_eq_self _ _
      rw [this]; simpa [update_eq_self] using hall (ρ (.inr Y))
  | axS13 X Y Z =>
    simp only [Formula.eval]
    intro hXY hYZ A
    by_cases h1 : X = Y
    · subst h1; exact absurd rfl hXY
    by_cases h2 : X = Z
    · subst h2; exact absurd hYZ.symm (fun h => hXY (h ▸ rfl))
    have e1 : (Sum.inr Y : N ⊕ N) ≠ .inr X := by simpa using Ne.symm h1
    have e2 : (Sum.inr Z : N ⊕ N) ≠ .inr X := by simpa using Ne.symm h2
    simpa [update_of_ne e1, update_of_ne e2] using hYZ
  | axNs11 φ x X =>
    simp only [Formula.eval]
    intro h A n
    have e : (Sum.inl x : N ⊕ N) ≠ .inr X := by simp
    have := h n A; rwa [update_comm e] at this
  | axSn11 φ x X =>
    simp only [Formula.eval]
    intro h n A
    have e : (Sum.inr X : N ⊕ N) ≠ .inl x := by simp
    have := h A n; rwa [update_comm e] at this
  | dfSex φ X => simp only [Formula.eval]; exact ⟨fun ⟨A, h⟩ h' => h' A h, fun h => by
      by_contra h'; exact h fun A hA => h' ⟨A, hA⟩⟩
  | dfSeq x X Y =>
    simp only [Formula.eval, Term.eval, update_self]
    have e1 : (Sum.inr X : N ⊕ N) ≠ .inl x := by simp
    have e2 : (Sum.inr Y : N ⊕ N) ≠ .inl x := by simp
    simp only [update_of_ne e1, update_of_ne e2]
    constructor
    · intro h n; rw [h]
    · intro h; exact Subtype.ext (Set.ext fun n => h n)
  | axEqS | axEqpl1 | axEqpl2 | axEqmu1 | axEqmu2 =>
    simp only [Formula.eval, Term.eval]; intro h; rw [h]
  | axEqlt1 | axEqlt2 => simp only [Formula.eval]; intro h; rw [h]; exact id
  | axEqel1 X t u => simp only [Formula.eval]; intro h; rw [h]; exact id
  | axEqel2 X Y t => simp only [Formula.eval]; intro h; rw [h]; exact id
  | axS0 t => simp only [Formula.eval, Term.eval]; omega
  | axSinj t u => simp only [Formula.eval, Term.eval]; omega
  | axPl0 t => simp [Formula.eval, Term.eval]
  | axPlS t u => simp only [Formula.eval, Term.eval]; omega
  | axMu0 t => simp [Formula.eval, Term.eval]
  | axMuS t u => simp only [Formula.eval, Term.eval]; exact Nat.mul_succ _ _
  | axLt0 t => simp [Formula.eval, Term.eval]
  | axLtS t u => simp only [Formula.eval, Term.eval]; omega

/-- The induction schema holds in every ω-model. -/
theorem induction_valid {x y : N} {φ : Formula N} (hxy : x ≠ y) (hy : y ∉ φ.names)
    (ρ : Env 𝒮 N) : (Formula.induction x y φ).eval ρ := by
  have exy : (Sum.inl x : N ⊕ N) ≠ .inl y := by simpa using hxy
  have key : ∀ m n, φ.eval (update (update ρ (.inl y) m) (.inl x) n) ↔
      φ.eval (update ρ (.inl x) n) := by
    intro m n; rw [← update_comm exy]; exact eval_update_inl φ _ hy m
  simp only [Formula.induction, Formula.eval, Term.eval, update_self, update_of_ne (Ne.symm exy)]
  intro hbase hstep
  have step : ∀ k : ℕ, φ.eval (update ρ (.inl x) k) → φ.eval (update ρ (.inl x) (k + 1)) :=
    fun k hk => (key k (k + 1)).1
      (hstep k (fun n hn => (key k n).2 (by subst hn; exact hk)) (k + 1) rfl)
  intro n
  induction n with
  | zero => exact hbase 0 rfl
  | succ k ih => exact step k ih

/-- The set of the numbers satisfying `φ` in `x`. -/
def defined (ρ : Env Set.univ N) (x : N) (φ : Formula N) : ↥(Set.univ : Set (Set ℕ)) :=
  ⟨{n | φ.eval (update ρ (.inl x) n)}, trivial⟩

theorem defined_spec {ρ : Env Set.univ N} {x X : N} {φ : Formula N} (hX : X ∉ φ.names) (n : ℕ) :
    φ.eval (update (update ρ (.inr X) (defined ρ x φ)) (.inl x) n) ↔
      n ∈ (defined ρ x φ).val := by
  have e : (Sum.inr X : N ⊕ N) ≠ .inl x := by simp
  rw [update_comm e, eval_update_inr φ _ hX]
  rfl

/-- The comprehension schema holds with every subset of ℕ. -/
theorem comprehension_valid {x X : N} {φ : Formula N} (hX : X ∉ φ.names) (ρ : Env Set.univ N) :
    (Formula.comprehension x X φ).eval ρ := by
  have e : (Sum.inr X : N ⊕ N) ≠ .inl x := by simp
  simp only [Formula.comprehension, Formula.eval, Term.eval, update_self, update_of_ne e]
  exact ⟨defined ρ x φ, fun n => (defined_spec hX n).symm⟩

/-- Separation holds with every subset of ℕ. -/
theorem separation_valid {x X : N} {φ ψ : Formula N} (hφ : X ∉ φ.names) (hψ : X ∉ ψ.names)
    (ρ : Env Set.univ N) : (Formula.separation x X φ ψ).eval ρ := by
  have e : (Sum.inr X : N ⊕ N) ≠ .inl x := by simp
  simp only [Formula.separation, Formula.eval, Term.eval, update_self, update_of_ne e]
  intro hdis
  refine ⟨defined ρ x φ, fun n => ⟨fun h => (defined_spec hφ n).1 h, fun h hn => ?_⟩⟩
  have hφn := (defined_spec hφ n).2 hn
  have e2 : (Sum.inr X : N ⊕ N) ≠ .inl x := by simp
  rw [update_comm e2, eval_update_inr φ _ hφ] at hφn
  rw [update_comm e2, eval_update_inr ψ _ hψ] at h
  exact hdis n ⟨hφn, h⟩

/-- **Every axiom of every subsystem is valid in the full standard model.** -/
theorem validAxioms_fullStandard (S : Subsystem) : ValidAxioms (N := N) S fullStandard := by
  intro p ax ρ
  show p.henkinEval (omegaStructure Set.univ) ρ
  rw [Formula.henkin_omega]
  cases ax with
  | base h => exact baseAxiom_valid h ρ
  | sigmaInd x y φ _ _ hxy hy => exact induction_valid hxy hy ρ
  | fullInd x y φ _ hxy hy => exact induction_valid hxy hy ρ
  | deltaComp x X φ ψ _ _ _ hφ _ => exact fun _ => comprehension_valid hφ ρ
  | sep x X φ ψ _ _ _ hφ hψ => exact separation_valid hφ hψ ρ
  | arithComp x X φ _ _ hX => exact comprehension_valid hX ρ
  | fullComp x X φ _ hX => exact comprehension_valid hX ρ

end Silmaril.Proofs.Logic.SecondOrderArithmetic

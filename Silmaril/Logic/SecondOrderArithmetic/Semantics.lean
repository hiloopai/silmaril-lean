module

public import Silmaril.Logic.SecondOrderArithmetic.Syntax
public import Silmaril.Logic.Metamath.SecondOrder.Model

@[expose] public section

/-! Independent evaluation, with certified realization of the native semantic
term/formula carriers. These results concern denotations, not derivability. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open Function

variable {N : Type} [DecidableEq N] {𝒮 : Set (Set ℕ)}

/-- An ω-environment: standard numbers, and sets from the specified collection.
`𝒮 = Set.univ` gives full standard semantics. General Henkin models may
have nonstandard numbers and are not identified with these ω-models. -/
abbrev Env (𝒮 : Set (Set ℕ)) (N : Type) := Metamath.SecondOrder.Sem.Env 𝒮 N

/-- Evaluation is defined directly by recursion on the independent syntax. -/
def Term.eval : Term N → Env 𝒮 N → ℕ
  | .var x, ρ => ρ (.inl x)
  | .zero, _ => 0
  | .succ t, ρ => t.eval ρ + 1
  | .add t u, ρ => t.eval ρ + u.eval ρ
  | .mul t u, ρ => t.eval ρ * u.eval ρ

def Formula.eval : Formula N → Env 𝒮 N → Prop
  | .equal t u, ρ => t.eval ρ = u.eval ρ
  | .less t u, ρ => t.eval ρ < u.eval ρ
  | .member t X, ρ => t.eval ρ ∈ (ρ (.inr X)).val
  | .setEqual X Y, ρ => ρ (.inr X) = ρ (.inr Y)
  | .neg φ, ρ => ¬ φ.eval ρ
  | .imp φ ψ, ρ => φ.eval ρ → ψ.eval ρ
  | .iff φ ψ, ρ => φ.eval ρ ↔ ψ.eval ρ
  | .conj φ ψ, ρ => φ.eval ρ ∧ ψ.eval ρ
  | .all x φ, ρ => ∀ n : ℕ, φ.eval (update ρ (.inl x) n)
  | .ex x φ, ρ => ∃ n : ℕ, φ.eval (update ρ (.inl x) n)
  | .setAll X φ, ρ => ∀ A : ↥𝒮, φ.eval (update ρ (.inr X) A)
  | .setEx X φ, ρ => ∃ A : ↥𝒮, φ.eval (update ρ (.inr X) A)

omit [DecidableEq N] in
theorem Term.isPoly (t : Term N) : Metamath.SecondOrder.Sem.IsPoly (t.eval (𝒮 := 𝒮)) := by
  induction t with
  | var x => exact .var x
  | zero => exact .zero
  | succ _ ih => exact .succ ih
  | add _ _ ih ih' => exact .add ih ih'
  | mul _ _ ih ih' => exact .mul ih ih'

theorem Formula.isDef (φ : Formula N) : Metamath.SecondOrder.Sem.IsDef (φ.eval (𝒮 := 𝒮)) := by
  induction φ with
  | equal t u => exact .eq t.isPoly u.isPoly
  | less t u => exact .lt t.isPoly u.isPoly
  | member t X => exact .mem X t.isPoly
  | setEqual X Y => exact .seq X Y
  | neg _ ih => exact .not ih
  | imp _ _ ih ih' => exact .imp ih ih'
  | iff _ _ ih ih' => exact .iff ih ih'
  | conj _ _ ih ih' => exact .and ih ih'
  | all x _ ih => exact .all x ih
  | ex x _ ih => exact .ex x ih
  | setAll X _ ih => exact .sall X ih
  | setEx X _ ih => exact .sex X ih

omit [DecidableEq N] in
/-- Every native polynomial denotation is realized by independent syntax. -/
theorem native_poly_iff {f : Env 𝒮 N → ℕ} :
    Metamath.SecondOrder.Sem.IsPoly f ↔ ∃ t : Term N, t.eval = f := by
  constructor
  · intro h
    induction h with
    | var x => exact ⟨.var x, rfl⟩
    | zero => exact ⟨.zero, rfl⟩
    | succ _ ih => obtain ⟨t, rfl⟩ := ih; exact ⟨.succ t, rfl⟩
    | add _ _ ih ih' =>
      obtain ⟨t, rfl⟩ := ih; obtain ⟨u, rfl⟩ := ih'; exact ⟨.add t u, rfl⟩
    | mul _ _ ih ih' =>
      obtain ⟨t, rfl⟩ := ih; obtain ⟨u, rfl⟩ := ih'; exact ⟨.mul t u, rfl⟩
  · rintro ⟨t, rfl⟩; exact t.isPoly

/-- Surjectivity onto the native definable formula carrier. No completeness
of a proof calculus for full second-order semantics is asserted. -/
theorem native_def_iff {f : Env 𝒮 N → Prop} :
    Metamath.SecondOrder.Sem.IsDef f ↔ ∃ φ : Formula N, φ.eval = f := by
  constructor
  · intro h
    induction h with
    | eq ht hu =>
      obtain ⟨t, rfl⟩ := native_poly_iff.mp ht
      obtain ⟨u, rfl⟩ := native_poly_iff.mp hu
      exact ⟨.equal t u, rfl⟩
    | lt ht hu =>
      obtain ⟨t, rfl⟩ := native_poly_iff.mp ht
      obtain ⟨u, rfl⟩ := native_poly_iff.mp hu
      exact ⟨.less t u, rfl⟩
    | mem X ht => obtain ⟨t, rfl⟩ := native_poly_iff.mp ht; exact ⟨.member t X, rfl⟩
    | seq X Y => exact ⟨.setEqual X Y, rfl⟩
    | not _ ih => obtain ⟨φ, rfl⟩ := ih; exact ⟨.neg φ, rfl⟩
    | imp _ _ ih ih' =>
      obtain ⟨φ, rfl⟩ := ih; obtain ⟨ψ, rfl⟩ := ih'; exact ⟨.imp φ ψ, rfl⟩
    | iff _ _ ih ih' =>
      obtain ⟨φ, rfl⟩ := ih; obtain ⟨ψ, rfl⟩ := ih'; exact ⟨.iff φ ψ, rfl⟩
    | and _ _ ih ih' =>
      obtain ⟨φ, rfl⟩ := ih; obtain ⟨ψ, rfl⟩ := ih'; exact ⟨.conj φ ψ, rfl⟩
    | all x _ ih => obtain ⟨φ, rfl⟩ := ih; exact ⟨.all x φ, rfl⟩
    | ex x _ ih => obtain ⟨φ, rfl⟩ := ih; exact ⟨.ex x φ, rfl⟩
    | sall X _ ih => obtain ⟨φ, rfl⟩ := ih; exact ⟨.setAll X φ, rfl⟩
    | sex X _ ih => obtain ⟨φ, rfl⟩ := ih; exact ⟨.setEx X φ, rfl⟩
  · rintro ⟨φ, rfl⟩; exact φ.isDef

theorem Term.ignores (t : Term N) {x : N} (h : x ∉ t.names) :
    Metamath.SecondOrder.Sem.Ignores (t.eval (𝒮 := 𝒮)) (.inl x) := by
  induction t with
  | var y =>
    have hxy : x ≠ y := by simpa [Term.names] using h
    exact Metamath.SecondOrder.Sem.ignores_var (by simpa using hxy)
  | zero => exact Metamath.SecondOrder.Sem.ignores_const 0 _
  | succ t ih => exact Metamath.SecondOrder.Sem.ignores_comp (ih h) (· + 1)
  | add t u ih ih' =>
    simp only [Term.names, Finset.mem_union, not_or] at h
    exact Metamath.SecondOrder.Sem.ignores_comp₂ (ih h.1) (ih' h.2) (· + ·)
  | mul t u ih ih' =>
    simp only [Term.names, Finset.mem_union, not_or] at h
    exact Metamath.SecondOrder.Sem.ignores_comp₂ (ih h.1) (ih' h.2) (· * ·)

theorem Bounded.native {φ : Formula N} (h : Bounded φ) :
    Metamath.SecondOrder.Sem.IsBnd (φ.eval (𝒮 := 𝒮)) := by
  induction h with
  | equal t u => exact .eq t.isPoly u.isPoly
  | less t u => exact .lt t.isPoly u.isPoly
  | member t X => exact .mem X t.isPoly
  | neg _ ih => exact .not ih
  | imp _ _ ih ih' => exact .imp ih ih'
  | iff _ _ ih ih' => exact .iff ih ih'
  | conj _ _ ih ih' => exact .and ih ih'
  | ball x t hx _ ih => exact .ball x t.isPoly (t.ignores hx) ih
  | bex x t hx _ ih => exact .bex x t.isPoly (t.ignores hx) ih

theorem Sigma01.native {φ : Formula N} : Sigma01 φ → Metamath.SecondOrder.Sem.IsSig1 (φ.eval (𝒮 := 𝒮))
  | .bounded h => .bnd h.native
  | .ex x h => .ex x h.native

theorem Pi01.native {φ : Formula N} : Pi01 φ → Metamath.SecondOrder.Sem.IsPi1 (φ.eval (𝒮 := 𝒮))
  | .bounded h => .bnd h.native
  | .all x h => .all x h.native

theorem Arithmetical.native {φ : Formula N} (h : Arithmetical φ) :
    Metamath.SecondOrder.Sem.IsArith (φ.eval (𝒮 := 𝒮)) := by
  induction h with
  | equal t u => exact .eq t.isPoly u.isPoly
  | less t u => exact .lt t.isPoly u.isPoly
  | member t X => exact .mem X t.isPoly
  | setEqual X Y => exact .seq X Y
  | neg _ ih => exact .not ih
  | imp _ _ ih ih' => exact .imp ih ih'
  | iff _ _ ih ih' => exact .iff ih ih'
  | conj _ _ ih ih' => exact .and ih ih'
  | all x _ ih => exact .all x ih
  | ex x _ ih => exact .ex x ih

end Silmaril.Logic.SecondOrderArithmetic

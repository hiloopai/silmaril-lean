module

public import Silmaril.Logic.Arithmetic.Syntax

@[expose] public section

namespace Silmaril.Logic.Arithmetic

variable {n m : ℕ}

abbrev Assignment (n : ℕ) := Fin n → ℕ
abbrev extend (e : Assignment n) (x : ℕ) : Assignment (n + 1) := Fin.cases x e

namespace Term

def eval {n : ℕ} (e : Assignment n) : Term n → ℕ
  | .var i => e i
  | .zero => 0
  | .succ t => Nat.succ (eval e t)
  | .add s t => eval e s + eval e t
  | .mul s t => eval e s * eval e t

@[simp] theorem eval_rename (t : Term n) (ρ : Fin n → Fin m) (e : Assignment m) :
    (t.rename ρ).eval e = t.eval (e ∘ ρ) := by
  induction t <;> simp_all [rename, eval]

@[simp] theorem eval_subst (t : Term n) (σ : Fin n → Term m) (e : Assignment m) :
    (t.subst σ).eval e = t.eval (fun i => (σ i).eval e) := by
  induction t <;> simp_all [subst, eval]

@[simp] theorem eval_shift (t : Term n) (e : Assignment n) (x : ℕ) :
    t.shift.eval (extend e x) = t.eval e := by simp [shift, extend, Function.comp_def]

end Term

namespace Formula

def eval {n : ℕ} (e : Assignment n) : Formula n → Prop
  | .bot => False
  | .equal s t => s.eval e = t.eval e
  | .imp φ ψ => eval e φ → eval e ψ
  | .conj φ ψ => eval e φ ∧ eval e ψ
  | .disj φ ψ => eval e φ ∨ eval e ψ
  | .all φ => ∀ x, eval (extend e x) φ
  | .ex φ => ∃ x, eval (extend e x) φ

@[simp] theorem eval_rename (φ : Formula n) (ρ : Fin n → Fin m) (e : Assignment m) :
    (φ.rename ρ).eval e ↔ φ.eval (e ∘ ρ) := by
  induction φ generalizing m with
  | bot => rfl
  | equal s t => simp [rename, eval]
  | imp φ ψ ihφ ihψ => simp [rename, eval, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp [rename, eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [rename, eval, ihφ, ihψ]
  | all φ ih =>
    simp only [rename, eval, ih]
    apply forall_congr'
    intro x
    have h : extend e x ∘ liftRename ρ = extend (e ∘ ρ) x := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [h]
  | ex φ ih =>
    simp only [rename, eval, ih]
    apply exists_congr
    intro x
    have h : extend e x ∘ liftRename ρ = extend (e ∘ ρ) x := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [h]

@[simp] theorem eval_subst (φ : Formula n) (σ : Fin n → Term m) (e : Assignment m) :
    (φ.subst σ).eval e ↔ φ.eval (fun i => (σ i).eval e) := by
  induction φ generalizing m with
  | bot => rfl
  | equal s t => simp [subst, eval]
  | imp φ ψ ihφ ihψ => simp [subst, eval, ihφ, ihψ]
  | conj φ ψ ihφ ihψ => simp [subst, eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [subst, eval, ihφ, ihψ]
  | all φ ih =>
    simp only [subst, eval, ih]
    apply forall_congr'
    intro x
    have h : (fun i => (Term.liftSubst σ i).eval (extend e x)) =
        extend (fun i => (σ i).eval e) x := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp [Term.liftSubst, extend, Function.comp_def]
    rw [h]
  | ex φ ih =>
    simp only [subst, eval, ih]
    apply exists_congr
    intro x
    have h : (fun i => (Term.liftSubst σ i).eval (extend e x)) =
        extend (fun i => (σ i).eval e) x := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp [Term.liftSubst, extend, Function.comp_def]
    rw [h]

@[simp] theorem eval_shift (φ : Formula n) (e : Assignment n) (x : ℕ) :
    φ.shift.eval (extend e x) ↔ φ.eval e := by simp [shift, extend, Function.comp_def]

@[simp] theorem eval_inst (φ : Formula (n + 1)) (t : Term n) (e : Assignment n) :
    (φ.inst t).eval e ↔ φ.eval (extend e (t.eval e)) := by
  rw [eval_subst]
  have h : (fun i => (show Term n from Fin.cases t Term.var i).eval e) = extend e (t.eval e) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [h]

@[simp] theorem eval_step (φ : Formula (n + 1)) (e : Assignment n) (x : ℕ) :
    φ.step.eval (extend e x) ↔ φ.eval (extend e (Nat.succ x)) := by
  rw [step, eval_subst]
  have h : (fun i => (show Term (n + 1) from Fin.cases (.succ (.var 0)) (fun j => .var j.succ) i).eval
      (extend e x)) = extend e (Nat.succ x) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [h]

end Formula

/-- All assumptions hold under this assignment. -/
def Satisfies (e : Assignment n) (Γ : Context n) : Prop := ∀ φ ∈ Γ, φ.eval e

/-- Validity in the standard natural-number model. -/
def Valid (φ : Formula n) : Prop := ∀ e, φ.eval e

end Silmaril.Logic.Arithmetic

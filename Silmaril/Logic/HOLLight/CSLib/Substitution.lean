module

public import Silmaril.Logic.HOLLight.Kernel.Structural
public import Cslib.Foundations.Syntax.HasSubstitution

@[expose] public section

/-!
# HOL substitutions through CSLib's interface

CSLib's `HasSubstitution` accepts both individual variables and finite variable
domains in the instances below. Single type-variable replacement specializes
the existing simultaneous type substitution. Free term replacement uses the
full typed name `Nat × Ty` and retains capture avoidance under locally nameless
binders. Finite domains paired with replacement maps provide parallel substitution.

Bound substitution and opening retain their explicit, separate operations.
There is deliberately no `HasSubstitution Tm Nat Tm` instance: a natural-number
name alone does not identify a HOL free variable.
-/

namespace Silmaril.Logic.HOLLight

/-- The type substitution changing exactly one schematic variable. -/
def Ty.replaceVar (A : Ty) (name : Nat) (replacement : Ty) : Ty :=
  A.subst (Function.update Ty.var name replacement)

instance : Cslib.HasSubstitution Ty Nat Ty := ⟨Ty.replaceVar⟩

instance : Cslib.HasSubstitution Const Nat Ty where
  subst c name replacement := c.tySubst (Function.update Ty.var name replacement)

instance : Cslib.HasSubstitution Tm Nat Ty where
  subst t name replacement := t.tySubst (Function.update Ty.var name replacement)

instance : Cslib.HasSubstitution Tm (Nat × Ty) Tm := ⟨Tm.replaceFree⟩

@[simp] theorem Ty.cslib_subst_def (A replacement : Ty) (name : Nat) :
    A[name := replacement] = A.subst (Function.update Ty.var name replacement) := rfl

@[simp] theorem Const.cslib_subst_def (c : Const) (name : Nat) (replacement : Ty) :
    c[name := replacement] = c.tySubst (Function.update Ty.var name replacement) := rfl

@[simp] theorem Tm.cslib_type_subst_def (t : Tm) (name : Nat) (replacement : Ty) :
    t[name := replacement] = t.tySubst (Function.update Ty.var name replacement) := rfl

@[simp] theorem Tm.cslib_free_subst_def (t replacement : Tm) (v : Nat × Ty) :
    t[v := replacement] = t.replaceFree v replacement := rfl

@[simp] theorem Ty.cslib_subst_same (name : Nat) (replacement : Ty) :
    (Ty.var name)[name := replacement] = replacement := by simp

@[simp] theorem Ty.cslib_subst_other {i name : Nat} (h : i ≠ name) (replacement : Ty) :
    (Ty.var i)[name := replacement] = Ty.var i := by simp [h]

theorem Ty.update_wellFormed {ops : List Nat} {replacement : Ty}
    (h : replacement.WellFormed ops) (name i : Nat) :
    (Function.update Ty.var name replacement i).WellFormed ops := by
  by_cases hi : i = name
  · subst i; simpa using h
  · simp [Function.update_of_ne hi, Ty.WellFormed]

theorem Ty.WellFormed.cslib_subst {ops : List Nat} {A replacement : Ty}
    (hA : A.WellFormed ops) (hReplacement : replacement.WellFormed ops) (name : Nat) :
    (A[name := replacement]).WellFormed ops :=
  hA.subst (Ty.update_wellFormed hReplacement name)

theorem Const.HasType.cslib_subst {sig : Signature} {c : Const} {A replacement : Ty}
    (typing : c.HasType sig A) (name : Nat)
    (hReplacement : replacement.WellFormed sig.tyOps) :
    (c[name := replacement]).HasType sig (A[name := replacement]) :=
  typing.tySubst _ (Ty.update_wellFormed hReplacement name)

theorem HasType.cslib_type_subst {sig : Signature} {Γ : List Ty} {t : Tm}
    {A replacement : Ty} (typing : HasType sig Γ t A) (name : Nat)
    (hReplacement : replacement.WellFormed sig.tyOps) :
    HasType sig (Γ.map (fun B => B[name := replacement]))
      (t[name := replacement]) (A[name := replacement]) :=
  typing.tySubst _ (Ty.update_wellFormed hReplacement name)

theorem HasType.cslib_free_subst {sig : Signature} {Γ : List Ty}
    {t replacement : Tm} {A : Ty} (typing : HasType sig Γ t A) (v : Nat × Ty)
    (hReplacement : HasType sig Γ replacement v.2) :
    HasType sig Γ (t[v := replacement]) A := by
  apply typing.freeSubst
  intro n B hB
  split
  · rename_i same
    have htype : B = v.2 := congrArg Prod.snd same
    cases htype
    exact hReplacement
  · exact .fvar n hB

theorem Tm.cslib_free_subst_fresh {v : Nat × Ty} {t : Tm}
    (fresh : t.Fresh v) (replacement : Tm) : t[v := replacement] = t :=
  Tm.replaceFree_of_fresh fresh replacement

/-- A closed free replacement crosses a binder unchanged. Open replacements
instead use the weakening already built into `Tm.freeSubst`. -/
theorem Tm.cslib_free_subst_lam_closed {replacement : Tm} (closed : replacement.Closed)
    (A : Ty) (body : Tm) (v : Nat × Ty) :
    (Tm.lam A body)[v := replacement] = .lam A (body[v := replacement]) := by
  apply Tm.freeSubst_lam_closed
  intro n B
  split
  · exact closed
  · trivial

theorem Tm.Scope.cslib_free_subst {depth : Nat} {t replacement : Tm}
    (ht : t.Scope depth) (hr : replacement.Scope depth) (v : Nat × Ty) :
    (t[v := replacement]).Scope depth := by
  apply ht.freeSubst
  intro n B
  split
  · exact hr
  · trivial

theorem Derives.cslib_type_subst {sig : Signature} {theory : Theory} {H : Hyps} {p : Tm}
    (proof : Derives sig theory H p) (name : Nat) {replacement : Ty}
    (hReplacement : replacement.WellFormed sig.tyOps) :
    Derives sig theory (H.image (fun t => t[name := replacement]))
      (p[name := replacement]) :=
  proof.instType _ (Ty.update_wellFormed hReplacement name)

theorem Derives.cslib_free_subst {sig : Signature} {theory : Theory} {H : Hyps}
    {p replacement : Tm} (proof : Derives sig theory H p) (v : Nat × Ty)
    (hReplacement : HasType sig [] replacement v.2) :
    Derives sig theory (H.image (fun t => t[v := replacement])) (p[v := replacement]) :=
  proof.replaceFree v.1 hReplacement

/-! ## Finite-domain simultaneous substitution

The same CSLib interface also accepts a finite set of variables and a replacement
map: `t[X := σ]` replaces the members of `X` simultaneously. Replacements are not
recursively substituted. A singleton agrees with single-variable replacement;
choosing the full support agrees with the original simultaneous operation.
-/

namespace Ty

mutual
/-- The finite support of schematic variables in a HOL type. -/
def vars : Ty → Finset Nat
  | .var i => {i}
  | .bool | .ind => ∅
  | .arr A B => vars A ∪ vars B
  | .app _ args => varsList args
termination_by structural A => A

def varsList : List Ty → Finset Nat
  | [] => ∅
  | A :: args => vars A ∪ varsList args
termination_by structural args => args
end

@[simp] theorem mem_varsList (i : Nat) (args : List Ty) :
    i ∈ varsList args ↔ ∃ A ∈ args, i ∈ vars A := by
  induction args with
  | nil => simp [varsList]
  | cons A args ih => simp [varsList, ih]

theorem subst_congr_vars {A : Ty} {σ τ : Nat → Ty}
    (h : ∀ i ∈ A.vars, σ i = τ i) : A.subst σ = A.subst τ := by
  induction A using induction_on with
  | var i => exact h i (Finset.mem_singleton_self _)
  | bool => rfl
  | ind => rfl
  | arr A B ihA ihB =>
    simp only [vars, Finset.mem_union] at h
    simp only [subst_arr, ihA (fun i hi => h i (.inl hi)), ihB (fun i hi => h i (.inr hi))]
  | app c args ih =>
    simp only [vars, mem_varsList] at h
    simp only [subst_app, Ty.app.injEq, true_and]
    exact List.map_congr_left (fun A hA => ih A hA (fun i hi => h i ⟨A, hA, hi⟩))

/-- Restrict a simultaneous substitution to a finite domain. -/
def restrictSubst (X : Finset Nat) (σ : Nat → Ty) : Nat → Ty :=
  fun i => if i ∈ X then σ i else .var i

instance : Cslib.HasSubstitution Ty (Finset Nat) (Nat → Ty) where
  subst A X σ := A.subst (restrictSubst X σ)

@[simp] theorem cslib_parallel_def (A : Ty) (X : Finset Nat) (σ : Nat → Ty) :
    A[X := σ] = A.subst (restrictSubst X σ) := rfl

@[simp] theorem cslib_parallel_empty (A : Ty) (σ : Nat → Ty) : A[(∅ : Finset Nat) := σ] = A := by
  have h : restrictSubst ∅ σ = Ty.var := by funext i; simp [restrictSubst]
  simp only [cslib_parallel_def, h, subst_id]

@[simp] theorem cslib_parallel_id (A : Ty) (X : Finset Nat) : A[X := Ty.var] = A := by
  have h : restrictSubst X Ty.var = Ty.var := by funext i; simp [restrictSubst]
  simp only [cslib_parallel_def, h, subst_id]

theorem cslib_parallel_singleton (A : Ty) (i : Nat) (σ : Nat → Ty) :
    A[({i} : Finset Nat) := σ] = A[i := σ i] := by
  unfold Cslib.HasSubstitution.subst
  apply congrArg (A.subst)
  funext j
  by_cases h : j = i <;> simp [restrictSubst, Function.update, h]

theorem cslib_parallel_support (A : Ty) (σ : Nat → Ty) : A[A.vars := σ] = A.subst σ :=
  subst_congr_vars (fun _ hi => ite_eq_left hi)

theorem cslib_parallel_comp (A : Ty) (X Y : Finset Nat) (σ τ : Nat → Ty) :
    (A[X := σ])[Y := τ] =
      A[X ∪ Y := fun i => if i ∈ X then (σ i)[Y := τ] else τ i] := by
  simp only [cslib_parallel_def, subst_comp]
  apply congrArg (A.subst)
  funext i
  by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [restrictSubst, hx, hy]

theorem restrictSubst_wellFormed {ops : List Nat} {X : Finset Nat} {σ : Nat → Ty}
    (hσ : ∀ i ∈ X, (σ i).WellFormed ops) (i : Nat) :
    (restrictSubst X σ i).WellFormed ops := by
  unfold restrictSubst
  split
  · exact hσ i ‹i ∈ X›
  · trivial

theorem WellFormed.cslib_parallel {ops : List Nat} {A : Ty} (hA : A.WellFormed ops)
    (X : Finset Nat) (σ : Nat → Ty) (hσ : ∀ i ∈ X, (σ i).WellFormed ops) :
    (A[X := σ]).WellFormed ops := hA.subst (restrictSubst_wellFormed hσ)

end Ty

namespace Const

def typeVars : Const → Finset Nat
  | .eq A | .select A => A.vars
  | .user _ args => Ty.varsList args

theorem tySubst_congr_vars {c : Const} {σ τ : Nat → Ty}
    (h : ∀ i ∈ c.typeVars, σ i = τ i) : c.tySubst σ = c.tySubst τ := by
  cases c with
  | eq A => exact congrArg Const.eq (Ty.subst_congr_vars h)
  | select A => exact congrArg Const.select (Ty.subst_congr_vars h)
  | user n args =>
    simp only [typeVars, Ty.mem_varsList] at h
    apply congrArg (Const.user n)
    exact List.map_congr_left (fun A hA => Ty.subst_congr_vars (fun i hi => h i ⟨A, hA, hi⟩))

instance : Cslib.HasSubstitution Const (Finset Nat) (Nat → Ty) where
  subst c X σ := c.tySubst (Ty.restrictSubst X σ)

@[simp] theorem cslib_parallel_def (c : Const) (X : Finset Nat) (σ : Nat → Ty) :
    c[X := σ] = c.tySubst (Ty.restrictSubst X σ) := rfl

@[simp] theorem cslib_parallel_empty (c : Const) (σ : Nat → Ty) :
    c[(∅ : Finset Nat) := σ] = c := by
  have h : Ty.restrictSubst ∅ σ = Ty.var := by funext i; simp [Ty.restrictSubst]
  simp only [cslib_parallel_def, h, tySubst_id]

@[simp] theorem cslib_parallel_id (c : Const) (X : Finset Nat) : c[X := Ty.var] = c := by
  have h : Ty.restrictSubst X Ty.var = Ty.var := by funext i; simp [Ty.restrictSubst]
  simp only [cslib_parallel_def, h, tySubst_id]

theorem cslib_parallel_singleton (c : Const) (i : Nat) (σ : Nat → Ty) :
    c[({i} : Finset Nat) := σ] = c[i := σ i] := by
  apply congrArg (c.tySubst)
  funext j
  by_cases h : j = i <;> simp [Ty.restrictSubst, Function.update, h]

theorem cslib_parallel_support (c : Const) (σ : Nat → Ty) :
    c[c.typeVars := σ] = c.tySubst σ := tySubst_congr_vars (fun _ hi => ite_eq_left hi)

theorem cslib_parallel_comp (c : Const) (X Y : Finset Nat) (σ τ : Nat → Ty) :
    (c[X := σ])[Y := τ] =
      c[X ∪ Y := fun i => if i ∈ X then (σ i)[Y := τ] else τ i] := by
  simp only [cslib_parallel_def, Ty.cslib_parallel_def, tySubst_comp]
  apply congrArg (c.tySubst)
  funext i
  by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [Ty.restrictSubst, hx, hy]

end Const

namespace Tm

/-- Type variables occurring in every annotation and constant instance. -/
def typeVars : Tm → Finset Nat
  | .bvar _ => ∅
  | .fvar _ A => A.vars
  | .const c => c.typeVars
  | .app f x => f.typeVars ∪ x.typeVars
  | .lam A b => A.vars ∪ b.typeVars

theorem tySubst_congr_vars {t : Tm} {σ τ : Nat → Ty}
    (h : ∀ i ∈ t.typeVars, σ i = τ i) : t.tySubst σ = t.tySubst τ := by
  induction t with
  | bvar i => rfl
  | fvar n A => exact congrArg (Tm.fvar n) (Ty.subst_congr_vars h)
  | const c => exact congrArg Tm.const (Const.tySubst_congr_vars h)
  | app f x ihf ihx =>
    simp only [typeVars, Finset.mem_union] at h
    simp only [tySubst, ihf (fun i hi => h i (.inl hi)), ihx (fun i hi => h i (.inr hi))]
  | lam A b ih =>
    simp only [typeVars, Finset.mem_union] at h
    simp only [tySubst, Ty.subst_congr_vars (fun i hi => h i (.inl hi)),
      ih (fun i hi => h i (.inr hi))]

instance : Cslib.HasSubstitution Tm (Finset Nat) (Nat → Ty) where
  subst t X σ := t.tySubst (Ty.restrictSubst X σ)

@[simp] theorem cslib_type_parallel_def (t : Tm) (X : Finset Nat) (σ : Nat → Ty) :
    t[X := σ] = t.tySubst (Ty.restrictSubst X σ) := rfl

@[simp] theorem cslib_type_parallel_empty (t : Tm) (σ : Nat → Ty) :
    t[(∅ : Finset Nat) := σ] = t := by
  have h : Ty.restrictSubst ∅ σ = Ty.var := by funext i; simp [Ty.restrictSubst]
  simp only [cslib_type_parallel_def, h, tySubst_id]

@[simp] theorem cslib_type_parallel_id (t : Tm) (X : Finset Nat) : t[X := Ty.var] = t := by
  have h : Ty.restrictSubst X Ty.var = Ty.var := by funext i; simp [Ty.restrictSubst]
  simp only [cslib_type_parallel_def, h, tySubst_id]

theorem cslib_type_parallel_singleton (t : Tm) (i : Nat) (σ : Nat → Ty) :
    t[({i} : Finset Nat) := σ] = t[i := σ i] := by
  apply congrArg (t.tySubst)
  funext j
  by_cases h : j = i <;> simp [Ty.restrictSubst, Function.update, h]

theorem cslib_type_parallel_support (t : Tm) (σ : Nat → Ty) :
    t[t.typeVars := σ] = t.tySubst σ := tySubst_congr_vars (fun _ hi => ite_eq_left hi)

theorem cslib_type_parallel_comp (t : Tm) (X Y : Finset Nat) (σ τ : Nat → Ty) :
    (t[X := σ])[Y := τ] =
      t[X ∪ Y := fun i => if i ∈ X then (σ i)[Y := τ] else τ i] := by
  simp only [cslib_type_parallel_def, Ty.cslib_parallel_def, tySubst_comp]
  apply congrArg (t.tySubst)
  funext i
  by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [Ty.restrictSubst, hx, hy]

/-- Restrict free substitution using full typed names as its finite domain. -/
def restrictFreeSubst (X : Finset (Nat × Ty)) (σ : Nat → Ty → Tm) : Nat → Ty → Tm :=
  fun n A => if (n, A) ∈ X then σ n A else .fvar n A

instance : Cslib.HasSubstitution Tm (Finset (Nat × Ty)) (Nat → Ty → Tm) where
  subst t X σ := t.freeSubst (restrictFreeSubst X σ)

@[simp] theorem cslib_free_parallel_def (t : Tm) (X : Finset (Nat × Ty))
    (σ : Nat → Ty → Tm) : t[X := σ] = t.freeSubst (restrictFreeSubst X σ) := rfl

@[simp] theorem cslib_free_parallel_empty (t : Tm) (σ : Nat → Ty → Tm) :
    t[(∅ : Finset (Nat × Ty)) := σ] = t := by
  have h : restrictFreeSubst ∅ σ = Tm.fvar := by funext n A; simp [restrictFreeSubst]
  simp only [cslib_free_parallel_def, h, freeSubst_id]

@[simp] theorem cslib_free_parallel_id (t : Tm) (X : Finset (Nat × Ty)) :
    t[X := Tm.fvar] = t := by
  have h : restrictFreeSubst X Tm.fvar = Tm.fvar := by funext n A; simp [restrictFreeSubst]
  simp only [cslib_free_parallel_def, h, freeSubst_id]

theorem cslib_free_parallel_singleton (t : Tm) (v : Nat × Ty) (σ : Nat → Ty → Tm) :
    t[({v} : Finset (Nat × Ty)) := σ] = t[v := σ v.1 v.2] := by
  apply congrArg (t.freeSubst)
  funext n A
  by_cases h : (n, A) = v
  · cases h; simp [restrictFreeSubst]
  · simp [restrictFreeSubst, h]

theorem cslib_free_parallel_support (t : Tm) (σ : Nat → Ty → Tm) :
    t[t.freeVars.toFinset := σ] = t.freeSubst σ :=
  freeSubst_congr t _ _ (fun _ _ hi => ite_eq_left (List.mem_toFinset.mpr hi))

theorem cslib_free_parallel_comp (t : Tm) (X Y : Finset (Nat × Ty))
    (σ τ : Nat → Ty → Tm) :
    (t[X := σ])[Y := τ] =
      t[X ∪ Y := fun n A => if (n, A) ∈ X then (σ n A)[Y := τ] else τ n A] := by
  simp only [cslib_free_parallel_def, freeSubst_comp]
  apply congrArg (t.freeSubst)
  funext n A
  by_cases hx : (n, A) ∈ X <;> by_cases hy : (n, A) ∈ Y <;>
    simp [restrictFreeSubst, freeSubst, hx, hy]

theorem Scope.cslib_free_parallel {depth : Nat} {t : Tm} (ht : t.Scope depth)
    (X : Finset (Nat × Ty)) (σ : Nat → Ty → Tm)
    (hσ : ∀ n A, (n, A) ∈ X → (σ n A).Scope depth) : (t[X := σ]).Scope depth := by
  apply ht.freeSubst
  intro n A
  unfold restrictFreeSubst
  split
  · exact hσ n A ‹(n, A) ∈ X›
  · trivial

end Tm

theorem Const.HasType.cslib_parallel {sig : Signature} {c : Const} {A : Ty}
    (typing : c.HasType sig A) (X : Finset Nat) (σ : Nat → Ty)
    (hσ : ∀ i ∈ X, (σ i).WellFormed sig.tyOps) :
    (c[X := σ]).HasType sig (A[X := σ]) :=
  typing.tySubst _ (Ty.restrictSubst_wellFormed hσ)

theorem HasType.cslib_type_parallel {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) (X : Finset Nat) (σ : Nat → Ty)
    (hσ : ∀ i ∈ X, (σ i).WellFormed sig.tyOps) :
    HasType sig (Γ.map (fun B => B[X := σ])) (t[X := σ]) (A[X := σ]) :=
  typing.tySubst _ (Ty.restrictSubst_wellFormed hσ)

theorem HasType.cslib_free_parallel {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) (X : Finset (Nat × Ty)) (σ : Nat → Ty → Tm)
    (hσ : ∀ n B, (n, B) ∈ X → B.WellFormed sig.tyOps → HasType sig Γ (σ n B) B) :
    HasType sig Γ (t[X := σ]) A := by
  apply typing.freeSubst
  intro n B hB
  unfold Tm.restrictFreeSubst
  split
  · exact hσ n B ‹(n, B) ∈ X› hB
  · exact .fvar n hB

theorem Derives.cslib_type_parallel {sig : Signature} {theory : Theory} {H : Hyps} {p : Tm}
    (proof : Derives sig theory H p) (X : Finset Nat) (σ : Nat → Ty)
    (hσ : ∀ i ∈ X, (σ i).WellFormed sig.tyOps) :
    Derives sig theory (H.image (fun t => t[X := σ])) (p[X := σ]) :=
  proof.instType _ (Ty.restrictSubst_wellFormed hσ)

theorem Derives.cslib_free_parallel {sig : Signature} {theory : Theory} {H : Hyps} {p : Tm}
    (proof : Derives sig theory H p) (X : Finset (Nat × Ty)) (σ : Nat → Ty → Tm)
    (hσ : ∀ n B, (n, B) ∈ X → B.WellFormed sig.tyOps → HasType sig [] (σ n B) B) :
    Derives sig theory (H.image (fun t => t[X := σ])) (p[X := σ]) := by
  apply proof.inst
  intro n B hB
  unfold Tm.restrictFreeSubst
  split
  · exact hσ n B ‹(n, B) ∈ X› hB
  · exact .fvar n hB

end Silmaril.Logic.HOLLight

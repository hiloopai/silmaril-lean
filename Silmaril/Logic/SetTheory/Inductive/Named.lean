module

public import Silmaril.Logic.SetTheory.Inductive.Semantics
public import Silmaril.Logic.SetTheory.Formula

@[expose] public section

/-!
# Independent named membership syntax

This finite syntax is the intermediate language for set.mm's named binders.
Classes are restricted to coerced set variables; wff metavariables are replaced
by actual finite formulas before translation. `lower` removes named binding in
favor of the scoped syntax, including shadowing. `vars` deliberately includes
bound variable names: Metamath disjointness is syntactic, stronger than merely
not being semantically free.
-/

namespace Silmaril.Logic.SetTheory.Inductive.Named

/-- Finite named first-order formulas in the common set.mm membership fragment. -/
inductive Formula (V : Type*) where
  | eq (x y : V)
  | mem (x y : V)
  | neg (p : Formula V)
  | imp (p q : Formula V)
  | iff (p q : Formula V)
  | conj (p q : Formula V)
  | disj (p q : Formula V)
  | all (x : V) (p : Formula V)
  | ex (x : V) (p : Formula V)
  deriving DecidableEq, Repr

namespace Formula

/-- Names occurring syntactically, including binder declarations. -/
def vars {V : Type*} : Formula V → List V
  | .eq x y | .mem x y => [x, y]
  | .neg p => p.vars
  | .imp p q | .iff p q | .conj p q | .disj p q => p.vars ++ q.vars
  | .all x p | .ex x p => p.vars ++ [x]

/-- Independent Tarski semantics for named binders. -/
def eval {M V : Type*} [Membership M M] [DecidableEq V] (E : V → M) : Formula V → Prop
  | .eq x y => E x = E y
  | .mem x y => E x ∈ E y
  | .neg p => ¬ p.eval E
  | .imp p q => p.eval E → q.eval E
  | .iff p q => p.eval E ↔ q.eval E
  | .conj p q => p.eval E ∧ q.eval E
  | .disj p q => p.eval E ∨ q.eval E
  | .all x p => ∀ a : M, p.eval (Function.update E x a)
  | .ex x p => ∃ a : M, p.eval (Function.update E x a)

/-- Interpret a named binder by a new head variable, respecting shadowing. -/
def bindNames {V : Type*} [DecidableEq V] {n : Nat} (ρ : V → Fin n) (x : V) : V → Fin (n + 1) :=
  fun v => if v = x then 0 else (ρ v).succ

/-- Translate named binding into scoped, capture-avoiding binding. -/
def lower {V : Type*} [DecidableEq V] {n : Nat} (ρ : V → Fin n) :
    Formula V → Inductive.Formula n
  | .eq x y => .eq (ρ x) (ρ y)
  | .mem x y => .mem (ρ x) (ρ y)
  | .neg p => .neg (p.lower ρ)
  | .imp p q => .imp (p.lower ρ) (q.lower ρ)
  | .iff p q => .iff (p.lower ρ) (q.lower ρ)
  | .conj p q => .conj (p.lower ρ) (q.lower ρ)
  | .disj p q => .disj (p.lower ρ) (q.lower ρ)
  | .all x p => .all (p.lower (bindNames ρ x))
  | .ex x p => .ex (p.lower (bindNames ρ x))

/-- Lift a partial free-name assignment underneath a binder. -/
def bindScope {V : Type*} [DecidableEq V] {n : Nat} (σ : V → Option (Fin n)) (x : V) :
    V → Option (Fin (n + 1)) := fun v => if v = x then some 0 else Fin.succ <$> σ v

/-- Scope a named formula, rejecting missing free names but accepting bound names.
In particular closed named schemas can be scoped into `Formula 0`. -/
def scope {V : Type*} [DecidableEq V] {n : Nat} (σ : V → Option (Fin n)) :
    Formula V → Option (Inductive.Formula n)
  | .eq x y => Inductive.Formula.eq <$> σ x <*> σ y
  | .mem x y => Inductive.Formula.mem <$> σ x <*> σ y
  | .neg p => Inductive.Formula.neg <$> p.scope σ
  | .imp p q => Inductive.Formula.imp <$> p.scope σ <*> q.scope σ
  | .iff p q => Inductive.Formula.iff <$> p.scope σ <*> q.scope σ
  | .conj p q => Inductive.Formula.conj <$> p.scope σ <*> q.scope σ
  | .disj p q => Inductive.Formula.disj <$> p.scope σ <*> q.scope σ
  | .all x p => Inductive.Formula.all <$> p.scope (bindScope σ x)
  | .ex x p => Inductive.Formula.ex <$> p.scope (bindScope σ x)

/-- An assignment for checking partial scoping; unused names receive a default value. -/
def resolve {M V : Type*} {n : Nat} (σ : V → Option (Fin n)) (E : Fin n → M) (d : M) : V → M :=
  fun v => (σ v).elim d E

@[simp] theorem resolve_bindScope {M V : Type*} [DecidableEq V] {n : Nat}
    (σ : V → Option (Fin n)) (E : Fin n → M) (d a : M) (x : V) :
    resolve (bindScope σ x) (Fin.cons a E) d = Function.update (resolve σ E d) x a := by
  funext v
  by_cases h : v = x
  · simp [resolve, bindScope, h]
  · cases hs : σ v <;> simp [resolve, bindScope, h, hs]

/-- Successful partial scoping preserves semantics; defaults cannot become free variables. -/
theorem eval_scope {M V : Type*} [Membership M M] [DecidableEq V]
    (p : Formula V) {n : Nat} (σ : V → Option (Fin n)) (q : Inductive.Formula n)
    (h : p.scope σ = some q) (E : Fin n → M) (d : M) :
    q.eval E ↔ p.eval (resolve σ E d) := by
  induction p generalizing n with
  | eq x y | mem x y =>
    cases hx : σ x <;> cases hy : σ y <;> simp [scope, hx, hy, Seq.seq] at h
    cases h
    simp [Inductive.Formula.eval, eval, resolve, hx, hy]
  | neg p ih =>
    cases hp : p.scope σ <;> simp [scope, hp] at h
    cases h
    exact not_congr (ih _ _ hp E)
  | imp p r ih ir | iff p r ih ir | conj p r ih ir | disj p r ih ir =>
    cases hp : p.scope σ <;> cases hr : r.scope σ <;> simp [scope, hp, hr, Seq.seq] at h
    cases h
    first
    | exact imp_congr (ih _ _ hp E) (ir _ _ hr E)
    | exact iff_congr (ih _ _ hp E) (ir _ _ hr E)
    | exact and_congr (ih _ _ hp E) (ir _ _ hr E)
    | exact or_congr (ih _ _ hp E) (ir _ _ hr E)
  | all x p ih | ex x p ih =>
    cases hp : p.scope (bindScope σ x) <;> simp [scope, hp] at h
    cases h
    have hh := fun a => (ih _ _ hp (Fin.cons a E)).trans (by rw [resolve_bindScope])
    first | exact forall_congr' hh | exact exists_congr hh

@[simp] theorem bindScope_total {V : Type*} [DecidableEq V] {n : Nat}
    (σ : V → Fin n) (x : V) : bindScope (some ∘ σ) x = some ∘ bindNames σ x := by
  funext v
  by_cases h : v = x <;> simp [bindScope, bindNames, h]

/-- Total scoping is the earlier total lowering operation. -/
@[simp] theorem scope_total {V : Type*} [DecidableEq V] {n : Nat}
    (p : Formula V) (σ : V → Fin n) : p.scope (some ∘ σ) = some (p.lower σ) := by
  induction p generalizing n <;> simp [scope, lower, *, bindScope_total]

/-- Lowering preserves satisfaction, even for noninjective assignments of names. -/
theorem eval_lower {M V : Type*} [Membership M M] [DecidableEq V]
    (p : Formula V) {n : Nat} (ρ : V → Fin n) (E : Fin n → M) :
    (p.lower ρ).eval E ↔ p.eval (E ∘ ρ) := by
  induction p generalizing n with
  | eq x y => rfl
  | mem x y => rfl
  | neg p ih => exact not_congr (ih ρ E)
  | imp p q ih iq => exact imp_congr (ih ρ E) (iq ρ E)
  | iff p q ih iq => exact iff_congr (ih ρ E) (iq ρ E)
  | conj p q ih iq => exact and_congr (ih ρ E) (iq ρ E)
  | disj p q ih iq => exact or_congr (ih ρ E) (iq ρ E)
  | all x p ih | ex x p ih =>
    have he : ∀ a, Fin.cons a E ∘ bindNames ρ x = Function.update (E ∘ ρ) x a := by
      intro a
      funext v
      by_cases hv : v = x <;> simp [bindNames, hv, Function.comp_def]
    first
    | exact forall_congr' (fun a => (ih _ _).trans (by rw [he]))
    | exact exists_congr (fun a => (ih _ _).trans (by rw [he]))

/-- Only syntactically occurring names can affect satisfaction. -/
theorem eval_congr {M V : Type*} [Membership M M] [DecidableEq V]
    (p : Formula V) (E F : V → M) (h : ∀ v ∈ p.vars, E v = F v) : p.eval E ↔ p.eval F := by
  induction p generalizing E F with
  | eq x y | mem x y =>
    have hx := h x (by simp [vars])
    have hy := h y (by simp [vars])
    simp only [eval, hx, hy]
  | neg p ih => exact not_congr (ih E F h)
  | imp p q ih iq =>
    exact imp_congr (ih E F (fun v hv => h v (List.mem_append_left _ hv)))
      (iq E F (fun v hv => h v (List.mem_append_right _ hv)))
  | iff p q ih iq =>
    exact iff_congr (ih E F (fun v hv => h v (List.mem_append_left _ hv)))
      (iq E F (fun v hv => h v (List.mem_append_right _ hv)))
  | conj p q ih iq =>
    exact and_congr (ih E F (fun v hv => h v (List.mem_append_left _ hv)))
      (iq E F (fun v hv => h v (List.mem_append_right _ hv)))
  | disj p q ih iq =>
    exact or_congr (ih E F (fun v hv => h v (List.mem_append_left _ hv)))
      (iq E F (fun v hv => h v (List.mem_append_right _ hv)))
  | all x p ih | ex x p ih =>
    have hh : ∀ a, p.eval (Function.update E x a) ↔ p.eval (Function.update F x a) := by
      intro a
      apply ih
      intro v hv
      by_cases hx : v = x
      · simp [hx]
      · simp [Function.update_of_ne hx, h v (List.mem_append_left _ hv)]
    first | exact forall_congr' hh | exact exists_congr hh

/-- Syntactic disjointness supplies set.mm's semantic freshness requirement. -/
theorem notFree_of_not_mem {M V : Type*} [Membership M M] [DecidableEq V]
    (p : Formula V) (x : V) (hx : x ∉ p.vars) :
    Wff.NotFree x (fun E : V → M => p.eval E) := by
  intro E a
  apply eval_congr
  intro v hv
  have hvx : v ≠ x := by
    intro he
    subst v
    exact hx hv
  exact Function.update_of_ne hvx a E

end Formula
end Silmaril.Logic.SetTheory.Inductive.Named

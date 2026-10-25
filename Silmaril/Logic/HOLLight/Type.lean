module

public import Std

@[expose] public section

/-!
# First-order polymorphic HOL types

Type variables are schematic parameters. Type operators have fixed arities in
a finite signature; no type-level binders or higher-kinded application occur.
Constant schemes bind a finite initial segment of type-variable indices.
-/

namespace Silmaril.Logic.HOLLight

inductive Ty where
  | var (name : Nat)
  | bool
  | ind
  | arr (domain codomain : Ty)
  | app (symbol : Nat) (arguments : List Ty)
  deriving Repr

mutual
/-- Computable equality, including nested lists of operator arguments. -/
def Ty.beq : Ty → Ty → Bool
  | .var a, .var b => a == b
  | .bool, .bool | .ind, .ind => true
  | .arr A B, .arr C D => Ty.beq A C && Ty.beq B D
  | .app c as, .app d bs => c == d && Ty.beqList as bs
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false
termination_by as bs => sizeOf as + sizeOf bs
end

instance : BEq Ty := ⟨Ty.beq⟩

private theorem beq_eq_true (a : Ty) : ∀ b, (a == b) = true ↔ a = b := by
  induction a using Ty.rec (motive_2 := fun xs => ∀ ys, Ty.beqList xs ys = true ↔ xs = ys) with
  | var i => intro b; cases b <;> simp [BEq.beq, Ty.beq]
  | bool => intro b; cases b <;> simp [BEq.beq, Ty.beq]
  | ind => intro b; cases b <;> simp [BEq.beq, Ty.beq]
  | arr A B ihA ihB =>
    intro b
    cases b <;> simp [BEq.beq, Ty.beq] at *
    case arr C D => exact and_congr (ihA C) (ihB D)
  | app c args ih =>
    intro b
    cases b <;> simp [BEq.beq, Ty.beq] at *
    case app d bs => intro _; exact ih bs
  | nil ys => cases ys <;> simp [Ty.beqList]
  | cons A as ihA ihAs ys =>
    cases ys <;> simp [BEq.beq, Ty.beqList] at *
    case cons B bs => exact and_congr (ihA B) (ihAs bs)

instance : LawfulBEq Ty where
  eq_of_beq h := (beq_eq_true _ _).mp h
  rfl := (beq_eq_true _ _).mpr rfl
instance : DecidableEq Ty := instDecidableEqOfLawfulBEq

namespace Ty

/-- Structural induction with an induction hypothesis for every operator argument. -/
@[elab_as_elim] theorem induction_on {P : Ty → Prop} (A : Ty)
    (var : ∀ i, P (.var i)) (bool : P .bool) (ind : P .ind)
    (arr : ∀ A B, P A → P B → P (.arr A B))
    (app : ∀ c args, (∀ A ∈ args, P A) → P (.app c args)) : P A :=
  Ty.rec (motive_2 := fun args => ∀ A ∈ args, P A) var bool ind arr app
    (by simp) (by
      intro A args hA hargs B hB
      rcases List.mem_cons.mp hB with h | h
      · exact h.symm ▸ hA
      · exact hargs B h) A

mutual
/-- Simultaneous, capture-free substitution of schematic type variables. -/
def subst (σ : Nat → Ty) : Ty → Ty
  | .var i => σ i
  | .bool => .bool
  | .ind => .ind
  | .arr A B => .arr (subst σ A) (subst σ B)
  | .app c args => .app c (substList σ args)
termination_by structural A => A

def substList (σ : Nat → Ty) : List Ty → List Ty
  | [] => []
  | A :: args => subst σ A :: substList σ args
termination_by structural args => args
end

@[simp] theorem substList_eq_map (σ : Nat → Ty) (args : List Ty) :
    substList σ args = args.map (subst σ) := by
  induction args with
  | nil => rfl
  | cons A args ih => simp [substList, ih]

mutual
/-- Every applied type operator is declared with exactly its number of arguments. -/
def WellFormed (ops : List Nat) : Ty → Prop
  | .var _ | .bool | .ind => True
  | .arr A B => WellFormed ops A ∧ WellFormed ops B
  | .app c args => ops[c]? = some args.length ∧ WellFormedList ops args
termination_by structural A => A

def WellFormedList (ops : List Nat) : List Ty → Prop
  | [] => True
  | A :: args => WellFormed ops A ∧ WellFormedList ops args
termination_by structural args => args
end

@[simp] theorem wellFormedList_iff (ops : List Nat) (args : List Ty) :
    WellFormedList ops args ↔ ∀ A ∈ args, WellFormed ops A := by
  induction args with
  | nil => simp [WellFormedList]
  | cons A args ih => simp [WellFormedList, ih]

mutual
/-- All schematic variables are among the first `n` indices. -/
def Scoped (n : Nat) : Ty → Prop
  | .var i => i < n
  | .bool | .ind => True
  | .arr A B => Scoped n A ∧ Scoped n B
  | .app _ args => ScopedList n args
termination_by structural A => A

def ScopedList (n : Nat) : List Ty → Prop
  | [] => True
  | A :: args => Scoped n A ∧ ScopedList n args
termination_by structural args => args
end

@[simp] theorem scopedList_iff (n : Nat) (args : List Ty) :
    ScopedList n args ↔ ∀ A ∈ args, Scoped n A := by
  induction args with
  | nil => simp [ScopedList]
  | cons A args ih => simp [ScopedList, ih]

/-- Instantiate a scheme. The default only matters for ill-scoped schemes. -/
def instantiate (args : List Ty) (A : Ty) : Ty :=
  subst (fun i => args[i]?.getD (.var i)) A

@[simp] theorem subst_var (σ : Nat → Ty) (i : Nat) : subst σ (.var i) = σ i := by simp [subst]
@[simp] theorem subst_bool (σ : Nat → Ty) : subst σ .bool = .bool := by simp [subst]
@[simp] theorem subst_ind (σ : Nat → Ty) : subst σ .ind = .ind := by simp [subst]
@[simp] theorem subst_arr (σ : Nat → Ty) (A B : Ty) :
    subst σ (.arr A B) = .arr (subst σ A) (subst σ B) := by simp [subst]
@[simp] theorem subst_app (σ : Nat → Ty) (c : Nat) (args : List Ty) :
    subst σ (.app c args) = .app c (args.map (subst σ)) := by simp [subst]

@[simp] theorem subst_id (A : Ty) : subst .var A = A := by
  induction A using induction_on with
  | var i => simp
  | bool => simp
  | ind => simp
  | arr A B ihA ihB => simp [ihA, ihB]
  | app c args ih =>
    simp only [subst_app, Ty.app.injEq, true_and]
    simpa only [List.map_id] using (List.map_congr_left (g := id) ih)

theorem subst_comp (σ τ : Nat → Ty) (A : Ty) :
    subst τ (subst σ A) = subst (fun i => subst τ (σ i)) A := by
  induction A using induction_on with
  | var i => simp
  | bool => simp
  | ind => simp
  | arr A B ihA ihB => simp [ihA, ihB]
  | app c args ih =>
    simp only [subst_app, List.map_map, Ty.app.injEq, true_and]
    exact List.map_congr_left ih

/-- Substitution only depends on variables occurring in a scoped type. -/
theorem subst_congr_scoped {n : Nat} {A : Ty} (hA : A.Scoped n)
    {σ τ : Nat → Ty} (h : ∀ i, i < n → σ i = τ i) : subst σ A = subst τ A := by
  induction A using induction_on with
  | var i => simpa using h i (by simpa [Scoped] using hA)
  | bool => simp
  | ind => simp
  | arr A B ihA ihB =>
    simp only [Scoped] at hA
    simp [ihA hA.1, ihB hA.2]
  | app c args ih =>
    simp only [Scoped, scopedList_iff] at hA
    simp only [subst_app, Ty.app.injEq, true_and]
    exact List.map_congr_left (fun A hmem => ih A hmem (hA A hmem))

theorem WellFormed.subst {ops : List Nat} {A : Ty} (hA : A.WellFormed ops)
    {σ : Nat → Ty} (hσ : ∀ i, (σ i).WellFormed ops) :
    (A.subst σ).WellFormed ops := by
  induction A using induction_on with
  | var i => simpa using hσ i
  | bool => simp [WellFormed]
  | ind => simp [WellFormed]
  | arr A B ihA ihB =>
    simp only [WellFormed] at hA
    simpa [WellFormed] using And.intro (ihA hA.1) (ihB hA.2)
  | app c args ih =>
    simp only [WellFormed, wellFormedList_iff] at hA
    simp only [subst_app, WellFormed, wellFormedList_iff]
    refine ⟨by simpa using hA.1, ?_⟩
    intro B hB
    obtain ⟨A, hmem, rfl⟩ := List.mem_map.mp hB
    exact ih A hmem (hA.2 A hmem)

theorem Scoped.subst {n m : Nat} {A : Ty} (hA : A.Scoped n)
    {σ : Nat → Ty} (hσ : ∀ i, i < n → (σ i).Scoped m) :
    (A.subst σ).Scoped m := by
  induction A using induction_on with
  | var i => simpa using hσ i (by simpa [Scoped] using hA)
  | bool => simp [Scoped]
  | ind => simp [Scoped]
  | arr A B ihA ihB =>
    simp only [Scoped] at hA
    simpa [Scoped] using And.intro (ihA hA.1) (ihB hA.2)
  | app c args ih =>
    simp only [Scoped, scopedList_iff] at hA
    simp only [subst_app, Scoped, scopedList_iff]
    intro B hB
    obtain ⟨A, hmem, rfl⟩ := List.mem_map.mp hB
    exact ih A hmem (hA A hmem)

theorem Scoped.mono {n m : Nat} {A : Ty} (hA : A.Scoped n) (hnm : n ≤ m) :
    A.Scoped m := by
  simpa using hA.subst (σ := Ty.var) (fun _ hi => by simpa [Scoped] using Nat.lt_of_lt_of_le hi hnm)

theorem WellFormed.instantiate {ops : List Nat} {A : Ty} (hA : A.WellFormed ops)
    {args : List Ty} (hargs : ∀ B ∈ args, B.WellFormed ops) :
    (A.instantiate args).WellFormed ops := by
  apply hA.subst
  intro i
  cases h : args[i]? with
  | none => simp [WellFormed]
  | some B => exact hargs B (List.mem_of_getElem? h)

theorem Scoped.instantiate {n m : Nat} {A : Ty} (hA : A.Scoped n)
    {args : List Ty} (hlen : args.length = n) (hargs : ∀ B ∈ args, B.Scoped m) :
    (A.instantiate args).Scoped m := by
  apply hA.subst
  intro i hi
  have hi' : i < args.length := hlen ▸ hi
  simpa [List.getElem?_eq_getElem hi'] using hargs args[i] (List.getElem_mem hi')

/-- Instantiating a closed scheme commutes with substituting its arguments. -/
theorem subst_instantiate {n : Nat} {A : Ty} (hA : A.Scoped n)
    {args : List Ty} (hlen : args.length = n) (σ : Nat → Ty) :
    (A.instantiate args).subst σ = A.instantiate (args.map (subst σ)) := by
  unfold instantiate
  rw [subst_comp]
  apply subst_congr_scoped hA
  intro i hi
  have hi' : i < args.length := hlen ▸ hi
  simp [List.getElem?_map, List.getElem?_eq_getElem hi']

end Ty

structure Scheme where
  arity : Nat
  body : Ty
  deriving DecidableEq, Repr

structure Signature where
  tyOps : List Nat
  consts : List Scheme
  deriving DecidableEq, Repr

def Scheme.WellFormed (ops : List Nat) (s : Scheme) : Prop :=
  s.body.WellFormed ops ∧ s.body.Scoped s.arity

def Signature.Valid (sig : Signature) : Prop :=
  ∀ s ∈ sig.consts, s.WellFormed sig.tyOps

/-- Declared constant schemes can be recovered from a successful lookup. -/
theorem Signature.Valid.lookup {sig : Signature} (valid : sig.Valid)
    {c : Nat} {s : Scheme} (lookup : sig.consts[c]? = some s) :
    s.WellFormed sig.tyOps :=
  valid s (List.mem_of_getElem? lookup)

theorem Scheme.WellFormed.instantiate {ops : List Nat} {s : Scheme}
    (hs : s.WellFormed ops) {args : List Ty}
    (hargs : ∀ A ∈ args, A.WellFormed ops) :
    (s.body.instantiate args).WellFormed ops :=
  hs.1.instantiate hargs

theorem Scheme.WellFormed.subst_instantiate {ops : List Nat} {s : Scheme}
    (hs : s.WellFormed ops) {args : List Ty} (hlen : args.length = s.arity)
    (σ : Nat → Ty) :
    (s.body.instantiate args).subst σ = s.body.instantiate (args.map (Ty.subst σ)) :=
  Ty.subst_instantiate hs.2 hlen σ

end Silmaril.Logic.HOLLight

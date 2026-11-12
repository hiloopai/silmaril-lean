module

public import Silmaril.Logic.Metatheory.Theory.Model
public import Silmaril.Raw.SSA.Isotope.Theory.Equational
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-!
# Raw constructor algebras of the let calculi

Raw scoped terms are initial algebras for their full constructor signatures.
The signature records every binder depth. This is independent of erased
calculus laws: quotients can be formed by any compatible raw theory.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetSeq.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory.TheoryModel CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- Constructor symbols, with binder depth as output sort. -/
inductive Op (ν : Type u) (Φ : Type v) : Nat → Type (max u v) where
  | fv {n : Nat} (x : ν) : Op ν Φ n
  | bv {n : Nat} (i : Fin n) : Op ν Φ n
  | op {n : Nat} (f : Φ) : Op ν Φ n
  | let₁ {n : Nat}  : Op ν Φ n
  | unit {n : Nat}  : Op ν Φ n
  | pair {n : Nat}  : Op ν Φ n
  | let₂ {n : Nat}  : Op ν Φ n

/-- The finite number of recursive children of a constructor. -/
abbrev arity {n : Nat} : Op ν Φ n → Nat
  | .fv _ => 0
  | .bv _ => 0
  | .op _ => 1
  | .let₁ => 2
  | .unit => 0
  | .pair => 2
  | .let₂ => 2

/-- Children under a binder inhabit the larger scope. -/
abbrev argSort {n : Nat} (o : Op ν Φ n) : Fin (arity o) → Nat :=
  match o with
  | .fv _ => (fun j => Fin.elim0 j)
  | .bv _ => (fun j => Fin.elim0 j)
  | .op _ => fun _ => n
  | .let₁ => Fin.cases n (fun _ => n + 1)
  | .unit => (fun j => Fin.elim0 j)
  | .pair => fun _ => n
  | .let₂ => Fin.cases n (fun _ => n + 2)

abbrev signature (ν : Type u) (Φ : Type v) : Silmaril.Logic.Metatheory.TheoryModel.Signature Nat where
  Op := Op ν Φ
  arity := arity
  argSort := argSort

/-- The ordinary raw syntax, equipped with every constructor operation. -/
def termAlgebra (ν : Type u) (Φ : Type v) : Algebra (signature ν Φ) where
  Carrier := Tm ν Φ
  op o args := match o with
    | .fv x => .fv x
    | .bv i => .bv i
    | .op f => .op f (args 0)
    | .let₁ => .let₁ (args 0) (args 1)
    | .unit => .unit
    | .pair => .pair (args 0) (args 1)
    | .let₂ => .let₂ (args 0) (args 1)

/-- Structural interpretation into an arbitrary constructor algebra. -/
def fold (A : Algebra (signature ν Φ)) : {n : Nat} → Tm ν Φ n → A.Carrier n
  | _, .fv x => A.op (.fv x) (fun j => Fin.elim0 j)
  | _, .bv i => A.op (.bv i) (fun j => Fin.elim0 j)
  | _, .op f a => A.op (.op f) (fun _ => fold A a)
  | _, .let₁ a b => A.op .let₁ (Fin.cases (fold A a) (fun _ => fold A b))
  | _, .unit => A.op .unit (fun j => Fin.elim0 j)
  | _, .pair a b => A.op .pair (Fin.cases (fold A a) (fun _ => fold A b))
  | _, .let₂ a b => A.op .let₂ (Fin.cases (fold A a) (fun _ => fold A b))

/-- Interpretation preserves all constructor operations on arbitrary arguments. -/
def foldHom (A : Algebra (signature ν Φ)) : termAlgebra ν Φ ⟶ A where
  map := fold A
  comm o args := by
    cases o <;> dsimp [termAlgebra, fold]
    all_goals congr 1; funext j; fin_cases j <;> rfl

/-- Every constructor homomorphism from syntax is structural interpretation. -/
theorem hom_eq_fold (A : Algebra (signature ν Φ)) (f : termAlgebra ν Φ ⟶ A) :
    f = foldHom A := by
  apply Algebra.Hom.ext
  intro n t
  induction t with
  | @fv n x =>
    have h := f.comm (.fv (n := n) x) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | bv i =>
    have h := f.comm (.bv i) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | op g a ha =>
    have h := f.comm (.op g) (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
  | let₁ a b ha hb =>
    have h := f.comm .let₁ (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
  | @unit n =>
    have h := f.comm (Op.unit (n := n)) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | pair a b ha hb =>
    have h := f.comm .pair (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
  | let₂ a b ha hb =>
    have h := f.comm .let₂ (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb

/-- Raw syntax is initial among all algebras of its constructor signature. -/
def termIsInitial (ν : Type u) (Φ : Type v) : IsInitial (termAlgebra ν Φ) := by
  letI (A : Algebra (signature ν Φ)) : Unique (termAlgebra ν Φ ⟶ A) :=
    ⟨⟨foldHom A⟩, hom_eq_fold A⟩
  exact IsInitial.ofUnique _

end Silmaril.Isotope.LetSeq.LocallyNameless.RawModels

namespace Silmaril.Isotope.LetCase.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory.TheoryModel CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- Constructor symbols, with binder depth as output sort. -/
inductive Op (ν : Type u) (Φ : Type v) : Nat → Type (max u v) where
  | fv {n : Nat} (x : ν) : Op ν Φ n
  | bv {n : Nat} (i : Fin n) : Op ν Φ n
  | op {n : Nat} (f : Φ) : Op ν Φ n
  | let₁ {n : Nat}  : Op ν Φ n
  | unit {n : Nat}  : Op ν Φ n
  | pair {n : Nat}  : Op ν Φ n
  | let₂ {n : Nat}  : Op ν Φ n
  | inl {n : Nat}  : Op ν Φ n
  | inr {n : Nat}  : Op ν Φ n
  | case {n : Nat}  : Op ν Φ n
  | abort {n : Nat}  : Op ν Φ n

/-- The finite number of recursive children of a constructor. -/
abbrev arity {n : Nat} : Op ν Φ n → Nat
  | .fv _ => 0
  | .bv _ => 0
  | .op _ => 1
  | .let₁ => 2
  | .unit => 0
  | .pair => 2
  | .let₂ => 2
  | .inl => 1
  | .inr => 1
  | .case => 3
  | .abort => 1

/-- Children under a binder inhabit the larger scope. -/
abbrev argSort {n : Nat} (o : Op ν Φ n) : Fin (arity o) → Nat :=
  match o with
  | .fv _ => (fun j => Fin.elim0 j)
  | .bv _ => (fun j => Fin.elim0 j)
  | .op _ => fun _ => n
  | .let₁ => Fin.cases n (fun _ => n + 1)
  | .unit => (fun j => Fin.elim0 j)
  | .pair => fun _ => n
  | .let₂ => Fin.cases n (fun _ => n + 2)
  | .inl => fun _ => n
  | .inr => fun _ => n
  | .case => Fin.cases n (fun _ => n + 1)
  | .abort => fun _ => n

abbrev signature (ν : Type u) (Φ : Type v) : Silmaril.Logic.Metatheory.TheoryModel.Signature Nat where
  Op := Op ν Φ
  arity := arity
  argSort := argSort

/-- The ordinary raw syntax, equipped with every constructor operation. -/
def termAlgebra (ν : Type u) (Φ : Type v) : Algebra (signature ν Φ) where
  Carrier := Tm ν Φ
  op o args := match o with
    | .fv x => .fv x
    | .bv i => .bv i
    | .op f => .op f (args 0)
    | .let₁ => .let₁ (args 0) (args 1)
    | .unit => .unit
    | .pair => .pair (args 0) (args 1)
    | .let₂ => .let₂ (args 0) (args 1)
    | .inl => .inl (args 0)
    | .inr => .inr (args 0)
    | .case => .case (args 0) (args 1) (args 2)
    | .abort => .abort (args 0)

/-- Structural interpretation into an arbitrary constructor algebra. -/
def fold (A : Algebra (signature ν Φ)) : {n : Nat} → Tm ν Φ n → A.Carrier n
  | _, .fv x => A.op (.fv x) (fun j => Fin.elim0 j)
  | _, .bv i => A.op (.bv i) (fun j => Fin.elim0 j)
  | _, .op f a => A.op (.op f) (fun _ => fold A a)
  | _, .let₁ a b => A.op .let₁ (Fin.cases (fold A a) (fun _ => fold A b))
  | _, .unit => A.op .unit (fun j => Fin.elim0 j)
  | _, .pair a b => A.op .pair (Fin.cases (fold A a) (fun _ => fold A b))
  | _, .let₂ a b => A.op .let₂ (Fin.cases (fold A a) (fun _ => fold A b))
  | _, .inl a => A.op .inl (fun _ => fold A a)
  | _, .inr a => A.op .inr (fun _ => fold A a)
  | _, .case a b c => A.op .case (Fin.cases (fold A a) (Fin.cases (fold A b) (fun _ => fold A c)))
  | _, .abort a => A.op .abort (fun _ => fold A a)

/-- Interpretation preserves all constructor operations on arbitrary arguments. -/
def foldHom (A : Algebra (signature ν Φ)) : termAlgebra ν Φ ⟶ A where
  map := fold A
  comm o args := by
    cases o <;> dsimp [termAlgebra, fold]
    all_goals congr 1; funext j; fin_cases j <;> rfl

/-- Every constructor homomorphism from syntax is structural interpretation. -/
theorem hom_eq_fold (A : Algebra (signature ν Φ)) (f : termAlgebra ν Φ ⟶ A) :
    f = foldHom A := by
  apply Algebra.Hom.ext
  intro n t
  induction t with
  | @fv n x =>
    have h := f.comm (.fv (n := n) x) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | bv i =>
    have h := f.comm (.bv i) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | op g a ha =>
    have h := f.comm (.op g) (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
  | let₁ a b ha hb =>
    have h := f.comm .let₁ (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
  | @unit n =>
    have h := f.comm (Op.unit (n := n)) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | pair a b ha hb =>
    have h := f.comm .pair (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
  | let₂ a b ha hb =>
    have h := f.comm .let₂ (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
  | inl a ha =>
    have h := f.comm .inl (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
  | inr a ha =>
    have h := f.comm .inr (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
  | case a b c ha hb hc =>
    have h := f.comm .case (Fin.cases a (Fin.cases b (fun _ => c)))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
    · exact hc
  | abort a ha =>
    have h := f.comm .abort (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha

/-- Raw syntax is initial among all algebras of its constructor signature. -/
def termIsInitial (ν : Type u) (Φ : Type v) : IsInitial (termAlgebra ν Φ) := by
  letI (A : Algebra (signature ν Φ)) : Unique (termAlgebra ν Φ ⟶ A) :=
    ⟨⟨foldHom A⟩, hom_eq_fold A⟩
  exact IsInitial.ofUnique _

end Silmaril.Isotope.LetCase.LocallyNameless.RawModels

namespace Silmaril.Isotope.LetIter.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory.TheoryModel CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- Constructor symbols, with binder depth as output sort. -/
inductive Op (ν : Type u) (Φ : Type v) : Nat → Type (max u v) where
  | fv {n : Nat} (x : ν) : Op ν Φ n
  | bv {n : Nat} (i : Fin n) : Op ν Φ n
  | op {n : Nat} (f : Φ) : Op ν Φ n
  | let₁ {n : Nat}  : Op ν Φ n
  | unit {n : Nat}  : Op ν Φ n
  | pair {n : Nat}  : Op ν Φ n
  | let₂ {n : Nat}  : Op ν Φ n
  | inl {n : Nat}  : Op ν Φ n
  | inr {n : Nat}  : Op ν Φ n
  | case {n : Nat}  : Op ν Φ n
  | abort {n : Nat}  : Op ν Φ n
  | iter {n : Nat}  : Op ν Φ n

/-- The finite number of recursive children of a constructor. -/
abbrev arity {n : Nat} : Op ν Φ n → Nat
  | .fv _ => 0
  | .bv _ => 0
  | .op _ => 1
  | .let₁ => 2
  | .unit => 0
  | .pair => 2
  | .let₂ => 2
  | .inl => 1
  | .inr => 1
  | .case => 3
  | .abort => 1
  | .iter => 2

/-- Children under a binder inhabit the larger scope. -/
abbrev argSort {n : Nat} (o : Op ν Φ n) : Fin (arity o) → Nat :=
  match o with
  | .fv _ => (fun j => Fin.elim0 j)
  | .bv _ => (fun j => Fin.elim0 j)
  | .op _ => fun _ => n
  | .let₁ => Fin.cases n (fun _ => n + 1)
  | .unit => (fun j => Fin.elim0 j)
  | .pair => fun _ => n
  | .let₂ => Fin.cases n (fun _ => n + 2)
  | .inl => fun _ => n
  | .inr => fun _ => n
  | .case => Fin.cases n (fun _ => n + 1)
  | .abort => fun _ => n
  | .iter => Fin.cases n (fun _ => n + 1)

abbrev signature (ν : Type u) (Φ : Type v) : Silmaril.Logic.Metatheory.TheoryModel.Signature Nat where
  Op := Op ν Φ
  arity := arity
  argSort := argSort

/-- The ordinary raw syntax, equipped with every constructor operation. -/
def termAlgebra (ν : Type u) (Φ : Type v) : Algebra (signature ν Φ) where
  Carrier := Tm ν Φ
  op o args := match o with
    | .fv x => .fv x
    | .bv i => .bv i
    | .op f => .op f (args 0)
    | .let₁ => .let₁ (args 0) (args 1)
    | .unit => .unit
    | .pair => .pair (args 0) (args 1)
    | .let₂ => .let₂ (args 0) (args 1)
    | .inl => .inl (args 0)
    | .inr => .inr (args 0)
    | .case => .case (args 0) (args 1) (args 2)
    | .abort => .abort (args 0)
    | .iter => .iter (args 0) (args 1)

/-- Structural interpretation into an arbitrary constructor algebra. -/
def fold (A : Algebra (signature ν Φ)) : {n : Nat} → Tm ν Φ n → A.Carrier n
  | _, .fv x => A.op (.fv x) (fun j => Fin.elim0 j)
  | _, .bv i => A.op (.bv i) (fun j => Fin.elim0 j)
  | _, .op f a => A.op (.op f) (fun _ => fold A a)
  | _, .let₁ a b => A.op .let₁ (Fin.cases (fold A a) (fun _ => fold A b))
  | _, .unit => A.op .unit (fun j => Fin.elim0 j)
  | _, .pair a b => A.op .pair (Fin.cases (fold A a) (fun _ => fold A b))
  | _, .let₂ a b => A.op .let₂ (Fin.cases (fold A a) (fun _ => fold A b))
  | _, .inl a => A.op .inl (fun _ => fold A a)
  | _, .inr a => A.op .inr (fun _ => fold A a)
  | _, .case a b c => A.op .case (Fin.cases (fold A a) (Fin.cases (fold A b) (fun _ => fold A c)))
  | _, .abort a => A.op .abort (fun _ => fold A a)
  | _, .iter a b => A.op .iter (Fin.cases (fold A a) (fun _ => fold A b))

/-- Interpretation preserves all constructor operations on arbitrary arguments. -/
def foldHom (A : Algebra (signature ν Φ)) : termAlgebra ν Φ ⟶ A where
  map := fold A
  comm o args := by
    cases o <;> dsimp [termAlgebra, fold]
    all_goals congr 1; funext j; fin_cases j <;> rfl

/-- Every constructor homomorphism from syntax is structural interpretation. -/
theorem hom_eq_fold (A : Algebra (signature ν Φ)) (f : termAlgebra ν Φ ⟶ A) :
    f = foldHom A := by
  apply Algebra.Hom.ext
  intro n t
  induction t with
  | @fv n x =>
    have h := f.comm (.fv (n := n) x) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | bv i =>
    have h := f.comm (.bv i) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | op g a ha =>
    have h := f.comm (.op g) (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
  | let₁ a b ha hb =>
    have h := f.comm .let₁ (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
  | @unit n =>
    have h := f.comm (Op.unit (n := n)) (fun j => Fin.elim0 j)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    exact Fin.elim0 j
  | pair a b ha hb =>
    have h := f.comm .pair (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
  | let₂ a b ha hb =>
    have h := f.comm .let₂ (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
  | inl a ha =>
    have h := f.comm .inl (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
  | inr a ha =>
    have h := f.comm .inr (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
  | case a b c ha hb hc =>
    have h := f.comm .case (Fin.cases a (Fin.cases b (fun _ => c)))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb
    · exact hc
  | abort a ha =>
    have h := f.comm .abort (fun _ => a)
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
  | iter a b ha hb =>
    have h := f.comm .iter (Fin.cases a (fun _ => b))
    refine h.trans ?_
    change A.op _ _ = A.op _ _
    congr 1
    funext j
    fin_cases j
    · exact ha
    · exact hb

/-- Raw syntax is initial among all algebras of its constructor signature. -/
def termIsInitial (ν : Type u) (Φ : Type v) : IsInitial (termAlgebra ν Φ) := by
  letI (A : Algebra (signature ν Φ)) : Unique (termAlgebra ν Φ ⟶ A) :=
    ⟨⟨foldHom A⟩, hom_eq_fold A⟩
  exact IsInitial.ofUnique _

end Silmaril.Isotope.LetIter.LocallyNameless.RawModels


module

public import Silmaril.Raw.SSA.Isotope.Refinement.Typing
public import Silmaril.Logic.Metatheory.Theory.Model
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

@[expose] public section
noncomputable section

/-! # Constructor algebras for quantitative syntax

The sorts retain the entire quantitative context.  Each legal context split,
fragment permission, and loop linearity condition is an operation parameter.
The free algebra retains native typing derivations at the top effect; effect
bounds are proof-irrelevant premises of these constructors.  This gives actual
operation-preserving homomorphisms and an initiality theorem for all three
fragments, independently of any later quotient by refinement laws.
-/

namespace Silmaril.Isotope.Refinement.Models

open Silmaril.Logic.Metatheory.TheoryModel CategoryTheory

universe u v w x y

structure TypingIndex (τ : Type u) where
  scope : Nat
  context : QCtx τ scope
  result : τ

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]

inductive Operation (F : Fragment) : TypingIndex τ → Type (max u v)
  | var {n : Nat} {Γ : QCtx τ n} (i : Fin n) (h : Γ.VarAllowed i) :
      Operation F ⟨n, Γ, (Γ i).1⟩
  | op {n : Nat} {Γ : QCtx τ n} (f : Φ) : Operation F ⟨n, Γ, instrTrg f⟩
  | let₁ {n : Nat} {Γ Γl Γr : QCtx τ n} (A B : τ) (s : Γ.Split Γl Γr) :
      Operation F ⟨n, Γ, B⟩
  | unit {n : Nat} {Γ : QCtx τ n} (h : Γ.Discardable) : Operation F ⟨n, Γ, Silmaril.unit⟩
  | pair {n : Nat} {Γ Γl Γr : QCtx τ n} (A B : τ) (s : Γ.Split Γl Γr) :
      Operation F ⟨n, Γ, product A B⟩
  | let₂ {n : Nat} {Γ Γl Γr : QCtx τ n} (A B C : τ) (s : Γ.Split Γl Γr) :
      Operation F ⟨n, Γ, C⟩
  | inl {n : Nat} {Γ : QCtx τ n} (A B : τ) (f : F.HasCase) :
      Operation F ⟨n, Γ, coprod A B⟩
  | inr {n : Nat} {Γ : QCtx τ n} (A B : τ) (f : F.HasCase) :
      Operation F ⟨n, Γ, coprod A B⟩
  | case {n : Nat} {Γ Γl Γr : QCtx τ n} (A B C : τ) (f : F.HasCase)
      (s : Γ.Split Γl Γr) : Operation F ⟨n, Γ, C⟩
  | abort {n : Nat} {Γ : QCtx τ n} (C : τ) (f : F.HasCase) : Operation F ⟨n, Γ, C⟩
  | iter {n : Nat} {Γ Γl Γr : QCtx τ n} (A B : τ) (f : F.HasIter)
      (s : Γ.Split Γl Γr) (u : Γl.linearity = ⊤) : Operation F ⟨n, Γ, B⟩

namespace Operation

variable {F : Fragment}

abbrev arity : {i : TypingIndex τ} → Operation (Φ := Φ) F i → Nat
  | _, .var _ _ => 0
  | _, .op _ => 1
  | _, .let₁ _ _ _ => 2
  | _, .unit _ => 0
  | _, .pair _ _ _ => 2
  | _, .let₂ _ _ _ _ => 2
  | _, .inl _ _ _ => 1
  | _, .inr _ _ _ => 1
  | _, .case _ _ _ _ _ => 3
  | _, .abort _ _ => 1
  | _, .iter _ _ _ _ _ => 2

abbrev argSort : {i : TypingIndex τ} → (o : Operation (Φ := Φ) F i) →
    Fin o.arity → TypingIndex τ
  | _, .var _ _, j => Fin.elim0 j
  | _, .op (Γ := Γ) f, _ => ⟨_, Γ, instrSrc f⟩
  | _, .let₁ (Γl := Γl) (Γr := Γr) A B _, j =>
      Fin.cases ⟨_, Γr, A⟩ (fun _ => ⟨_, Γl.snoc A, B⟩) j
  | _, .unit _, j => Fin.elim0 j
  | _, .pair (Γl := Γl) (Γr := Γr) A B _, j =>
      Fin.cases ⟨_, Γl, A⟩ (fun _ => ⟨_, Γr, B⟩) j
  | _, .let₂ (Γl := Γl) (Γr := Γr) A B C _, j =>
      Fin.cases ⟨_, Γr, product A B⟩ (fun _ => ⟨_, (Γl.snoc A).snoc B, C⟩) j
  | _, .inl (Γ := Γ) A _ _, _ => ⟨_, Γ, A⟩
  | _, .inr (Γ := Γ) _ B _, _ => ⟨_, Γ, B⟩
  | _, .case (Γl := Γl) (Γr := Γr) A B C _ _, j =>
      Fin.cases ⟨_, Γr, coprod A B⟩
        (Fin.cases ⟨_, Γl.snoc A, C⟩ (fun _ => ⟨_, Γl.snoc B, C⟩)) j
  | _, .abort (Γ := Γ) _ _, _ => ⟨_, Γ, Silmaril.empty⟩
  | _, .iter (Γl := Γl) (Γr := Γr) A B _ _ _, j =>
      Fin.cases ⟨_, Γr, A⟩ (fun _ => ⟨_, Γl.snoc A, coprod B A⟩) j

end Operation

abbrev signature (Φ : Type v) [HasTy Φ τ] (F : Fragment) : Silmaril.Logic.Metatheory.TheoryModel.Signature (TypingIndex τ) where
  Op := Operation (Φ := Φ) F
  arity := Operation.arity
  argSort := Operation.argSort

variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

abbrev Carrier (Φ : Type v) [HasTy Φ τ] (ε : Type w) [EffectSystem ε] [HasEff Φ ε]
    (F : Fragment) (i : TypingIndex τ) :=
  Σ t : Term Φ i.scope, HasType F i.context (⊤ : ε) t i.result

/-- The proposition-valued typing fiber of the written calculus. -/
abbrev TypedTerm (Φ : Type v) [HasTy Φ τ] (ε : Type w) [EffectSystem ε] [HasEff Φ ε]
    (F : Fragment) (i : TypingIndex τ) :=
  {t : Term Φ i.scope // Nonempty (HasType F i.context (⊤ : ε) t i.result)}

/-- Forget only the choice of typing derivation, retaining its existence. -/
def eraseCarrier {F : Fragment} {i : TypingIndex τ} (a : Carrier Φ ε F i) :
    TypedTerm Φ ε F i := ⟨a.1, ⟨a.2⟩⟩

theorem eraseCarrier_surjective {F : Fragment} {i : TypingIndex τ} :
    Function.Surjective (eraseCarrier (Φ := Φ) (ε := ε) (F := F) (i := i)) := by
  rintro ⟨t, ⟨h⟩⟩
  exact ⟨⟨t, h⟩, rfl⟩

variable {F : Fragment}

def syntaxOp : {i : TypingIndex τ} → (o : Operation (Φ := Φ) F i) →
    ((j : Fin o.arity) → Carrier Φ ε F (o.argSort j)) → Carrier Φ ε F i
  | _, .var i h, _ => ⟨.bv i, .var i h⟩
  | _, .op f, a => ⟨.op f (a 0).1, .op le_top (a 0).2⟩
  | _, .let₁ _ _ s, a => ⟨.let₁ (a 0).1 (a 1).1, .let₁ s (a 0).2 (a 1).2⟩
  | _, .unit h, _ => ⟨.unit, .unit h⟩
  | _, .pair _ _ s, a => ⟨.pair (a 0).1 (a 1).1, .pair s (a 0).2 (a 1).2⟩
  | _, .let₂ _ _ _ s, a => ⟨.let₂ (a 0).1 (a 1).1, .let₂ s (a 0).2 (a 1).2⟩
  | _, .inl _ _ f, a => ⟨.inl (a 0).1, .inl f (a 0).2⟩
  | _, .inr _ _ f, a => ⟨.inr (a 0).1, .inr f (a 0).2⟩
  | _, .case _ _ _ f s, a =>
      ⟨.case (a 0).1 (a 1).1 (a 2).1, .case f s (a 0).2 (a 1).2 (a 2).2⟩
  | _, .abort _ f, a => ⟨.abort (a 0).1, .abort f (a 0).2⟩
  | _, .iter _ _ f s u, a =>
      ⟨.iter (a 0).1 (a 1).1, .iter f s u EffectSystem.iterable_top (a 0).2 (a 1).2⟩

def syntaxAlgebra (Φ : Type v) [HasTy Φ τ] (ε : Type w) [EffectSystem ε] [HasEff Φ ε]
    (F : Fragment) : Algebra (signature (τ := τ) Φ F) where
  Carrier := Carrier Φ ε F
  op := syntaxOp

/-- Structural interpretation remembers every context split and type choice. -/
def denote (X : Algebra.{u, max u v, x} (signature (τ := τ) Φ F)) :
    {n : Nat} → {Γ : QCtx τ n} → {e : ε} → {t : Term Φ n} → {A : τ} →
      HasType F Γ e t A → X.Carrier ⟨n, Γ, A⟩
  | _, _, _, _, _, .var i h => X.op (.var i h) (fun j => Fin.elim0 j)
  | _, _, _, _, _, .op (f := f) _ h => X.op (.op f) (fun _ => denote X h)
  | _, _, _, _, _, .let₁ (A := A) (B := B) s h k =>
      X.op (.let₁ A B s) (Fin.cases (denote X h) (fun _ => denote X k))
  | _, _, _, _, _, .unit h => X.op (.unit h) (fun j => Fin.elim0 j)
  | _, _, _, _, _, .pair (A := A) (B := B) s h k =>
      X.op (.pair A B s) (Fin.cases (denote X h) (fun _ => denote X k))
  | _, _, _, _, _, .let₂ (A := A) (B := B) (C := C) s h k =>
      X.op (.let₂ A B C s) (Fin.cases (denote X h) (fun _ => denote X k))
  | _, _, _, _, _, .inl (A := A) (B := B) f h => X.op (.inl A B f) (fun _ => denote X h)
  | _, _, _, _, _, .inr (A := A) (B := B) f h => X.op (.inr A B f) (fun _ => denote X h)
  | _, _, _, _, _, .case (A := A) (B := B) (C := C) f s h l r =>
      X.op (.case A B C f s)
        (Fin.cases (denote X h) (Fin.cases (denote X l) (fun _ => denote X r)))
  | _, _, _, _, _, .abort (A := A) f h => X.op (.abort A f) (fun _ => denote X h)
  | _, _, _, _, _, .iter (A := A) (B := B) f s u _ h k =>
      X.op (.iter A B f s u) (Fin.cases (denote X h) (fun _ => denote X k))

/-- Enlarging an effect annotation does not change structural interpretation. -/
@[simp] theorem denote_effectMono (X : Algebra.{u, max u v, x} (signature (τ := τ) Φ F))
    {n : Nat} {Γ : QCtx τ n} {e e' : ε} {t : Term Φ n} {A : τ}
    (d : HasType F Γ e t A) (he : e ≤ e') : denote X (d.effectMono he) = denote X d := by
  induction d <;> simp only [HasType.effectMono, denote]
  all_goals
    congr 1
    funext j
    fin_cases j <;> solve_by_elim

/-- Structural interpretation is natural in every operation-preserving map,
even when its source and target carriers have different universes. -/
theorem denote_naturality
    {X : Algebra.{u, max u v, x} (signature (τ := τ) Φ F)}
    {Y : Algebra.{u, max u v, y} (signature (τ := τ) Φ F)} (f : Algebra.Hom X Y)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (d : HasType F Γ e t A) : f.map (denote X d) = denote Y d := by
  induction d <;> simp only [denote, f.comm]
  all_goals
    congr 1
    funext j
    fin_cases j <;> assumption

def fold (X : Algebra.{u, max u v, x} (signature (τ := τ) Φ F)) :
    Algebra.Hom (syntaxAlgebra Φ ε F) X where
  map a := denote X a.2
  comm o a := by
    cases o <;> dsimp only [syntaxAlgebra, syntaxOp, denote]
    all_goals congr 1; funext j; fin_cases j <;> rfl

/-- All homomorphisms out of the native derivation algebra are structural folds. -/
private theorem map_denote_aux (X : Algebra.{u, max u v, x} (signature (τ := τ) Φ F))
    (f : Algebra.Hom (syntaxAlgebra Φ ε F) X)
    {n : Nat} {Γ : QCtx τ n} {t : Term Φ n} {A : τ}
    (e : ε) (d : HasType F Γ e t A) (he : e = ⊤) :
    f.map ⟨t, he ▸ d⟩ = denote X d := by
  revert he
  induction d with
  | @var n Γ e i h =>
    intro he
    subst e
    exact (f.comm (.var (Γ := Γ) i h) (fun j => Fin.elim0 j)).trans
      (congrArg (X.op (.var (Γ := Γ) i h)) (funext fun j => Fin.elim0 j))
  | @unit n Γ e h =>
    intro he
    subst e
    exact (f.comm (.unit (Γ := Γ) h) (fun j => Fin.elim0 j)).trans
      (congrArg (X.op (.unit (Γ := Γ) h)) (funext fun j => Fin.elim0 j))
  | @op n Γ e g a hf ha ih =>
    intro he
    subst e
    exact (f.comm (.op (Γ := Γ) g) (fun _ => ⟨a, ha⟩)).trans
      (congrArg (X.op (.op (Γ := Γ) g)) (funext fun _ => ih rfl))
  | @let₁ n Γ Γl Γr e a b A B s ha hb iha ihb =>
    intro he
    subst e
    refine (f.comm (.let₁ A B s) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
    apply congrArg (X.op (.let₁ A B s))
    funext j
    fin_cases j <;> first | exact iha rfl | exact ihb rfl
  | @pair n Γ Γl Γr e a b A B s ha hb iha ihb =>
    intro he
    subst e
    refine (f.comm (.pair A B s) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
    apply congrArg (X.op (.pair A B s))
    funext j
    fin_cases j <;> first | exact iha rfl | exact ihb rfl
  | @let₂ n Γ Γl Γr e a b A B C s ha hb iha ihb =>
    intro he
    subst e
    refine (f.comm (.let₂ A B C s) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
    apply congrArg (X.op (.let₂ A B C s))
    funext j
    fin_cases j <;> first | exact iha rfl | exact ihb rfl
  | @inl n Γ e a A B hg ha ih =>
    intro he
    subst e
    exact (f.comm (.inl (Γ := Γ) A B hg) (fun _ => ⟨a, ha⟩)).trans
      (congrArg (X.op (.inl (Γ := Γ) A B hg)) (funext fun _ => ih rfl))
  | @inr n Γ e a A B hg ha ih =>
    intro he
    subst e
    exact (f.comm (.inr (Γ := Γ) A B hg) (fun _ => ⟨a, ha⟩)).trans
      (congrArg (X.op (.inr (Γ := Γ) A B hg)) (funext fun _ => ih rfl))
  | @case n Γ Γl Γr e a l r A B C hg s ha hl hr iha ihl ihr =>
    intro he
    subst e
    refine (f.comm (.case A B C hg s)
      (Fin.cases ⟨a, ha⟩ (Fin.cases ⟨l, hl⟩ (fun _ => ⟨r, hr⟩)))).trans ?_
    apply congrArg (X.op (.case A B C hg s))
    funext j
    fin_cases j <;> first | exact iha rfl | exact ihl rfl | exact ihr rfl
  | @abort n Γ e a A hg ha ih =>
    intro he
    subst e
    exact (f.comm (.abort (Γ := Γ) A hg) (fun _ => ⟨a, ha⟩)).trans
      (congrArg (X.op (.abort (Γ := Γ) A hg)) (funext fun _ => ih rfl))
  | @iter n Γ Γl Γr e a b A B hg s u it ha hb iha ihb =>
    intro he
    subst e
    refine (f.comm (.iter A B hg s u) (Fin.cases ⟨a, ha⟩ (fun _ => ⟨b, hb⟩))).trans ?_
    apply congrArg (X.op (.iter A B hg s u))
    funext j
    fin_cases j <;> first | exact iha rfl | exact ihb rfl

/-- Every homomorphism agrees with interpretation at top-effect typing data. -/
theorem map_denote (X : Algebra.{u, max u v, x} (signature (τ := τ) Φ F))
    (f : Algebra.Hom (syntaxAlgebra Φ ε F) X)
    {n : Nat} {Γ : QCtx τ n} {t : Term Φ n} {A : τ}
    (d : HasType F Γ (⊤ : ε) t A) : f.map ⟨t, d⟩ = denote X d :=
  map_denote_aux X f ⊤ d rfl

theorem fold_unique (X : Algebra.{u, max u v, x} (signature (τ := τ) Φ F))
    (f : Algebra.Hom (syntaxAlgebra Φ ε F) X) :
    f = fold X := by
  apply Algebra.Hom.ext
  intro i a
  rcases i with ⟨n, Γ, A⟩
  rcases a with ⟨t, d⟩
  exact map_denote X f d

/-- The free quantitative constructor algebra is categorically initial. -/
def syntaxIsInitial (Φ : Type v) [HasTy Φ τ] (ε : Type w) [EffectSystem ε] [HasEff Φ ε]
    (F : Fragment) : CategoryTheory.Limits.IsInitial (syntaxAlgebra (τ := τ) Φ ε F) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom (fun X => fold X) (fun X f => fold_unique X f)

end Silmaril.Isotope.Refinement.Models

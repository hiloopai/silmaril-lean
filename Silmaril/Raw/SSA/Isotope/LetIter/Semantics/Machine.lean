module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Operational

/-!
# A continuation machine for let-iter

Each transition performs one syntax or continuation action. Saved environments
restore lexical scope after evaluating a subterm. Primitive instructions use
exactly the atomic relation of `Semantics.Eval`; no transition assumes a finite
subterm evaluation. Pair operands run left to right, and an iteration evaluates
its initializer once. Empty elimination evaluates its operand and then is stuck.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.Machine

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

/-- Evaluation frames capture precisely the data needed after a subterm returns. -/
inductive Kont (α : Type u) (ν : Type v) (Φ : Type w) where
  | halt
  | op (f : Φ) (next : Kont α ν Φ)
  | let₁ {n : Nat} (bound : BoundEnv α n) (body : Tm ν Φ (n + 1)) (next : Kont α ν Φ)
  | pairLeft {n : Nat} (bound : BoundEnv α n) (right : Tm ν Φ n) (next : Kont α ν Φ)
  | pairRight (left : Value α) (next : Kont α ν Φ)
  | let₂ {n : Nat} (bound : BoundEnv α n) (body : Tm ν Φ (n + 2)) (next : Kont α ν Φ)
  | inl (next : Kont α ν Φ)
  | inr (next : Kont α ν Φ)
  | case {n : Nat} (bound : BoundEnv α n) (left right : Tm ν Φ (n + 1)) (next : Kont α ν Φ)
  | abort (next : Kont α ν Φ)
  | iterInit {n : Nat} (bound : BoundEnv α n) (body : Tm ν Φ (n + 1)) (next : Kont α ν Φ)
  | iterBody {n : Nat} (bound : BoundEnv α n) (body : Tm ν Φ (n + 1)) (next : Kont α ν Φ)

/-- A machine is either evaluating, returning to a continuation, or entering a loop body. -/
inductive Config (α : Type u) (ν : Type v) (Φ : Type w) (σ : Type q) where
  | eval {n : Nat} (bound : BoundEnv α n) (term : Tm ν Φ n) (kont : Kont α ν Φ) (state : σ)
  | ret (value : Value α) (kont : Kont α ν Φ) (state : σ)
  | loop {n : Nat} (bound : BoundEnv α n) (body : Tm ν Φ (n + 1))
      (current : Value α) (kont : Kont α ν Φ) (state : σ)

/-- A single machine transition. Failed atomic instructions and malformed eliminations have no rule. -/
inductive Step (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    Config α ν Φ σ → Config α ν Φ σ → Prop where
  | fv {n} (bound : BoundEnv α n) (x : ν) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.fv x) k s) (.ret (free x) k s)
  | bv {n} (bound : BoundEnv α n) (i : Fin n) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.bv i) k s) (.ret (bound i) k s)
  | unit {n} (bound : BoundEnv α n) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound .unit k s) (.ret .unit k s)
  | op {n} (bound : BoundEnv α n) (f : Φ) (a : Tm ν Φ n) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.op f a) k s) (.eval bound a (.op f k) s)
  | apply {f : Φ} {a b : Value α} {s s' : σ} (k : Kont α ν Φ) (h : instr f a s b s') :
      Step instr free (.ret a (.op f k) s) (.ret b k s')
  | let₁ {n} (bound : BoundEnv α n) (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.let₁ a b) k s) (.eval bound a (.let₁ bound b k) s)
  | bind₁ {n} (bound : BoundEnv α n) (b : Tm ν Φ (n + 1)) (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret a (.let₁ bound b k) s) (.eval (extend bound a) b k s)
  | pair {n} (bound : BoundEnv α n) (a b : Tm ν Φ n) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.pair a b) k s) (.eval bound a (.pairLeft bound b k) s)
  | pairLeft {n} (bound : BoundEnv α n) (b : Tm ν Φ n) (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret a (.pairLeft bound b k) s) (.eval bound b (.pairRight a k) s)
  | pairRight (a b : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret b (.pairRight a k) s) (.ret (.pair a b) k s)
  | let₂ {n} (bound : BoundEnv α n) (a : Tm ν Φ n) (b : Tm ν Φ (n + 2)) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.let₂ a b) k s) (.eval bound a (.let₂ bound b k) s)
  | bind₂ {n} (bound : BoundEnv α n) (b : Tm ν Φ (n + 2)) (a₁ a₂ : Value α)
      (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret (.pair a₁ a₂) (.let₂ bound b k) s)
        (.eval (extend (extend bound a₁) a₂) b k s)
  | inl {n} (bound : BoundEnv α n) (a : Tm ν Φ n) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.inl a) k s) (.eval bound a (.inl k) s)
  | injectLeft (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret a (.inl k) s) (.ret (.inl a) k s)
  | inr {n} (bound : BoundEnv α n) (a : Tm ν Φ n) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.inr a) k s) (.eval bound a (.inr k) s)
  | injectRight (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret a (.inr k) s) (.ret (.inr a) k s)
  | case {n} (bound : BoundEnv α n) (a : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.case a l r) k s) (.eval bound a (.case bound l r k) s)
  | caseLeft {n} (bound : BoundEnv α n) (l r : Tm ν Φ (n + 1)) (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret (.inl a) (.case bound l r k) s) (.eval (extend bound a) l k s)
  | caseRight {n} (bound : BoundEnv α n) (l r : Tm ν Φ (n + 1)) (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret (.inr a) (.case bound l r k) s) (.eval (extend bound a) r k s)
  | abort {n} (bound : BoundEnv α n) (a : Tm ν Φ n) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.abort a) k s) (.eval bound a (.abort k) s)
  | iter {n} (bound : BoundEnv α n) (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.eval bound (.iter a b) k s) (.eval bound a (.iterInit bound b k) s)
  | initialized {n} (bound : BoundEnv α n) (b : Tm ν Φ (n + 1)) (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret a (.iterInit bound b k) s) (.loop bound b a k s)
  | loop {n} (bound : BoundEnv α n) (b : Tm ν Φ (n + 1)) (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.loop bound b a k s) (.eval (extend bound a) b (.iterBody bound b k) s)
  | exit {n} (bound : BoundEnv α n) (b : Tm ν Φ (n + 1)) (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret (.inl a) (.iterBody bound b k) s) (.ret a k s)
  | continue {n} (bound : BoundEnv α n) (b : Tm ν Φ (n + 1)) (a : Value α) (k : Kont α ν Φ) (s : σ) :
      Step instr free (.ret (.inr a) (.iterBody bound b k) s) (.loop bound b a k s)

/-- A finite machine execution, including the empty execution. -/
inductive Steps (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    Config α ν Φ σ → Config α ν Φ σ → Prop where
  | refl (c) : Steps instr free c c
  | cons {a b c} : Step instr free a b → Steps instr free b c → Steps instr free a c

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

theorem Step.steps {a b : Config α ν Φ σ} (h : Step instr free a b) : Steps instr free a b :=
  .cons h (.refl _)

theorem Steps.trans {a b c : Config α ν Φ σ} (h : Steps instr free a b)
    (g : Steps instr free b c) : Steps instr free a c := by
  induction h with
  | refl => exact g
  | cons step tail ih => exact .cons step (ih g)

/-- Finite term evaluation can run under any surrounding continuation. -/
theorem eval_steps {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α} (h : Eval instr free bound t s value s') :
    ∀ k, Steps instr free (.eval bound t k s) (.ret value k s') := by
  induction h using Eval.rec
      (motive_2 := fun bound body current s value s' _ =>
        ∀ k, Steps instr free (.loop bound body current k s) (.ret value k s')) with
  | fv => intro k; exact (Step.fv ..).steps
  | bv => intro k; exact (Step.bv ..).steps
  | unit => intro k; exact (Step.unit ..).steps
  | op arg step ih =>
      intro k
      exact .cons (.op ..) ((ih _).trans (Step.apply k step).steps)
  | let₁ arg body ihArg ihBody =>
      intro k
      exact .cons (.let₁ ..) ((ihArg _).trans (.cons (.bind₁ ..) (ihBody k)))
  | pair left right ihLeft ihRight =>
      intro k
      exact .cons (.pair ..) ((ihLeft _).trans (.cons (.pairLeft ..)
        ((ihRight _).trans (Step.pairRight ..).steps)))
  | let₂ arg body ihArg ihBody =>
      intro k
      exact .cons (.let₂ ..) ((ihArg _).trans (.cons (.bind₂ ..) (ihBody k)))
  | inl arg ih =>
      intro k
      exact .cons (.inl ..) ((ih _).trans (Step.injectLeft ..).steps)
  | inr arg ih =>
      intro k
      exact .cons (.inr ..) ((ih _).trans (Step.injectRight ..).steps)
  | case_inl scrutinee branch ihScrutinee ihBranch =>
      intro k
      exact .cons (.case ..) ((ihScrutinee _).trans (.cons (.caseLeft ..) (ihBranch k)))
  | case_inr scrutinee branch ihScrutinee ihBranch =>
      intro k
      exact .cons (.case ..) ((ihScrutinee _).trans (.cons (.caseRight ..) (ihBranch k)))
  | iter init loop ihInit ihLoop =>
      intro k
      exact .cons (.iter ..) ((ihInit _).trans (.cons (.initialized ..) (ihLoop k)))
  | done step ih =>
      rename_i k
      exact .cons (.loop ..) ((ih _).trans (Step.exit ..).steps)
  | step head tail ihHead ihTail =>
      rename_i k
      exact .cons (.loop ..) ((ihHead _).trans (.cons (.continue ..) (ihTail k)))

/-- The corresponding execution after the initializer has already run. -/
theorem loop_steps {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {current value : Value α} {s s' : σ} (h : Loop instr free bound body current s value s')
    (k : Kont α ν Φ) :
    Steps instr free (.loop bound body current k s) (.ret value k s') := by
  induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | done step _ => exact .cons (.loop ..) ((eval_steps step _).trans (Step.exit ..).steps)
  | step head tail _ ih =>
      exact .cons (.loop ..) ((eval_steps head _).trans (.cons (.continue ..) ih))
  | _ => trivial

end Silmaril.Isotope.LetIter.Semantics.Machine

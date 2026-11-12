module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Structural

/-!
# State-threading operational semantics for let-iter

Evaluation orders subterms from left to right. An iteration evaluates its
initializer exactly once; its body returns `inl result` to exit or `inr state`
to continue. Primitive instructions are atomic transitions supplied by the
model. A missing primitive transition is stuckness, not evidence of divergence.

`Eval` and `Loop` describe finite evaluations, without a totality assumption.
Malformed eliminations have no rule: runtime values include no empty value.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

abbrev FreeEnv (ν : Type v) (α : Type u) := ν → Value α
abbrev BoundEnv (α : Type u) (n : Nat) := Fin n → Value α

/-- Extend an environment with its newest value at index zero. -/
def extend {n : Nat} (bound : BoundEnv α n) (value : Value α) : BoundEnv α (n + 1) :=
  Fin.cases value bound

@[simp] theorem extend_zero {n : Nat} (bound : BoundEnv α n) (value : Value α) :
    extend bound value 0 = value := rfl

@[simp] theorem extend_succ {n : Nat} (bound : BoundEnv α n) (value : Value α) (i : Fin n) :
    extend bound value i.succ = bound i := rfl

/-- Each primitive input and machine state has at most one output and final state. -/
def InstrDeterministic (instr : Φ → Value α → σ → Value α → σ → Prop) : Prop :=
  ∀ f a s b s' c s'', instr f a s b s' → instr f a s c s'' → b = c ∧ s' = s''

mutual

/-- Finite, left-to-right evaluation of a term. -/
inductive Eval (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    {n : Nat} → BoundEnv α n → Tm ν Φ n → σ → Value α → σ → Prop where
  | fv {n : Nat} {bound : BoundEnv α n} {x : ν} {s : σ} :
      Eval instr free bound (.fv x) s (free x) s
  | bv {n : Nat} {bound : BoundEnv α n} {i : Fin n} {s : σ} :
      Eval instr free bound (.bv i) s (bound i) s
  | op {n : Nat} {bound : BoundEnv α n} {f : Φ} {a : Tm ν Φ n}
      {s s₁ s₂ : σ} {va value : Value α}
      (arg : Eval instr free bound a s va s₁) (step : instr f va s₁ value s₂) :
      Eval instr free bound (.op f a) s value s₂
  | let₁ {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
      {s s₁ s₂ : σ} {va value : Value α}
      (arg : Eval instr free bound a s va s₁)
      (body : Eval instr free (extend bound va) b s₁ value s₂) :
      Eval instr free bound (.let₁ a b) s value s₂
  | unit {n : Nat} {bound : BoundEnv α n} {s : σ} :
      Eval instr free bound .unit s .unit s
  | pair {n : Nat} {bound : BoundEnv α n} {a b : Tm ν Φ n}
      {s s₁ s₂ : σ} {va vb : Value α}
      (left : Eval instr free bound a s va s₁) (right : Eval instr free bound b s₁ vb s₂) :
      Eval instr free bound (.pair a b) s (.pair va vb) s₂
  | let₂ {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)}
      {s s₁ s₂ : σ} {va vb value : Value α}
      (arg : Eval instr free bound a s (.pair va vb) s₁)
      (body : Eval instr free (extend (extend bound va) vb) b s₁ value s₂) :
      Eval instr free bound (.let₂ a b) s value s₂
  | inl {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {s s' : σ} {value : Value α}
      (arg : Eval instr free bound a s value s') :
      Eval instr free bound (.inl a) s (.inl value) s'
  | inr {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {s s' : σ} {value : Value α}
      (arg : Eval instr free bound a s value s') :
      Eval instr free bound (.inr a) s (.inr value) s'
  | case_inl {n : Nat} {bound : BoundEnv α n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
      {s s₁ s₂ : σ} {va value : Value α}
      (scrutinee : Eval instr free bound e s (.inl va) s₁)
      (branch : Eval instr free (extend bound va) l s₁ value s₂) :
      Eval instr free bound (.case e l r) s value s₂
  | case_inr {n : Nat} {bound : BoundEnv α n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
      {s s₁ s₂ : σ} {va value : Value α}
      (scrutinee : Eval instr free bound e s (.inr va) s₁)
      (branch : Eval instr free (extend bound va) r s₁ value s₂) :
      Eval instr free bound (.case e l r) s value s₂
  | iter {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
      {s s₁ s₂ : σ} {initial value : Value α}
      (init : Eval instr free bound a s initial s₁)
      (loop : Loop instr free bound b initial s₁ value s₂) :
      Eval instr free bound (.iter a b) s value s₂

/-- Finite iterations after the initializer has already produced its value. -/
inductive Loop (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    {n : Nat} → BoundEnv α n → Tm ν Φ (n + 1) → Value α → σ → Value α → σ → Prop where
  | done {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
      {current value : Value α} {s s' : σ}
      (step : Eval instr free (extend bound current) body s (.inl value) s') :
      Loop instr free bound body current s value s'
  | step {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
      {current next value : Value α} {s s₁ s₂ : σ}
      (head : Eval instr free (extend bound current) body s (.inr next) s₁)
      (tail : Loop instr free bound body next s₁ value s₂) :
      Loop instr free bound body current s value s₂

end

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

theorem Eval.deterministic (hd : InstrDeterministic instr) {n : Nat}
    {bound : BoundEnv α n} {t : Tm ν Φ n} {s s₁ : σ} {v₁ : Value α}
    (h : Eval instr free bound t s v₁ s₁) :
    ∀ {v₂ s₂}, Eval instr free bound t s v₂ s₂ → v₁ = v₂ ∧ s₁ = s₂ := by
  induction h using Eval.rec
      (motive_2 := fun bound body current s v₁ s₁ _ =>
        ∀ {v₂ s₂}, Loop instr free bound body current s v₂ s₂ → v₁ = v₂ ∧ s₁ = s₂) with
  | fv => intro _ _ h'; cases h'; exact ⟨rfl, rfl⟩
  | bv => intro _ _ h'; cases h'; exact ⟨rfl, rfl⟩
  | unit => intro _ _ h'; cases h'; exact ⟨rfl, rfl⟩
  | op arg step ih =>
      intro _ _ h'
      cases h' with
      | op arg' step' =>
          obtain ⟨rfl, rfl⟩ := ih arg'
          exact hd _ _ _ _ _ _ _ step step'
  | let₁ arg body ihArg ihBody =>
      intro _ _ h'
      cases h' with
      | let₁ arg' body' =>
          obtain ⟨rfl, rfl⟩ := ihArg arg'
          exact ihBody body'
  | pair left right ihLeft ihRight =>
      intro _ _ h'
      cases h' with
      | pair left' right' =>
          obtain ⟨rfl, rfl⟩ := ihLeft left'
          obtain ⟨rfl, rfl⟩ := ihRight right'
          exact ⟨rfl, rfl⟩
  | let₂ arg body ihArg ihBody =>
      intro _ _ h'
      cases h' with
      | let₂ arg' body' =>
          obtain ⟨hv, rfl⟩ := ihArg arg'
          obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
          exact ihBody body'
  | inl arg ih =>
      intro _ _ h'
      cases h' with
      | inl arg' =>
          obtain ⟨rfl, rfl⟩ := ih arg'
          exact ⟨rfl, rfl⟩
  | inr arg ih =>
      intro _ _ h'
      cases h' with
      | inr arg' =>
          obtain ⟨rfl, rfl⟩ := ih arg'
          exact ⟨rfl, rfl⟩
  | case_inl scrutinee branch ihScrutinee ihBranch =>
      intro _ _ h'
      cases h' with
      | case_inl scrutinee' branch' =>
          obtain ⟨hv, rfl⟩ := ihScrutinee scrutinee'
          cases Value.inl.inj hv
          exact ihBranch branch'
      | case_inr scrutinee' _ =>
          obtain ⟨hv, _⟩ := ihScrutinee scrutinee'
          cases hv
  | case_inr scrutinee branch ihScrutinee ihBranch =>
      intro _ _ h'
      cases h' with
      | case_inr scrutinee' branch' =>
          obtain ⟨hv, rfl⟩ := ihScrutinee scrutinee'
          cases Value.inr.inj hv
          exact ihBranch branch'
      | case_inl scrutinee' _ =>
          obtain ⟨hv, _⟩ := ihScrutinee scrutinee'
          cases hv
  | iter init loop ihInit ihLoop =>
      intro _ _ h'
      cases h' with
      | iter init' loop' =>
          obtain ⟨rfl, rfl⟩ := ihInit init'
          exact ihLoop loop'
  | done step ih =>
      rename_i v₂ s₂ h'
      cases h' with
      | done step' =>
          obtain ⟨hv, hs⟩ := ih step'
          exact ⟨Value.inl.inj hv, hs⟩
      | step head _ =>
          obtain ⟨hv, _⟩ := ih head
          cases hv
  | step head tail ihHead ihTail =>
      rename_i v₂ s₂ h'
      cases h' with
      | done step' =>
          obtain ⟨hv, _⟩ := ihHead step'
          cases hv
      | step head' tail' =>
          obtain ⟨hv, rfl⟩ := ihHead head'
          cases Value.inr.inj hv
          exact ihTail tail'

theorem Loop.deterministic (hd : InstrDeterministic instr) {n : Nat}
    {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)} {current v₁ : Value α} {s s₁ : σ}
    (h : Loop instr free bound body current s v₁ s₁) :
    ∀ {v₂ s₂}, Loop instr free bound body current s v₂ s₂ → v₁ = v₂ ∧ s₁ = s₂ := by
  induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | done step _ =>
      intro _ _ h'
      cases h' with
      | done step' =>
          obtain ⟨hv, hs⟩ := Eval.deterministic hd step step'
          exact ⟨Value.inl.inj hv, hs⟩
      | step head _ =>
          obtain ⟨hv, _⟩ := Eval.deterministic hd step head
          cases hv
  | step head tail _ ih =>
      intro _ _ h'
      cases h' with
      | done step' =>
          obtain ⟨hv, _⟩ := Eval.deterministic hd head step'
          cases hv
      | step head' tail' =>
          obtain ⟨hv, rfl⟩ := Eval.deterministic hd head head'
          cases Value.inr.inj hv
          exact ih tail'
  | _ => trivial

/-- Existence of a finite result; stuck and diverging computations both fail this predicate. -/
def Terminates {n : Nat} (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) (bound : BoundEnv α n) (t : Tm ν Φ n) (s : σ) : Prop :=
  ∃ value s', Eval instr free bound t s value s'

/-- Absence of a finite result does not by itself assert an infinite computation. -/
def NoResult {n : Nat} (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) (bound : BoundEnv α n) (t : Tm ν Φ n) (s : σ) : Prop :=
  ¬ Terminates instr free bound t s

@[simp] theorem Eval.not_abort {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n}
    {s s' : σ} {value : Value α} : ¬ Eval instr free bound (.abort a) s value s' := by
  intro h
  cases h

section Examples

variable {n : Nat} (bound : BoundEnv α n) (s : σ)

/-- A body that immediately returns its input exits without changing machine state. -/
theorem Loop.exit_immediately (value : Value α) :
    Loop instr free bound (.inl (.bv 0)) value s value s := .done (.inl .bv)

/-- Initializer effects occur before the loop and are not evaluated again at exit. -/
theorem Eval.iter_exit {a : Tm ν Φ n} {value : Value α} {s' : σ}
    (init : Eval instr free bound a s value s') :
    Eval instr free bound (.iter a (.inl (.bv 0))) s value s' :=
  .iter init (Loop.exit_immediately bound s' value)

/-- Two atomic body evaluations: one continuation followed by an exit. -/
theorem Loop.step_then_exit (f : Φ) (current next value : Value α) (s₁ s₂ : σ)
    (head : instr f current s (.inr next) s₁) (tail : instr f next s₁ (.inl value) s₂) :
    Loop instr free bound (.op f (.bv 0)) current s value s₂ :=
  .step (.op .bv head) (.done (.op .bv tail))

end Examples

/-- Suspended term evaluation or an iteration whose initializer has already run. -/
inductive Config (α : Type u) (ν : Type v) (Φ : Type w) (σ : Type q) where
  | term {n : Nat} (bound : BoundEnv α n) (t : Tm ν Φ n) (state : σ)
  | loop {n : Nat} (bound : BoundEnv α n) (body : Tm ν Φ (n + 1))
      (current : Value α) (state : σ)

/-- One observable unfolding of divergence. Finite prefixes use `Eval`, and
the remaining infinite computation is represented by `continues`.
There is no rule that turns a stuck primitive or a malformed value into divergence. -/
inductive DivergenceStep (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) (continues : Config α ν Φ σ → Prop) : Config α ν Φ σ → Prop where
  | op {n : Nat} {bound : BoundEnv α n} {f : Φ} {a : Tm ν Φ n} {s : σ}
      (arg : continues (.term bound a s)) :
      DivergenceStep instr free continues (.term bound (.op f a) s)
  | let₁_arg {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {s : σ}
      (arg : continues (.term bound a s)) :
      DivergenceStep instr free continues (.term bound (.let₁ a b) s)
  | let₁_body {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
      {s s' : σ} {value : Value α} (arg : Eval instr free bound a s value s')
      (body : continues (.term (extend bound value) b s')) :
      DivergenceStep instr free continues (.term bound (.let₁ a b) s)
  | pair_left {n : Nat} {bound : BoundEnv α n} {a b : Tm ν Φ n} {s : σ}
      (left : continues (.term bound a s)) :
      DivergenceStep instr free continues (.term bound (.pair a b) s)
  | pair_right {n : Nat} {bound : BoundEnv α n} {a b : Tm ν Φ n} {s s' : σ} {value : Value α}
      (left : Eval instr free bound a s value s') (right : continues (.term bound b s')) :
      DivergenceStep instr free continues (.term bound (.pair a b) s)
  | let₂_arg {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} {s : σ}
      (arg : continues (.term bound a s)) :
      DivergenceStep instr free continues (.term bound (.let₂ a b) s)
  | let₂_body {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)}
      {s s' : σ} {va vb : Value α} (arg : Eval instr free bound a s (.pair va vb) s')
      (body : continues (.term (extend (extend bound va) vb) b s')) :
      DivergenceStep instr free continues (.term bound (.let₂ a b) s)
  | inl {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {s : σ}
      (arg : continues (.term bound a s)) :
      DivergenceStep instr free continues (.term bound (.inl a) s)
  | inr {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {s : σ}
      (arg : continues (.term bound a s)) :
      DivergenceStep instr free continues (.term bound (.inr a) s)
  | case_scrutinee {n : Nat} {bound : BoundEnv α n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
      {s : σ} (scrutinee : continues (.term bound e s)) :
      DivergenceStep instr free continues (.term bound (.case e l r) s)
  | case_inl {n : Nat} {bound : BoundEnv α n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
      {s s' : σ} {value : Value α} (scrutinee : Eval instr free bound e s (.inl value) s')
      (branch : continues (.term (extend bound value) l s')) :
      DivergenceStep instr free continues (.term bound (.case e l r) s)
  | case_inr {n : Nat} {bound : BoundEnv α n} {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
      {s s' : σ} {value : Value α} (scrutinee : Eval instr free bound e s (.inr value) s')
      (branch : continues (.term (extend bound value) r s')) :
      DivergenceStep instr free continues (.term bound (.case e l r) s)
  | abort {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {s : σ}
      (arg : continues (.term bound a s)) :
      DivergenceStep instr free continues (.term bound (.abort a) s)
  | iter_init {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {s : σ}
      (init : continues (.term bound a s)) :
      DivergenceStep instr free continues (.term bound (.iter a b) s)
  | iter_loop {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
      {s s' : σ} {value : Value α} (init : Eval instr free bound a s value s')
      (loop : continues (.loop bound b value s')) :
      DivergenceStep instr free continues (.term bound (.iter a b) s)
  | loop_body {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
      {current : Value α} {s : σ} (step : continues (.term (extend bound current) body s)) :
      DivergenceStep instr free continues (.loop bound body current s)
  | loop_step {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
      {current next : Value α} {s s' : σ}
      (head : Eval instr free (extend bound current) body s (.inr next) s')
      (tail : continues (.loop bound body next s')) :
      DivergenceStep instr free continues (.loop bound body current s)

theorem DivergenceStep.mono {R S : Config α ν Φ σ → Prop} {c : Config α ν Φ σ}
    (h : DivergenceStep instr free R c) (hRS : ∀ c, R c → S c) :
    DivergenceStep instr free S c := by
  cases h with
  | op arg => exact .op (hRS _ arg)
  | let₁_arg arg => exact .let₁_arg (hRS _ arg)
  | let₁_body arg body => exact .let₁_body arg (hRS _ body)
  | pair_left left => exact .pair_left (hRS _ left)
  | pair_right left right => exact .pair_right left (hRS _ right)
  | let₂_arg arg => exact .let₂_arg (hRS _ arg)
  | let₂_body arg body => exact .let₂_body arg (hRS _ body)
  | inl arg => exact .inl (hRS _ arg)
  | inr arg => exact .inr (hRS _ arg)
  | case_scrutinee scrutinee => exact .case_scrutinee (hRS _ scrutinee)
  | case_inl scrutinee branch => exact .case_inl scrutinee (hRS _ branch)
  | case_inr scrutinee branch => exact .case_inr scrutinee (hRS _ branch)
  | abort arg => exact .abort (hRS _ arg)
  | iter_init init => exact .iter_init (hRS _ init)
  | iter_loop init loop => exact .iter_loop init (hRS _ loop)
  | loop_body step => exact .loop_body (hRS _ step)
  | loop_step head tail => exact .loop_step head (hRS _ tail)

/-- Greatest-fixed-point divergence: a witness relation supports another
divergence unfolding at every one of its configurations. -/
def Diverges (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α)
    (c : Config α ν Φ σ) : Prop :=
  ∃ R : Config α ν Φ σ → Prop, R c ∧ ∀ c, R c → DivergenceStep instr free R c

namespace Diverges

theorem coinduct (R : Config α ν Φ σ → Prop)
    (closed : ∀ c, R c → DivergenceStep instr free R c) {c : Config α ν Φ σ}
    (hc : R c) : Diverges instr free c := ⟨R, hc, closed⟩

theorem unfold {c : Config α ν Φ σ} (h : Diverges instr free c) :
    DivergenceStep instr free (Diverges instr free) c := by
  obtain ⟨R, hc, closed⟩ := h
  exact (closed c hc).mono (fun _ hr => ⟨R, hr, closed⟩)

theorem fold {c : Config α ν Φ σ}
    (h : DivergenceStep instr free (Diverges instr free) c) : Diverges instr free c := by
  refine ⟨fun c' => c' = c ∨ Diverges instr free c', Or.inl rfl, ?_⟩
  intro c' hc'
  rcases hc' with rfl | hd
  · exact h.mono (fun _ hd => Or.inr hd)
  · exact hd.unfold.mono (fun _ hd => Or.inr hd)

theorem iff_step {c : Config α ν Φ σ} :
    Diverges instr free c ↔ DivergenceStep instr free (Diverges instr free) c := ⟨unfold, fold⟩

end Diverges

/-- A deterministic finite evaluation cannot also support an infinite computation. -/
theorem Eval.not_diverges (hd : InstrDeterministic instr) {n : Nat}
    {bound : BoundEnv α n} {t : Tm ν Φ n} {s s' : σ} {value : Value α}
    (h : Eval instr free bound t s value s') :
    ¬ Diverges instr free (.term bound t s) := by
  induction h using Eval.rec
      (motive_2 := fun bound body current s _ _ _ =>
        ¬ Diverges instr free (.loop bound body current s)) with
  | fv | bv | unit => intro hdiv; cases hdiv.unfold
  | op arg step ih =>
      intro hdiv
      cases hdiv.unfold with
      | op darg => exact ih darg
  | let₁ arg body ihArg ihBody =>
      intro hdiv
      cases hdiv.unfold with
      | let₁_arg darg => exact ihArg darg
      | let₁_body arg' dbody =>
          obtain ⟨rfl, rfl⟩ := arg.deterministic hd arg'
          exact ihBody dbody
  | pair left right ihLeft ihRight =>
      intro hdiv
      cases hdiv.unfold with
      | pair_left dleft => exact ihLeft dleft
      | pair_right left' dright =>
          obtain ⟨rfl, rfl⟩ := left.deterministic hd left'
          exact ihRight dright
  | let₂ arg body ihArg ihBody =>
      intro hdiv
      cases hdiv.unfold with
      | let₂_arg darg => exact ihArg darg
      | let₂_body arg' dbody =>
          obtain ⟨hv, rfl⟩ := arg.deterministic hd arg'
          obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
          exact ihBody dbody
  | inl arg ih =>
      intro hdiv
      cases hdiv.unfold with
      | inl darg => exact ih darg
  | inr arg ih =>
      intro hdiv
      cases hdiv.unfold with
      | inr darg => exact ih darg
  | case_inl scrutinee branch ihScrutinee ihBranch =>
      intro hdiv
      cases hdiv.unfold with
      | case_scrutinee dscrutinee => exact ihScrutinee dscrutinee
      | case_inl scrutinee' dbranch =>
          obtain ⟨hv, rfl⟩ := scrutinee.deterministic hd scrutinee'
          cases Value.inl.inj hv
          exact ihBranch dbranch
      | case_inr scrutinee' _ =>
          obtain ⟨hv, _⟩ := scrutinee.deterministic hd scrutinee'
          cases hv
  | case_inr scrutinee branch ihScrutinee ihBranch =>
      intro hdiv
      cases hdiv.unfold with
      | case_scrutinee dscrutinee => exact ihScrutinee dscrutinee
      | case_inr scrutinee' dbranch =>
          obtain ⟨hv, rfl⟩ := scrutinee.deterministic hd scrutinee'
          cases Value.inr.inj hv
          exact ihBranch dbranch
      | case_inl scrutinee' _ =>
          obtain ⟨hv, _⟩ := scrutinee.deterministic hd scrutinee'
          cases hv
  | iter init loop ihInit ihLoop =>
      intro hdiv
      cases hdiv.unfold with
      | iter_init dinit => exact ihInit dinit
      | iter_loop init' dloop =>
          obtain ⟨rfl, rfl⟩ := init.deterministic hd init'
          exact ihLoop dloop
  | done step ih =>
      intro hdiv
      cases hdiv.unfold with
      | loop_body dstep => exact ih dstep
      | loop_step head _ =>
          obtain ⟨hv, _⟩ := step.deterministic hd head
          cases hv
  | step head tail ihHead ihTail =>
      intro hdiv
      cases hdiv.unfold with
      | loop_body dhead => exact ihHead dhead
      | loop_step head' dtail =>
          obtain ⟨hv, rfl⟩ := head.deterministic hd head'
          cases Value.inr.inj hv
          exact ihTail dtail

theorem Loop.not_diverges (hd : InstrDeterministic instr) {n : Nat}
    {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)} {current value : Value α} {s s' : σ}
    (h : Loop instr free bound body current s value s') :
    ¬ Diverges instr free (.loop bound body current s) := by
  induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | done step _ =>
      intro hdiv
      cases hdiv.unfold with
      | loop_body dstep => exact step.not_diverges hd dstep
      | loop_step head _ =>
          obtain ⟨hv, _⟩ := step.deterministic hd head
          cases hv
  | step head tail _ ih =>
      intro hdiv
      cases hdiv.unfold with
      | loop_body dhead => exact head.not_diverges hd dhead
      | loop_step head' dtail =>
          obtain ⟨hv, rfl⟩ := head.deterministic hd head'
          cases Value.inr.inj hv
          exact ih dtail
  | _ => trivial

theorem Diverges.noResult (hd : InstrDeterministic instr) {n : Nat}
    {bound : BoundEnv α n} {t : Tm ν Φ n} {s : σ}
    (h : Diverges instr free (.term bound t s)) : NoResult instr free bound t s := by
  rintro ⟨value, s', he⟩
  exact he.not_diverges hd h

section DivergenceExamples

variable {n : Nat} (bound : BoundEnv α n) (s : σ)

/-- Returning `inr` of the current value forever is a genuine infinite loop. -/
theorem Loop.diverges_continue (current : Value α) :
    Diverges instr free (.loop bound (.inr (.bv 0)) current s) := by
  apply Diverges.coinduct (fun c => c = .loop bound (.inr (.bv 0)) current s) ?_ rfl
  intro c hc
  subst c
  exact .loop_step (.inr .bv) rfl

theorem Eval.iter_continue_diverges {a : Tm ν Φ n} {current : Value α} {s' : σ}
    (init : Eval instr free bound a s current s') :
    Diverges instr free (.term bound (.iter a (.inr (.bv 0))) s) :=
  Diverges.fold (.iter_loop init (Loop.diverges_continue bound s' current))

/-- A malformed elimination can have no result without supporting divergence. -/
theorem abort_unit_stuck :
    NoResult instr free bound (.abort .unit) s ∧
      ¬ Diverges instr free (.term bound (.abort .unit) s) := by
  constructor
  · rintro ⟨value, s', h⟩
    cases h
  · intro hdiv
    cases hdiv.unfold with
    | abort hunit => cases hunit.unfold

end DivergenceExamples

/-- Matching environments continue to match under one common newest binder. -/
theorem extend_rename {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} (agree : ∀ i, target (ρ i) = bound i) (value : Value α) :
    ∀ i, extend target value (Tm.up ρ i) = extend bound value i :=
  Fin.cases rfl (fun i => agree i)

/-- Bound renaming preserves both the result and the threaded machine state
when the target environment supplies the same value at every renamed index. -/
theorem Eval.rename {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α} (h : Eval instr free bound t s value s') :
    ∀ {m : Nat} (ρ : Fin n → Fin m) (target : BoundEnv α m),
      (∀ i, target (ρ i) = bound i) → Eval instr free target (t.rename ρ) s value s' := by
  induction h using Eval.rec
      (motive_2 := fun {n} bound body current s value s' _ =>
        ∀ {m : Nat} (ρ : Fin n → Fin m) (target : BoundEnv α m),
          (∀ i, target (ρ i) = bound i) →
          Loop instr free target (body.rename (Tm.up ρ)) current s value s') with
  | fv => intro _ _ _ _; exact .fv
  | bv => intro _ _ _ agree; exact agree _ ▸ .bv
  | unit => intro _ _ _ _; exact .unit
  | op arg step ih =>
      intro _ ρ target agree
      exact .op (ih ρ target agree) step
  | let₁ arg body ihArg ihBody =>
      intro _ ρ target agree
      exact .let₁ (ihArg ρ target agree) (ihBody (Tm.up ρ) _ (extend_rename agree _))
  | pair left right ihLeft ihRight =>
      intro _ ρ target agree
      exact .pair (ihLeft ρ target agree) (ihRight ρ target agree)
  | let₂ arg body ihArg ihBody =>
      intro _ ρ target agree
      exact .let₂ (ihArg ρ target agree)
        (ihBody (Tm.up (Tm.up ρ)) _ (extend_rename (extend_rename agree _) _))
  | inl arg ih =>
      intro _ ρ target agree
      exact .inl (ih ρ target agree)
  | inr arg ih =>
      intro _ ρ target agree
      exact .inr (ih ρ target agree)
  | case_inl scrutinee branch ihScrutinee ihBranch =>
      intro _ ρ target agree
      exact .case_inl (ihScrutinee ρ target agree)
        (ihBranch (Tm.up ρ) _ (extend_rename agree _))
  | case_inr scrutinee branch ihScrutinee ihBranch =>
      intro _ ρ target agree
      exact .case_inr (ihScrutinee ρ target agree)
        (ihBranch (Tm.up ρ) _ (extend_rename agree _))
  | iter init loop ihInit ihLoop =>
      intro _ ρ target agree
      exact .iter (ihInit ρ target agree) (ihLoop ρ target agree)
  | done step ih =>
      rename_i m ρ target agree
      exact .done (ih (Tm.up ρ) _ (extend_rename agree _))
  | step head tail ihHead ihTail =>
      rename_i m ρ target agree
      exact .step (ihHead (Tm.up ρ) _ (extend_rename agree _)) (ihTail ρ target agree)

theorem Loop.rename {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {current value : Value α} {s s' : σ} (h : Loop instr free bound body current s value s') :
    ∀ {m : Nat} (ρ : Fin n → Fin m) (target : BoundEnv α m),
      (∀ i, target (ρ i) = bound i) →
      Loop instr free target (body.rename (Tm.up ρ)) current s value s' := by
  induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | done step _ =>
      intro _ ρ target agree
      exact .done (step.rename (Tm.up ρ) _ (extend_rename agree _))
  | step head tail _ ih =>
      intro _ ρ target agree
      exact .step (head.rename (Tm.up ρ) _ (extend_rename agree _)) (ih ρ target agree)
  | _ => trivial

/-- Runtime product elimination agrees with the type-level binder ordering. -/
example {n : Nat} (bound : BoundEnv α n) (left right : Value α) (s : σ) :
    Eval instr free (extend bound (.pair left right))
      (.let₂ (.bv 0) (.pair (.bv 0) (.bv 1))) s (.pair right left) s :=
  .let₂ .bv (.pair .bv .bv)

end Silmaril.Isotope.LetIter.Semantics

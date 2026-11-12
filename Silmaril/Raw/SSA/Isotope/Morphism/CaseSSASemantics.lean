module

public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSA
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Operational
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-!
# Operational agreement of scoped let-case and SSA expressions

Both presentations use the same atomic instruction relation and thread the same
state. The ambient scope can be nonempty; positions outside it are irrelevant.
This compares finite expression evaluation, without a typing or determinism
assumption.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.CaseSSA

open LetCase.LocallyNameless

variable {α : Type u} {Φ : Type v} {σ : Type w} {n : Nat}

/-- A positional environment agrees with a finite environment at in-scope slots. -/
def EnvAgrees (env : LambdaSSA.Semantics.Env α)
    (bound : LetIter.Semantics.BoundEnv α n) : Prop :=
  ∀ i, env i.val = bound i

theorem EnvAgrees.extend {env : LambdaSSA.Semantics.Env α}
    {bound : LetIter.Semantics.BoundEnv α n} (h : EnvAgrees env bound)
    (value : Value α) :
    EnvAgrees (LambdaSSA.Semantics.extend env value)
      (LetIter.Semantics.extend bound value) :=
  Fin.cases rfl (fun i => h i)

variable {instr : Φ → Value α → σ → Value α → σ → Prop}
    {free : LetIter.Semantics.FreeEnv Empty α}

/-- Erasure preserves and reflects the returned value and final state. -/
theorem erase_eval_iff {t : Tm Empty Φ n}
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s s' : σ} {value : Value α} (agree : EnvAgrees env bound) :
    LambdaSSA.Semantics.Tm.Eval instr env (erase t) s value s' ↔
      LetIter.Semantics.Eval instr free bound (CaseIter.embed t) s value s' := by
  induction t generalizing env s s' value with
  | fv x => exact x.elim
  | bv i =>
      constructor
      · intro h
        cases h
        exact agree i ▸ .bv
      · intro h
        cases h
        exact agree i ▸ LambdaSSA.Semantics.Tm.Eval.var
  | op f a ih =>
      constructor
      · intro h
        cases h with | op arg step => exact .op ((ih agree).mp arg) step
      · intro h
        cases h with | op arg step => exact .op ((ih agree).mpr arg) step
  | let₁ a b iha ihb =>
      constructor
      · intro h
        cases h with
        | let₁ arg body => exact .let₁ ((iha agree).mp arg) ((ihb (agree.extend _)).mp body)
      · intro h
        cases h with
        | let₁ arg body => exact .let₁ ((iha agree).mpr arg) ((ihb (agree.extend _)).mpr body)
  | unit =>
      constructor
      · intro h; cases h; exact .unit
      · intro h; cases h; exact .unit
  | pair a b iha ihb =>
      constructor
      · intro h
        cases h with | pair left right => exact .pair ((iha agree).mp left) ((ihb agree).mp right)
      · intro h
        cases h with | pair left right => exact .pair ((iha agree).mpr left) ((ihb agree).mpr right)
  | let₂ a b iha ihb =>
      constructor
      · intro h
        cases h with
        | let₂ arg body =>
            exact .let₂ ((iha agree).mp arg) ((ihb ((agree.extend _).extend _)).mp body)
      · intro h
        cases h with
        | let₂ arg body =>
            exact .let₂ ((iha agree).mpr arg) ((ihb ((agree.extend _).extend _)).mpr body)
  | inl a ih =>
      constructor
      · intro h; cases h with | inl arg => exact .inl ((ih agree).mp arg)
      · intro h; cases h with | inl arg => exact .inl ((ih agree).mpr arg)
  | inr a ih =>
      constructor
      · intro h; cases h with | inr arg => exact .inr ((ih agree).mp arg)
      · intro h; cases h with | inr arg => exact .inr ((ih agree).mpr arg)
  | case a l r iha ihl ihr =>
      constructor
      · intro h
        cases h with
        | case_inl arg branch =>
            exact .case_inl ((iha agree).mp arg) ((ihl (agree.extend _)).mp branch)
        | case_inr arg branch =>
            exact .case_inr ((iha agree).mp arg) ((ihr (agree.extend _)).mp branch)
      · intro h
        cases h with
        | case_inl arg branch =>
            exact .case_inl ((iha agree).mpr arg) ((ihl (agree.extend _)).mpr branch)
        | case_inr arg branch =>
            exact .case_inr ((iha agree).mpr arg) ((ihr (agree.extend _)).mpr branch)
  | abort a _ =>
      constructor
      · intro h; cases h
      · intro h; cases h

theorem erase_eval {t : Tm Empty Φ n}
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s s' : σ} {value : Value α} (agree : EnvAgrees env bound)
    (h : LetIter.Semantics.Eval instr free bound (CaseIter.embed t) s value s') :
    LambdaSSA.Semantics.Tm.Eval instr env (erase t) s value s' :=
  (erase_eval_iff agree).mpr h

theorem eval_of_erase {t : Tm Empty Φ n}
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s s' : σ} {value : Value α} (agree : EnvAgrees env bound)
    (h : LambdaSSA.Semantics.Tm.Eval instr env (erase t) s value s') :
    LetIter.Semantics.Eval instr free bound (CaseIter.embed t) s value s' :=
  (erase_eval_iff agree).mp h

/-- A positional environment can always be restricted to the finite source scope. -/
theorem erase_eval_restrict_iff {t : Tm Empty Φ n}
    {env : LambdaSSA.Semantics.Env α} {s s' : σ} {value : Value α} :
    LambdaSSA.Semantics.Tm.Eval instr env (erase t) s value s' ↔
      LetIter.Semantics.Eval instr free (fun i => env i.val)
        (CaseIter.embed t) s value s' :=
  erase_eval_iff (fun _ => rfl)

/-- Decoding a scoped SSA expression preserves and reflects its operational behavior. -/
theorem ofScoped_eval_iff {t : LambdaSSA.Tm Φ} (scope : t.Scoped n)
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s s' : σ} {value : Value α} (agree : EnvAgrees env bound) :
    LetIter.Semantics.Eval instr free bound (CaseIter.embed (ofScoped t scope))
      s value s' ↔ LambdaSSA.Semantics.Tm.Eval instr env t s value s' := by
  rw [← erase_eval_iff agree, erase_ofScoped]

/-- Finite termination agrees even when the instruction relation is nondeterministic. -/
theorem erase_terminates_iff {t : Tm Empty Φ n}
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s : σ} (agree : EnvAgrees env bound) :
    (∃ value s', LambdaSSA.Semantics.Tm.Eval instr env (erase t) s value s') ↔
      LetIter.Semantics.Terminates instr free bound (CaseIter.embed t) s := by
  constructor
  · rintro ⟨value, s', h⟩
    exact ⟨value, s', eval_of_erase agree h⟩
  · rintro ⟨value, s', h⟩
    exact ⟨value, s', erase_eval agree h⟩

/-- The two product binders keep their order across a nonempty ambient scope. -/
example (env : LambdaSSA.Semantics.Env α) (left right : Value α) (s : σ) :
    LambdaSSA.Semantics.Tm.Eval instr
      (LambdaSSA.Semantics.extend env (.pair left right))
      (erase (.let₂ (.bv 0) (.pair (.bv 0) (.bv 1)) : Tm Empty Φ 1))
      s (.pair right left) s :=
  erase_eval (free := Empty.elim)
    (bound := LetIter.Semantics.extend Fin.elim0 (.pair left right))
    (Fin.cases rfl (fun i => Fin.elim0 i)) (.let₂ .bv (.pair .bv .bv))

/-- A stateful selected branch transfers unchanged; an unselected stuck branch
does not need an evaluation. -/
example (env : LambdaSSA.Semantics.Env α) (f : Φ) (input output : Value α)
    (s s' : σ) (step : instr f input s output s') :
    LambdaSSA.Semantics.Tm.Eval instr (LambdaSSA.Semantics.extend env input)
      (erase (.case (.inl (.bv 0)) (.op f (.bv 0)) (.abort .unit) : Tm Empty Φ 1))
      s output s' :=
  erase_eval (free := Empty.elim)
    (bound := LetIter.Semantics.extend Fin.elim0 input)
    (Fin.cases rfl (fun i => Fin.elim0 i)) (.case_inl (.inl .bv) (.op .bv step))

end Silmaril.Isotope.Morphism.CaseSSA

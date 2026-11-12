module

public import Silmaril.Raw.SSA.Isotope.Morphism.IterSSA
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Operational
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-!
# Finite semantic preservation for CPS compilation

Source and target use the same atomic instruction relation. The theorem
composes a finite source evaluation with any finite target continuation run;
it imposes no determinism, totality, typing, or purity assumption.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.IterSSA

open LetIter.LocallyNameless (Tm)
open LetIter.Semantics (FreeEnv BoundEnv)
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q} {n : Nat}

namespace Vars

/-- The target environment agrees with both source variable spaces. -/
structure Relates (free : FreeEnv ν α) (bound : BoundEnv α n) (env : Env α)
    (vars : Vars ν n) : Prop where
  free : ∀ x, env (vars.free x) = free x
  bound : ∀ i, env (vars.bound i) = bound i

theorem Relates.shift {free : FreeEnv ν α} {bound : BoundEnv α n} {env : Env α}
    {vars : Vars ν n} (h : Relates free bound env vars) (value : Value α) :
    Relates free bound (extend env value) vars.shift where
  free x := h.free x
  bound i := h.bound i

theorem Relates.bind {free : FreeEnv ν α} {bound : BoundEnv α n} {env : Env α}
    {vars : Vars ν n} (h : Relates free bound env vars) (value : Value α) :
    Relates free (LetIter.Semantics.extend bound value) (extend env value) vars.bind where
  free x := h.free x
  bound := Fin.cases rfl (fun i => h.bound i)

end Vars

variable {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- A temporary inserted below the result is invisible to the continuation. -/
theorem eval_under {env : Env α} {value out : Value α} {k : Region Φ}
    {s s' : σ} {label : Nat}
    (hk : LambdaSSA.Semantics.Region.Eval instr (extend env value) k s label out s')
    (temp : Value α) :
    LambdaSSA.Semantics.Region.Eval instr (extend (extend env temp) value)
      (under k) s label out s' := by
  exact hk.renameVars (fun i => by cases i <;> rfl)

/-- General finite CPS correctness, including machine-state transitions and
arbitrary result continuations. This is a forward simulation theorem. -/
theorem compile_eval {free : FreeEnv ν α} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' s'' : σ} {value out : Value α} {label : Nat}
    (ht : LetIter.Semantics.Eval instr free bound t s value s')
    {env : Env α} {vars : Vars ν n} {k : Region Φ}
    (hvars : Vars.Relates free bound env vars)
    (hk : LambdaSSA.Semantics.Region.Eval instr (extend env value) k s' label out s'') :
    LambdaSSA.Semantics.Region.Eval instr env (compile t vars k) s label out s'' := by
  induction ht using LetIter.Semantics.Eval.rec
      (motive_2 := fun {n} bound body current s value s' _ =>
        ∀ {env : Env α} {vars : Vars ν n} {k : Region Φ} {label : Nat}
          {out : Value α} {s'' : σ}, Vars.Relates free bound env vars →
          LambdaSSA.Semantics.Region.Eval instr (extend env value) k s' label out s'' →
          LambdaSSA.Semantics.Region.Follow instr env
            (fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
              (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0))))
            0 current s label out s'') generalizing env k label out s'' with
  | fv =>
      apply LambdaSSA.Semantics.Region.Eval.let₁ ?_ hk
      simpa only [hvars.free] using
        (LambdaSSA.Semantics.Tm.Eval.var (instr := instr) (env := env)
          (i := vars.free _) (s := _))
  | bv =>
      apply LambdaSSA.Semantics.Region.Eval.let₁ ?_ hk
      simpa only [hvars.bound] using
        (LambdaSSA.Semantics.Tm.Eval.var (instr := instr) (env := env)
          (i := vars.bound _) (s := _))
  | unit => exact .let₁ .unit hk
  | op arg step ih => exact ih hvars (.let₁ (.op .var step) (eval_under hk _))
  | let₁ arg body ihArg ihBody =>
      exact ihArg hvars (ihBody (hvars.bind _) (eval_under hk _))
  | pair left right ihLeft ihRight =>
      exact ihLeft hvars (ihRight (hvars.shift _) (.let₁ (.pair .var .var)
        (eval_under (eval_under hk _) _)))
  | let₂ arg body ihArg ihBody =>
      exact ihArg hvars (.let₂ .var (ihBody (((hvars.shift _).bind _).bind _)
        (eval_under (eval_under (eval_under hk _) _) _)))
  | inl arg ih => exact ih hvars (.let₁ (.inl .var) (eval_under hk _))
  | inr arg ih => exact ih hvars (.let₁ (.inr .var) (eval_under hk _))
  | case_inl scrutinee branch ihScrutinee ihBranch =>
      exact ihScrutinee hvars (.case_inl .var
        (ihBranch ((hvars.shift _).bind _) (eval_under (eval_under hk _) _)))
  | case_inr scrutinee branch ihScrutinee ihBranch =>
      exact ihScrutinee hvars (.case_inr .var
        (ihBranch ((hvars.shift _).bind _) (eval_under (eval_under hk _) _)))
  | iter init loop ihInit ihLoop => exact .cfg (ihInit hvars (.br .var)) (ihLoop hvars hk)
  | done step ih =>
      rename_i env vars k label out s'' hvars hk
      apply LambdaSSA.Semantics.Region.Follow.step (by decide)
      · exact ih (hvars.bind _) (.case_inl .var
          (eval_under (eval_under (hk.renameLabels Nat.succ) _) _))
      · simpa only [Nat.add_sub_cancel] using
          (LambdaSSA.Semantics.Region.Follow.exit (instr := instr) (env := env)
            (blocks := fun (_ : Fin 1) => compile _ vars.bind (.case (.var 0)
              (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0))))
            (value := out) (s := s'') (Nat.le_add_left 1 label))
  | step head tail ihHead ihTail =>
      rename_i env vars k label out s'' hvars hk
      exact .step (by decide) (ihHead (hvars.bind _) (.case_inr .var (.br .var))) (ihTail hvars hk)

/-- Running the compiled term with a return continuation produces the same
value and final machine state at the selected exit. -/
theorem compile_return_eval {free : FreeEnv ν α} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α}
    (ht : LetIter.Semantics.Eval instr free bound t s value s')
    {env : Env α} {vars : Vars ν n} (hvars : Vars.Relates free bound env vars) (label : Nat) :
    LambdaSSA.Semantics.Region.Eval instr env (compile t vars (.br label (.var 0)))
      s label value s' := compile_eval ht hvars (.br .var)

end Silmaril.Isotope.Morphism.IterSSA

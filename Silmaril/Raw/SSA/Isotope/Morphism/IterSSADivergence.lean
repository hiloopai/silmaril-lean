module

public import Silmaril.Raw.SSA.Isotope.Morphism.IterSSASemantics
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.DivergenceStructural

/-!
# Divergence preservation for CPS compilation

Finite source prefixes retain their machine-state transitions before a
divergent continuation. Infinite source loops become infinite execution of the
compiled CFG or a divergent compiled body. Atomic instructions need not be
deterministic or total.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.IterSSA

open LetIter.LocallyNameless (Tm)
open LetIter.Semantics (FreeEnv BoundEnv)
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q} {n : Nat}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- An administrative variable beneath a result does not stop a divergent continuation. -/
theorem diverges_under {env : Env α} {value : Value α} {k : Region Φ} {s : σ}
    (hk : LambdaSSA.Semantics.Diverges instr (.region (extend env value) k s))
    (temp : Value α) :
    LambdaSSA.Semantics.Diverges instr
      (.region (extend (extend env temp) value) (under k) s) :=
  hk.renameVars (fun i => by cases i <;> rfl)

/-- A finite source evaluation followed by a divergent continuation compiles
to a divergent target region, with the source prefix's effects preserved. -/
theorem compile_eval_diverges {free : FreeEnv ν α} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α}
    (ht : LetIter.Semantics.Eval instr free bound t s value s')
    {env : Env α} {vars : Vars ν n} {k : Region Φ}
    (hvars : Vars.Relates free bound env vars)
    (hk : LambdaSSA.Semantics.Diverges instr (.region (extend env value) k s')) :
    LambdaSSA.Semantics.Diverges instr (.region env (compile t vars k) s) := by
  induction ht using LetIter.Semantics.Eval.rec
      (motive_2 := fun {n} bound body current s value s' _ =>
        ∀ {env : Env α} {vars : Vars ν n} {k : Region Φ},
          Vars.Relates free bound env vars →
          LambdaSSA.Semantics.Diverges instr (.region (extend env value) k s') →
          LambdaSSA.Semantics.Diverges instr (.follow env
            (fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
              (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0))))
            0 current s)) generalizing env k with
  | fv =>
      apply LambdaSSA.Semantics.Diverges.fold
      apply LambdaSSA.Semantics.DivergenceStep.let₁ ?_ hk
      simpa only [hvars.free] using
        (LambdaSSA.Semantics.Tm.Eval.var (instr := instr) (env := env)
          (i := vars.free _) (s := _))
  | bv =>
      apply LambdaSSA.Semantics.Diverges.fold
      apply LambdaSSA.Semantics.DivergenceStep.let₁ ?_ hk
      simpa only [hvars.bound] using
        (LambdaSSA.Semantics.Tm.Eval.var (instr := instr) (env := env)
          (i := vars.bound _) (s := _))
  | unit => exact .fold (.let₁ .unit hk)
  | op arg step ih => exact ih hvars (.fold (.let₁ (.op .var step) (diverges_under hk _)))
  | let₁ arg body ihArg ihBody =>
      exact ihArg hvars (ihBody (hvars.bind _) (diverges_under hk _))
  | pair left right ihLeft ihRight =>
      exact ihLeft hvars (ihRight (hvars.shift _) (.fold (.let₁ (.pair .var .var)
        (diverges_under (diverges_under hk _) _))))
  | let₂ arg body ihArg ihBody =>
      exact ihArg hvars (.fold (.let₂ .var (ihBody (((hvars.shift _).bind _).bind _)
        (diverges_under (diverges_under (diverges_under hk _) _) _))))
  | inl arg ih => exact ih hvars (.fold (.let₁ (.inl .var) (diverges_under hk _)))
  | inr arg ih => exact ih hvars (.fold (.let₁ (.inr .var) (diverges_under hk _)))
  | case_inl scrutinee branch ihScrutinee ihBranch =>
      exact ihScrutinee hvars (.fold (.case_inl .var
        (ihBranch ((hvars.shift _).bind _) (diverges_under (diverges_under hk _) _))))
  | case_inr scrutinee branch ihScrutinee ihBranch =>
      exact ihScrutinee hvars (.fold (.case_inr .var
        (ihBranch ((hvars.shift _).bind _) (diverges_under (diverges_under hk _) _))))
  | iter init loop _ ihLoop =>
      exact .fold (.cfg_follow (compile_return_eval init hvars 0) (ihLoop hvars hk))
  | done step ih =>
      rename_i env vars k hvars hk
      exact .fold (.follow_body (by decide) (ih (hvars.bind _) (.fold (.case_inl .var
        (diverges_under (diverges_under (hk.renameLabels Nat.succ) _) _)))))
  | step head tail _ ihTail =>
      rename_i env vars k hvars hk
      exact .fold (.follow_next (by decide)
        (compile_eval head (hvars.bind _) (.case_inr .var (.br .var))) (ihTail hvars hk))

/-- Compile a divergent loop given preservation of divergence for its body.
The coinduction reuses the environment captured at the CFG boundary. -/
theorem loop_compile_diverges {free : FreeEnv ν α} {bound : BoundEnv α n}
    {body : Tm ν Φ (n + 1)} {env : Env α} {vars : Vars ν n} {k : Region Φ}
    (hvars : Vars.Relates free bound env vars)
    (hbody : ∀ (current : Value α) (s : σ),
      LetIter.Semantics.Diverges instr free
        (.term (LetIter.Semantics.extend bound current) body s) →
      LambdaSSA.Semantics.Diverges instr (.region (extend env current)
        (compile body vars.bind (.case (.var 0)
          (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) s))
    {current : Value α} {s : σ}
    (hloop : LetIter.Semantics.Diverges instr free (.loop bound body current s)) :
    LambdaSSA.Semantics.Diverges instr (.follow env
      (fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
        (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) 0 current s) := by
  let blocks := fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
    (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))
  apply LambdaSSA.Semantics.Diverges.coinduct
    (fun c => (∃ current s, LetIter.Semantics.Diverges instr free
      (.loop bound body current s) ∧ c = .follow env blocks 0 current s) ∨
      LambdaSSA.Semantics.Diverges instr c) ?_ (Or.inl ⟨current, s, hloop, rfl⟩)
  intro c hc
  rcases hc with ⟨current, s, hloop, rfl⟩ | hd
  · cases hloop.unfold with
    | loop_body hd => exact .follow_body (by decide) (Or.inr (hbody current s hd))
    | loop_step head tail =>
        exact .follow_next (by decide)
          (compile_eval head (hvars.bind _) (.case_inr .var (.br .var)))
          (Or.inl ⟨_, _, tail, rfl⟩)
  · exact hd.unfold.mono (fun _ h => Or.inr h)

/-- Every divergent source term compiles to a divergent target region, for
any continuation and any environment agreeing on the source variables. -/
theorem compile_diverges {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {k : Region Φ} {s : σ}
    (hvars : Vars.Relates free bound env vars)
    (ht : LetIter.Semantics.Diverges instr free (.term bound t s)) :
    LambdaSSA.Semantics.Diverges instr (.region env (compile t vars k) s) := by
  induction t generalizing env k s with
  | fv | bv | unit => cases ht.unfold
  | op f a ih => cases ht.unfold with
    | op hd => exact ih hvars hd
  | let₁ a b iha ihb => cases ht.unfold with
    | let₁_arg hd => exact iha hvars hd
    | let₁_body ha hd => exact compile_eval_diverges ha hvars (ihb (hvars.bind _) hd)
  | pair a b iha ihb => cases ht.unfold with
    | pair_left hd => exact iha hvars hd
    | pair_right ha hd => exact compile_eval_diverges ha hvars (ihb (hvars.shift _) hd)
  | let₂ a b iha ihb => cases ht.unfold with
    | let₂_arg hd => exact iha hvars hd
    | let₂_body ha hd =>
        exact compile_eval_diverges ha hvars
          (.fold (.let₂ .var (ihb (((hvars.shift _).bind _).bind _) hd)))
  | inl a ih => cases ht.unfold with
    | inl hd => exact ih hvars hd
  | inr a ih => cases ht.unfold with
    | inr hd => exact ih hvars hd
  | case a l r iha ihl ihr => cases ht.unfold with
    | case_scrutinee hd => exact iha hvars hd
    | case_inl ha hd =>
        exact compile_eval_diverges ha hvars (.fold (.case_inl .var (ihl ((hvars.shift _).bind _) hd)))
    | case_inr ha hd =>
        exact compile_eval_diverges ha hvars (.fold (.case_inr .var (ihr ((hvars.shift _).bind _) hd)))
  | abort a ih => cases ht.unfold with
    | abort hd => exact ih hvars hd
  | iter init body ihInit ihBody => cases ht.unfold with
    | iter_init hd => exact .fold (.cfg_entry (ihInit hvars hd))
    | iter_loop hi hd =>
        exact .fold (.cfg_follow (compile_return_eval hi hvars 0)
          (loop_compile_diverges hvars (fun current _ h => ihBody (hvars.bind current) h) hd))

end Silmaril.Isotope.Morphism.IterSSA

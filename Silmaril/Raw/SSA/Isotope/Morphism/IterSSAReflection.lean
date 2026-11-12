module

public import Silmaril.Raw.SSA.Isotope.Morphism.IterSSADivergence
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.External
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Reflection

/-!
# Reflection of continuation-passing compilation

`IterSSA.compile` is proved elsewhere to preserve finite evaluation, faults and
divergence. This module proves the converse: every target execution of a
compiled region decomposes into a source execution followed by an execution of
the supplied continuation. Combined with the existing preservation theorems the
result is an exact correspondence, which is what the round-trip theorems need.

Nothing here assumes instruction determinism, totality, or typing. Both
calculi treat a missing instruction transition and a malformed elimination as
stuckness, so the stuck cases match on the nose.
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

/-- An administrative binder beneath the result is invisible to the
continuation, in both directions. -/
theorem eval_under_iff {env : Env α} {value temp out : Value α} {k : Region Φ}
    {s s' : σ} {label : Nat} :
    LambdaSSA.Semantics.Region.Eval instr (extend (extend env temp) value) (under k)
        s label out s' ↔
      LambdaSSA.Semantics.Region.Eval instr (extend env value) k s label out s' :=
  LambdaSSA.Semantics.Region.Eval.renameVars_iff (fun i => by cases i <;> rfl)

/-- Reading the newest variable yields its value and leaves the state alone. -/
theorem eval_var_zero {env : Env α} {value : Value α} {s s' : σ} {out : Value α}
    (h : LambdaSSA.Semantics.Tm.Eval instr (extend env value) (.var 0) s out s') :
    out = value ∧ s' = s := by cases h; exact ⟨rfl, rfl⟩

/-- Finite iterations of a compiled loop body come from source iterations. The
single compiled block exits internally to continue and externally to finish. -/
theorem compile_loop_rev {free : FreeEnv ν α} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {vars : Vars ν n} {k : Region Φ}
    (ihBody : ∀ {bound' : BoundEnv α (n + 1)} {env' : Env α} {vars' : Vars ν (n + 1)}
      {k' : Region Φ} {s₀ s₁ : σ} {ℓ : Nat} {o : Value α},
      Vars.Relates free bound' env' vars' →
      LambdaSSA.Semantics.Region.Eval instr env' (compile body vars' k') s₀ ℓ o s₁ →
      ∃ value s₂, LetIter.Semantics.Eval instr free bound' body s₀ value s₂ ∧
        LambdaSSA.Semantics.Region.Eval instr (extend env' value) k' s₂ ℓ o s₁)
    {count : Nat} {blocks : Fin count → Region Φ} {env : Env α}
    {first : Nat} {current : Value α} {s : σ} {label : Nat} {out : Value α} {s'' : σ}
    (h : LambdaSSA.Semantics.Region.Follow instr env blocks first current s label out s'') :
    Vars.Relates free bound env vars →
    (∀ i, blocks i = compile body vars.bind (.case (.var 0)
      (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) →
    count = 1 → first = 0 →
      ∃ w s', LetIter.Semantics.Loop instr free bound body current s w s' ∧
        LambdaSSA.Semantics.Region.Eval instr (extend env w) k s' label out s'' := by
  induction h using LambdaSSA.Semantics.Region.Follow.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside => intro _ _ hcount hfirst; omega
  | @step env' count' first' next o' blocks' current' middle value' s₀ s₁ s₂ inside head tail _ ih =>
      intro hvars hblocks hcount hfirst
      subst hfirst
      rw [hblocks] at head
      obtain ⟨w, sw, runBody, runCase⟩ := ihBody (hvars.bind current') head
      cases runCase with
      | case_inl arg branch =>
          obtain ⟨hw, hs⟩ := eval_var_zero arg
          subst hw
          obtain ⟨ℓ, hℓ, runK⟩ :=
            LambdaSSA.Semantics.Region.Eval.of_renameLabels
              (eval_under_iff.mp (eval_under_iff.mp branch))
          cases tail with
          | exit outside =>
              refine ⟨_, _, .done (hs ▸ runBody), ?_⟩
              have hlabel : next - count' = ℓ := by omega
              rw [hlabel]
              exact runK
          | step inside' _ _ => omega
      | case_inr arg branch =>
          obtain ⟨hw, hs⟩ := eval_var_zero arg
          subst hw
          cases branch with
          | br argBr =>
              obtain ⟨hmid, hs'⟩ := eval_var_zero argBr
              subst hmid
              obtain ⟨w', s', loop, runK⟩ := ih hvars hblocks hcount (by omega)
              exact ⟨w', s', .step (hs ▸ runBody) (hs' ▸ loop), runK⟩
  | _ => trivial

/-- Every finite execution of a compiled region decomposes into a source
evaluation and an execution of the continuation. -/
theorem compile_eval_rev {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {k : Region Φ} {s s'' : σ} {label : Nat} {out : Value α}
    (hvars : Vars.Relates free bound env vars)
    (h : LambdaSSA.Semantics.Region.Eval instr env (compile t vars k) s label out s'') :
    ∃ value s', LetIter.Semantics.Eval instr free bound t s value s' ∧
      LambdaSSA.Semantics.Region.Eval instr (extend env value) k s' label out s'' := by
  induction t generalizing env k s s'' label out with
  | fv x =>
      cases h with
      | let₁ arg rest =>
          cases arg
          exact ⟨free x, s, .fv, by simpa only [hvars.free] using rest⟩
  | bv i =>
      cases h with
      | let₁ arg rest =>
          cases arg
          exact ⟨bound i, s, .bv, by simpa only [hvars.bound] using rest⟩
  | unit => cases h with | let₁ arg rest => cases arg; exact ⟨.unit, s, .unit, rest⟩
  | op f a ih =>
      obtain ⟨va, s₁, runA, rest⟩ := ih hvars h
      cases rest with
      | let₁ arg body =>
          cases arg with
          | op argVar step =>
              obtain ⟨hv, rfl⟩ := eval_var_zero argVar
              subst hv
              exact ⟨_, _, .op runA step, eval_under_iff.mp body⟩
  | pair a b iha ihb =>
      obtain ⟨va, s₁, runA, rest⟩ := iha hvars h
      obtain ⟨vb, s₂, runB, rest'⟩ := ihb (hvars.shift va) rest
      cases rest' with
      | let₁ arg body =>
          cases arg with
          | pair left right =>
              cases left; cases right
              exact ⟨_, _, .pair runA runB, eval_under_iff.mp (eval_under_iff.mp body)⟩
  | let₁ a b iha ihb =>
      obtain ⟨va, s₁, runA, rest⟩ := iha hvars h
      obtain ⟨vb, s₂, runB, rest'⟩ := ihb (hvars.bind va) rest
      exact ⟨vb, s₂, .let₁ runA runB, eval_under_iff.mp rest'⟩
  | let₂ a b iha ihb =>
      obtain ⟨va, s₁, runA, rest⟩ := iha hvars h
      cases rest with
      | let₂ arg body =>
          obtain ⟨hv, rfl⟩ := eval_var_zero arg
          subst hv
          obtain ⟨vb, s₂, runB, rest'⟩ := ihb (((hvars.shift _).bind _).bind _) body
          exact ⟨vb, s₂, .let₂ runA runB,
            eval_under_iff.mp (eval_under_iff.mp (eval_under_iff.mp rest'))⟩
  | inl a ih =>
      obtain ⟨va, s₁, runA, rest⟩ := ih hvars h
      cases rest with
      | let₁ arg body =>
          cases arg with
          | inl argVar =>
              obtain ⟨hv, rfl⟩ := eval_var_zero argVar
              subst hv
              exact ⟨_, _, .inl runA, eval_under_iff.mp body⟩
  | inr a ih =>
      obtain ⟨va, s₁, runA, rest⟩ := ih hvars h
      cases rest with
      | let₁ arg body =>
          cases arg with
          | inr argVar =>
              obtain ⟨hv, rfl⟩ := eval_var_zero argVar
              subst hv
              exact ⟨_, _, .inr runA, eval_under_iff.mp body⟩
  | case a l r iha ihl ihr =>
      obtain ⟨va, s₁, runA, rest⟩ := iha hvars h
      cases rest with
      | case_inl arg branch =>
          obtain ⟨hv, rfl⟩ := eval_var_zero arg
          subst hv
          obtain ⟨v, s₂, runL, rest'⟩ := ihl ((hvars.shift _).bind _) branch
          exact ⟨v, s₂, .case_inl runA runL, eval_under_iff.mp (eval_under_iff.mp rest')⟩
      | case_inr arg branch =>
          obtain ⟨hv, rfl⟩ := eval_var_zero arg
          subst hv
          obtain ⟨v, s₂, runR, rest'⟩ := ihr ((hvars.shift _).bind _) branch
          exact ⟨v, s₂, .case_inr runA runR, eval_under_iff.mp (eval_under_iff.mp rest')⟩
  | abort a ih =>
      obtain ⟨va, s₁, runA, rest⟩ := ih hvars h
      cases rest with
      | let₁ arg _ => cases arg
  | iter init body ihInit ihBody =>
      cases h with
      | cfg entryRun follow =>
          obtain ⟨vi, s₁, runInit, rest⟩ := ihInit hvars entryRun
          cases rest with
          | br arg =>
              obtain ⟨hv, rfl⟩ := eval_var_zero arg
              subst hv
              obtain ⟨w, s', loop, runK⟩ :=
                compile_loop_rev (fun {_b _e _v _k _s₀ _s₁ _ℓ _o} hv run => ihBody hv run)
                  follow hvars (fun _ => rfl) rfl rfl
              exact ⟨w, s', .iter runInit loop, runK⟩

/-- Finite executions of a compiled region are exactly a source evaluation
followed by an execution of the continuation under the bound result. -/
theorem compile_eval_iff {free : FreeEnv ν α} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {env : Env α} {vars : Vars ν n} {k : Region Φ} {s s'' : σ} {label : Nat} {out : Value α}
    (hvars : Vars.Relates free bound env vars) :
    LambdaSSA.Semantics.Region.Eval instr env (compile t vars k) s label out s'' ↔
      ∃ (value : Value α) (s' : σ),
        LetIter.Semantics.Eval instr free bound t s value s' ∧
        LambdaSSA.Semantics.Region.Eval instr (extend env value) k s' label out s'' :=
  ⟨fun h => compile_eval_rev t hvars h, fun ⟨_value, _s', run, rest⟩ =>
    compile_eval run hvars rest⟩

variable {faults : Φ → Value α → σ → σ → Prop}

/-- An administrative binder beneath the result is invisible to a faulting
continuation, in both directions. -/
theorem fault_under_iff {env : Env α} {value temp : Value α} {k : Region Φ} {s s' : σ} :
    LambdaSSA.Semantics.Region.Fault instr faults (extend (extend env temp) value) (under k)
        s s' ↔
      LambdaSSA.Semantics.Region.Fault instr faults (extend env value) k s s' :=
  LambdaSSA.Semantics.Region.Fault.renameVars_iff (fun i => by cases i <;> rfl)

/-- Faulting iterations of the compiled loop body come from a source loop fault,
or from a completed source loop whose continuation faults. -/
theorem compile_loopFault_rev {free : FreeEnv ν α} {bound : BoundEnv α n}
    {body : Tm ν Φ (n + 1)} {vars : Vars ν n} {k : Region Φ}
    (ihBodyEval : ∀ {bound' : BoundEnv α (n + 1)} {env' : Env α} {vars' : Vars ν (n + 1)}
      {k' : Region Φ} {s₀ s₁ : σ} {ℓ : Nat} {o : Value α},
      Vars.Relates free bound' env' vars' →
      LambdaSSA.Semantics.Region.Eval instr env' (compile body vars' k') s₀ ℓ o s₁ →
      ∃ value s₂, LetIter.Semantics.Eval instr free bound' body s₀ value s₂ ∧
        LambdaSSA.Semantics.Region.Eval instr (extend env' value) k' s₂ ℓ o s₁)
    (ihBodyFault : ∀ {bound' : BoundEnv α (n + 1)} {env' : Env α} {vars' : Vars ν (n + 1)}
      {k' : Region Φ} {s₀ s₁ : σ},
      Vars.Relates free bound' env' vars' →
      LambdaSSA.Semantics.Region.Fault instr faults env' (compile body vars' k') s₀ s₁ →
      LetIter.Semantics.Fault instr faults free bound' body s₀ s₁ ∨
      ∃ value s₂, LetIter.Semantics.Eval instr free bound' body s₀ value s₂ ∧
        LambdaSSA.Semantics.Region.Fault instr faults (extend env' value) k' s₂ s₁)
    {count : Nat} {blocks : Fin count → Region Φ} {env : Env α}
    {first : Nat} {current : Value α} {s s'' : σ}
    (h : LambdaSSA.Semantics.Region.FollowFault instr faults env blocks first current s s'') :
    Vars.Relates free bound env vars →
    (∀ i, blocks i = compile body vars.bind (.case (.var 0)
      (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) →
    count = 1 → first = 0 →
      LetIter.Semantics.LoopFault instr faults free bound body current s s'' ∨
      ∃ w s', LetIter.Semantics.Loop instr free bound body current s w s' ∧
        LambdaSSA.Semantics.Region.Fault instr faults (extend env w) k s' s'' := by
  induction h using LambdaSSA.Semantics.Region.FollowFault.rec
      (motive_1 := fun _ _ _ _ _ => True) with
  | @body env' count' first' blocks' current' s₀ s₁ inside fault _ =>
      intro hvars hblocks hcount hfirst
      subst hfirst
      rw [hblocks] at fault
      rcases ihBodyFault (hvars.bind current') fault with bodyFault | ⟨w, sw, runBody, faultCase⟩
      · exact Or.inl (.body bodyFault)
      · cases faultCase with
        | case_arg arg => cases arg
        | case_inl arg branch =>
            obtain ⟨hw, hs⟩ := eval_var_zero arg
            subst hw
            exact Or.inr ⟨_, _, .done (hs ▸ runBody),
              (LambdaSSA.Semantics.Region.Fault.renameLabels_iff Nat.succ).mp
                (fault_under_iff.mp (fault_under_iff.mp branch))⟩
        | case_inr arg branch =>
            obtain ⟨_hw, _hs⟩ := eval_var_zero arg
            cases branch with | br argBr => cases argBr
  | @step env' count' first' next blocks' current' middle s₀ s₁ s₂ inside run tail ih =>
      intro hvars hblocks hcount hfirst
      subst hfirst
      rw [hblocks] at run
      obtain ⟨w, sw, runBody, runCase⟩ := ihBodyEval (hvars.bind current') run
      cases runCase with
      | case_inl arg branch =>
          obtain ⟨_hw, _hs⟩ := eval_var_zero arg
          obtain ⟨ℓ, hℓ, _⟩ :=
            LambdaSSA.Semantics.Region.Eval.of_renameLabels
              (eval_under_iff.mp (eval_under_iff.mp branch))
          subst hℓ
          exact False.elim (by cases tail <;> omega)
      | case_inr arg branch =>
          obtain ⟨hw, hs⟩ := eval_var_zero arg
          subst hw
          cases branch with
          | br argBr =>
              obtain ⟨hmid, hs'⟩ := eval_var_zero argBr
              subst hmid
              rcases ih hvars hblocks hcount (by omega) with
                loopFault | ⟨w', s', loop, faultK⟩
              · exact Or.inl (.step (hs ▸ runBody) (hs' ▸ loopFault))
              · exact Or.inr ⟨w', s', .step (hs ▸ runBody) (hs' ▸ loop), faultK⟩
  | _ => trivial

/-- The continuation under which a compiled loop body runs: exiting on `inl`
leaves the loop into the surrounding continuation, exiting on `inr` iterates. -/
theorem compile_loopFault_of_loopFault {free : FreeEnv ν α} {k : Region Φ}
    {m : Nat} {bound : BoundEnv α m} {body : Tm ν Φ (m + 1)} {current : Value α} {s s'' : σ}
    (h : LetIter.Semantics.LoopFault instr faults free bound body current s s'') :
    ∀ (vars : Vars ν m) (env : Env α),
      (∀ {bound' : BoundEnv α (m + 1)} {env' : Env α} {vars' : Vars ν (m + 1)}
        {k' : Region Φ} {s₀ s₁ : σ},
        Vars.Relates free bound' env' vars' →
        (LetIter.Semantics.Fault instr faults free bound' body s₀ s₁ ∨
          ∃ value s₂, LetIter.Semantics.Eval instr free bound' body s₀ value s₂ ∧
            LambdaSSA.Semantics.Region.Fault instr faults (extend env' value) k' s₂ s₁) →
        LambdaSSA.Semantics.Region.Fault instr faults env' (compile body vars' k') s₀ s₁) →
      Vars.Relates free bound env vars →
      LambdaSSA.Semantics.Region.FollowFault instr faults env
        (fun _ : Fin 1 => compile body vars.bind (.case (.var 0)
          (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) 0 current s s'' := by
  induction h using LetIter.Semantics.LoopFault.rec (motive_1 := fun _ _ _ _ _ => True) with
  | body fault _ =>
      intro vars env ihBody hvars
      exact .body (by decide) (ihBody (hvars.bind _) (Or.inl fault))
  | step head _ ih =>
      intro vars env ihBody hvars
      exact .step (by decide) (compile_eval head (hvars.bind _) (.case_inr .var (.br .var)))
        (ih vars env ihBody hvars)
  | _ => trivial

/-- A finite source loop whose continuation faults compiles to a faulting
iteration of the compiled block. -/
theorem compile_loopFault_of_loop {free : FreeEnv ν α} {k : Region Φ}
    {m : Nat} {bound : BoundEnv α m} {body : Tm ν Φ (m + 1)} {current w : Value α} {s s' : σ}
    (h : LetIter.Semantics.Loop instr free bound body current s w s') :
    ∀ (vars : Vars ν m) (env : Env α) {s'' : σ},
      (∀ {bound' : BoundEnv α (m + 1)} {env' : Env α} {vars' : Vars ν (m + 1)}
        {k' : Region Φ} {s₀ s₁ : σ},
        Vars.Relates free bound' env' vars' →
        (LetIter.Semantics.Fault instr faults free bound' body s₀ s₁ ∨
          ∃ value s₂, LetIter.Semantics.Eval instr free bound' body s₀ value s₂ ∧
            LambdaSSA.Semantics.Region.Fault instr faults (extend env' value) k' s₂ s₁) →
        LambdaSSA.Semantics.Region.Fault instr faults env' (compile body vars' k') s₀ s₁) →
      Vars.Relates free bound env vars →
      LambdaSSA.Semantics.Region.Fault instr faults (extend env w) k s' s'' →
      LambdaSSA.Semantics.Region.FollowFault instr faults env
        (fun _ : Fin 1 => compile body vars.bind (.case (.var 0)
          (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) 0 current s s'' := by
  induction h using LetIter.Semantics.Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | done step _ =>
      intro vars env s'' ihBody hvars faultK
      refine .body (by decide) (ihBody (hvars.bind _) (Or.inr ⟨_, _, step, ?_⟩))
      exact .case_inl .var (fault_under_iff.mpr (fault_under_iff.mpr
        ((LambdaSSA.Semantics.Region.Fault.renameLabels_iff Nat.succ).mpr faultK)))
  | step head _ _ ih =>
      intro vars env s'' ihBody hvars faultK
      exact .step (by decide) (compile_eval head (hvars.bind _) (.case_inr .var (.br .var)))
        (ih vars env ihBody hvars faultK)
  | _ => trivial

/-- A compiled region reaches a primitive fault exactly when the source term
does, or when the source term finishes and the continuation faults. -/
theorem compile_fault_iff {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {k : Region Φ} {s s'' : σ}
    (hvars : Vars.Relates free bound env vars) :
    LambdaSSA.Semantics.Region.Fault instr faults env (compile t vars k) s s'' ↔
      LetIter.Semantics.Fault instr faults free bound t s s'' ∨
      ∃ value s', LetIter.Semantics.Eval instr free bound t s value s' ∧
        LambdaSSA.Semantics.Region.Fault instr faults (extend env value) k s' s'' := by
  induction t generalizing env k s s'' with
  | fv x =>
      constructor
      · intro h
        cases h with
        | let₁_arg arg => cases arg
        | let₁_body arg body =>
            cases arg
            exact Or.inr ⟨free x, s, .fv, by simpa only [hvars.free] using body⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h
        · cases run
          exact .let₁_body (by simpa only [hvars.free] using
            (LambdaSSA.Semantics.Tm.Eval.var (instr := instr) (env := env)
              (i := vars.free x) (s := s))) (by simpa only [hvars.free] using fault)
  | bv i =>
      constructor
      · intro h
        cases h with
        | let₁_arg arg => cases arg
        | let₁_body arg body =>
            cases arg
            exact Or.inr ⟨bound i, s, .bv, by simpa only [hvars.bound] using body⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h
        · cases run
          exact .let₁_body (by simpa only [hvars.bound] using
            (LambdaSSA.Semantics.Tm.Eval.var (instr := instr) (env := env)
              (i := vars.bound i) (s := s))) (by simpa only [hvars.bound] using fault)
  | unit =>
      constructor
      · intro h
        cases h with
        | let₁_arg arg => cases arg
        | let₁_body arg body => cases arg; exact Or.inr ⟨.unit, s, .unit, body⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h
        · cases run; exact .let₁_body .unit fault
  | op f a ih =>
      constructor
      · intro h
        rcases (ih hvars).mp h with hA | ⟨value, s', run, fault⟩
        · exact Or.inl (.op_arg hA)
        · cases fault with
          | let₁_arg arg =>
              cases arg with
              | op_arg argArg => cases argArg
              | op_fault argEval step =>
                  obtain ⟨hv, hs⟩ := eval_var_zero argEval
                  subst hv
                  exact Or.inl (.op_fault run (hs ▸ step))
          | let₁_body argEval body =>
              cases argEval with
              | op argVar step =>
                  obtain ⟨hv, hs⟩ := eval_var_zero argVar
                  subst hv
                  exact Or.inr ⟨_, _, .op run (hs ▸ step), fault_under_iff.mp body⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with
          | op_arg arg => exact (ih hvars).mpr (Or.inl arg)
          | op_fault argEval step =>
              exact (ih hvars).mpr (Or.inr ⟨_, _, argEval, .let₁_arg (.op_fault .var step)⟩)
        · cases run with
          | op argEval step =>
              exact (ih hvars).mpr (Or.inr ⟨_, _, argEval,
                .let₁_body (.op .var step) (fault_under_iff.mpr fault)⟩)
  | pair a b iha ihb =>
      constructor
      · intro h
        rcases (iha hvars).mp h with hA | ⟨value, s', run, fault⟩
        · exact Or.inl (.pair_left hA)
        · rcases (ihb (hvars.shift value)).mp fault with h' | ⟨value', s₂, run', fault'⟩
          · exact Or.inl (.pair_right run h')
          · cases fault' with
            | let₁_arg arg => cases arg with
              | pair_left left => cases left
              | pair_right _ right => cases right
            | let₁_body argEval body =>
                cases argEval with
                | pair left right =>
                    cases left; cases right
                    exact Or.inr ⟨_, _, .pair run run',
                      fault_under_iff.mp (fault_under_iff.mp body)⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with
          | pair_left left => exact (iha hvars).mpr (Or.inl left)
          | pair_right left right =>
              exact (iha hvars).mpr
                (Or.inr ⟨_, _, left, (ihb (hvars.shift _)).mpr (Or.inl right)⟩)
        · cases run with
          | pair left right =>
              refine (iha hvars).mpr (Or.inr ⟨_, _, left, (ihb (hvars.shift _)).mpr
                (Or.inr ⟨_, _, right, ?_⟩)⟩)
              exact .let₁_body (.pair .var .var)
                (fault_under_iff.mpr (fault_under_iff.mpr fault))
  | let₁ a b iha ihb =>
      constructor
      · intro h
        rcases (iha hvars).mp h with hA | ⟨value, s', run, fault⟩
        · exact Or.inl (.let₁_arg hA)
        · rcases (ihb (hvars.bind value)).mp fault with h' | ⟨value', s₂, run', fault'⟩
          · exact Or.inl (.let₁_body run h')
          · exact Or.inr ⟨_, _, .let₁ run run', fault_under_iff.mp fault'⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with
          | let₁_arg arg => exact (iha hvars).mpr (Or.inl arg)
          | let₁_body argEval body =>
              exact (iha hvars).mpr
                (Or.inr ⟨_, _, argEval, (ihb (hvars.bind _)).mpr (Or.inl body)⟩)
        · cases run with
          | let₁ argEval body =>
              exact (iha hvars).mpr (Or.inr ⟨_, _, argEval, (ihb (hvars.bind _)).mpr
                (Or.inr ⟨_, _, body, fault_under_iff.mpr fault⟩)⟩)
  | let₂ a b iha ihb =>
      constructor
      · intro h
        rcases (iha hvars).mp h with hA | ⟨value, s', run, fault⟩
        · exact Or.inl (.let₂_arg hA)
        · cases fault with
          | let₂_arg arg => cases arg
          | let₂_body argEval body =>
              obtain ⟨hv, hs⟩ := eval_var_zero argEval
              subst hv
              rcases (ihb (((hvars.shift _).bind _).bind _)).mp body with
                h' | ⟨value', s₂, run', fault'⟩
              · exact Or.inl (.let₂_body (hs ▸ run) h')
              · exact Or.inr ⟨_, _, .let₂ (hs ▸ run) run',
                  fault_under_iff.mp (fault_under_iff.mp (fault_under_iff.mp fault'))⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with
          | let₂_arg arg => exact (iha hvars).mpr (Or.inl arg)
          | let₂_body argEval body =>
              exact (iha hvars).mpr (Or.inr ⟨_, _, argEval, .let₂_body .var
                ((ihb (((hvars.shift _).bind _).bind _)).mpr (Or.inl body))⟩)
        · cases run with
          | let₂ argEval body =>
              refine (iha hvars).mpr (Or.inr ⟨_, _, argEval, .let₂_body .var
                ((ihb (((hvars.shift _).bind _).bind _)).mpr (Or.inr ⟨_, _, body, ?_⟩))⟩)
              exact fault_under_iff.mpr (fault_under_iff.mpr (fault_under_iff.mpr fault))
  | inl a ih =>
      constructor
      · intro h
        rcases (ih hvars).mp h with hA | ⟨value, s', run, fault⟩
        · exact Or.inl (.inl hA)
        · cases fault with
          | let₁_arg arg => cases arg with | inl argArg => cases argArg
          | let₁_body argEval body =>
              cases argEval with
              | inl argVar =>
                  obtain ⟨hv, hs⟩ := eval_var_zero argVar
                  subst hv
                  exact Or.inr ⟨_, _, hs ▸ (LetIter.Semantics.Eval.inl run),
                    fault_under_iff.mp body⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with | inl arg => exact (ih hvars).mpr (Or.inl arg)
        · cases run with
          | inl argEval =>
              exact (ih hvars).mpr (Or.inr ⟨_, _, argEval,
                .let₁_body (.inl .var) (fault_under_iff.mpr fault)⟩)
  | inr a ih =>
      constructor
      · intro h
        rcases (ih hvars).mp h with hA | ⟨value, s', run, fault⟩
        · exact Or.inl (.inr hA)
        · cases fault with
          | let₁_arg arg => cases arg with | inr argArg => cases argArg
          | let₁_body argEval body =>
              cases argEval with
              | inr argVar =>
                  obtain ⟨hv, hs⟩ := eval_var_zero argVar
                  subst hv
                  exact Or.inr ⟨_, _, hs ▸ (LetIter.Semantics.Eval.inr run),
                    fault_under_iff.mp body⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with | inr arg => exact (ih hvars).mpr (Or.inl arg)
        · cases run with
          | inr argEval =>
              exact (ih hvars).mpr (Or.inr ⟨_, _, argEval,
                .let₁_body (.inr .var) (fault_under_iff.mpr fault)⟩)
  | case a l r iha ihl ihr =>
      constructor
      · intro h
        rcases (iha hvars).mp h with hA | ⟨value, s', run, fault⟩
        · exact Or.inl (.case_arg hA)
        · cases fault with
          | case_arg arg => cases arg
          | case_inl argEval branch =>
              obtain ⟨hv, hs⟩ := eval_var_zero argEval
              subst hv
              rcases (ihl ((hvars.shift _).bind _)).mp branch with
                h' | ⟨value', s₂, run', fault'⟩
              · exact Or.inl (.case_inl (hs ▸ run) h')
              · exact Or.inr ⟨_, _, .case_inl (hs ▸ run) run',
                  fault_under_iff.mp (fault_under_iff.mp fault')⟩
          | case_inr argEval branch =>
              obtain ⟨hv, hs⟩ := eval_var_zero argEval
              subst hv
              rcases (ihr ((hvars.shift _).bind _)).mp branch with
                h' | ⟨value', s₂, run', fault'⟩
              · exact Or.inl (.case_inr (hs ▸ run) h')
              · exact Or.inr ⟨_, _, .case_inr (hs ▸ run) run',
                  fault_under_iff.mp (fault_under_iff.mp fault')⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with
          | case_arg arg => exact (iha hvars).mpr (Or.inl arg)
          | case_inl argEval branch =>
              exact (iha hvars).mpr (Or.inr ⟨_, _, argEval, .case_inl .var
                ((ihl ((hvars.shift _).bind _)).mpr (Or.inl branch))⟩)
          | case_inr argEval branch =>
              exact (iha hvars).mpr (Or.inr ⟨_, _, argEval, .case_inr .var
                ((ihr ((hvars.shift _).bind _)).mpr (Or.inl branch))⟩)
        · cases run with
          | case_inl argEval branch =>
              exact (iha hvars).mpr (Or.inr ⟨_, _, argEval, .case_inl .var
                ((ihl ((hvars.shift _).bind _)).mpr (Or.inr ⟨_, _, branch,
                  fault_under_iff.mpr (fault_under_iff.mpr fault)⟩))⟩)
          | case_inr argEval branch =>
              exact (iha hvars).mpr (Or.inr ⟨_, _, argEval, .case_inr .var
                ((ihr ((hvars.shift _).bind _)).mpr (Or.inr ⟨_, _, branch,
                  fault_under_iff.mpr (fault_under_iff.mpr fault)⟩))⟩)
  | abort a ih =>
      constructor
      · intro h
        rcases (ih hvars).mp h with hA | ⟨value, s', run, fault⟩
        · exact Or.inl (.abort_arg hA)
        · cases fault with
          | let₁_arg arg => cases arg with | abort_arg argArg => cases argArg
          | let₁_body argEval _ => cases argEval
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with | abort_arg arg => exact (ih hvars).mpr (Or.inl arg)
        · cases run
  | iter init body ihInit ihBody =>
      constructor
      · intro h
        cases h with
        | cfg_entry fault =>
            rcases (ihInit hvars).mp fault with h' | ⟨value, s', _, faultBr⟩
            · exact Or.inl (.iter_init h')
            · cases faultBr with | br arg => cases arg
        | cfg_follow run fault =>
            obtain ⟨vi, s₁, runInit, rest⟩ := compile_eval_rev init hvars run
            cases rest with
            | br arg =>
                obtain ⟨hv, hs⟩ := eval_var_zero arg
                subst hv
                rcases compile_loopFault_rev
                    (fun {_b _e _v _k _s₀ _s₁ _ℓ _o} hv run => compile_eval_rev body hv run)
                    (fun {_b _e _v _k _s₀ _s₁} hv f => (ihBody hv).mp f)
                    fault hvars (fun _ => rfl) rfl rfl with
                  loopFault | ⟨w, s₂, loop, faultK⟩
                · exact Or.inl (.iter_loop (hs ▸ runInit) (hs ▸ loopFault))
                · exact Or.inr ⟨w, s₂, .iter (hs ▸ runInit) (hs ▸ loop), faultK⟩
      · rintro (h | ⟨value, s', run, fault⟩)
        · cases h with
          | iter_init arg => exact .cfg_entry ((ihInit hvars).mpr (Or.inl arg))
          | iter_loop argEval loop =>
              exact .cfg_follow (compile_return_eval argEval hvars 0)
                (compile_loopFault_of_loopFault loop vars env
                  (fun {_b _e _v _k _s₀ _s₁} hv d => (ihBody hv).mpr d) hvars)
        · cases run with
          | iter argEval loop =>
              exact .cfg_follow (compile_return_eval argEval hvars 0)
                (compile_loopFault_of_loop loop vars env
                  (fun {_b _e _v _k _s₀ _s₁} hv d => (ihBody hv).mpr d) hvars fault)

namespace External

variable {prim : Φ → Value α → σ → Prop}

/-- An administrative binder beneath the result is invisible to a divergent
continuation, in both directions. -/
theorem diverges_under_iff {env : Env α} {value temp : Value α} {k : Region Φ} {s : σ} :
    LambdaSSA.Semantics.External.Diverges instr prim
        (.region (extend (extend env temp) value) (under k) s) ↔
      LambdaSSA.Semantics.External.Diverges instr prim (.region (extend env value) k s) :=
  LambdaSSA.Semantics.External.Diverges.renameVars_iff (fun i => by cases i <;> rfl)

/-- A finite source evaluation followed by a divergent continuation compiles to
a divergent region, preserving the prefix's machine-state transitions. -/
theorem compile_eval_diverges {free : FreeEnv ν α} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α}
    (ht : LetIter.Semantics.Eval instr free bound t s value s')
    {env : Env α} {vars : Vars ν n} {k : Region Φ}
    (hvars : Vars.Relates free bound env vars)
    (hk : LambdaSSA.Semantics.External.Diverges instr prim
      (.region (extend env value) k s')) :
    LambdaSSA.Semantics.External.Diverges instr prim (.region env (compile t vars k) s) := by
  induction ht using LetIter.Semantics.Eval.rec
      (motive_2 := fun {m} bound body current s value s' _ =>
        ∀ {env : Env α} {vars : Vars ν m} {k : Region Φ},
          Vars.Relates free bound env vars →
          LambdaSSA.Semantics.External.Diverges instr prim (.region (extend env value) k s') →
          LambdaSSA.Semantics.External.Diverges instr prim (.follow env
            (fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
              (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0))))
            0 current s)) generalizing env k with
  | fv =>
      apply LambdaSSA.Semantics.External.Diverges.fold_core
      apply LambdaSSA.Semantics.DivergenceStep.let₁ ?_ hk
      simpa only [hvars.free] using
        (LambdaSSA.Semantics.Tm.Eval.var (instr := instr) (env := env)
          (i := vars.free _) (s := _))
  | bv =>
      apply LambdaSSA.Semantics.External.Diverges.fold_core
      apply LambdaSSA.Semantics.DivergenceStep.let₁ ?_ hk
      simpa only [hvars.bound] using
        (LambdaSSA.Semantics.Tm.Eval.var (instr := instr) (env := env)
          (i := vars.bound _) (s := _))
  | unit => exact .fold_core (.let₁ .unit hk)
  | op arg step ih =>
      exact ih hvars (.fold_core (.let₁ (.op .var step) (diverges_under_iff.mpr hk)))
  | let₁ arg body ihArg ihBody =>
      exact ihArg hvars (ihBody (hvars.bind _) (diverges_under_iff.mpr hk))
  | pair left right ihLeft ihRight =>
      exact ihLeft hvars (ihRight (hvars.shift _) (.fold_core (.let₁ (.pair .var .var)
        (diverges_under_iff.mpr (diverges_under_iff.mpr hk)))))
  | let₂ arg body ihArg ihBody =>
      exact ihArg hvars (.fold_core (.let₂ .var (ihBody (((hvars.shift _).bind _).bind _)
        (diverges_under_iff.mpr (diverges_under_iff.mpr (diverges_under_iff.mpr hk))))))
  | inl arg ih => exact ih hvars (.fold_core (.let₁ (.inl .var) (diverges_under_iff.mpr hk)))
  | inr arg ih => exact ih hvars (.fold_core (.let₁ (.inr .var) (diverges_under_iff.mpr hk)))
  | case_inl scrutinee branch ihScrutinee ihBranch =>
      exact ihScrutinee hvars (.fold_core (.case_inl .var
        (ihBranch ((hvars.shift _).bind _)
          (diverges_under_iff.mpr (diverges_under_iff.mpr hk)))))
  | case_inr scrutinee branch ihScrutinee ihBranch =>
      exact ihScrutinee hvars (.fold_core (.case_inr .var
        (ihBranch ((hvars.shift _).bind _)
          (diverges_under_iff.mpr (diverges_under_iff.mpr hk)))))
  | iter init loop ihInit ihLoop =>
      exact .fold_core (.cfg_follow (compile_return_eval init hvars 0) (ihLoop hvars hk))
  | done step ih =>
      rename_i env vars k hvars hk
      refine .fold_core (.follow_body (by decide) (ih (hvars.bind _) (.fold_core
        (.case_inl .var ?_))))
      exact diverges_under_iff.mpr (diverges_under_iff.mpr
        ((LambdaSSA.Semantics.External.Diverges.renameLabels_iff Nat.succ).mpr hk))
  | step head tail ihHead ihTail =>
      rename_i env vars k hvars hk
      exact .fold_core (.follow_next (by decide)
        (compile_eval head (hvars.bind _) (.case_inr .var (.br .var))) (ihTail hvars hk))

/-- An infinite source loop compiles to infinite iteration of the compiled
block, reusing the environment captured at the control-flow-graph boundary. -/
theorem loop_compile_diverges {free : FreeEnv ν α} {bound : BoundEnv α n}
    {body : Tm ν Φ (n + 1)} {env : Env α} {vars : Vars ν n} {k : Region Φ}
    (hvars : Vars.Relates free bound env vars)
    (hbody : ∀ (current : Value α) (s : σ),
      LetIter.Semantics.External.Diverges instr free prim
        (.term (LetIter.Semantics.extend bound current) body s) →
      LambdaSSA.Semantics.External.Diverges instr prim (.region (extend env current)
        (compile body vars.bind (.case (.var 0)
          (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) s))
    {current : Value α} {s : σ}
    (hloop : LetIter.Semantics.External.Diverges instr free prim
      (.loop bound body current s)) :
    LambdaSSA.Semantics.External.Diverges instr prim (.follow env
      (fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
        (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) 0 current s) := by
  apply LambdaSSA.Semantics.External.Diverges.coinduct
    (fun c => (∃ current s, LetIter.Semantics.External.Diverges instr free prim
      (.loop bound body current s) ∧ c = .follow env
        (fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
          (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) 0 current s) ∨
      LambdaSSA.Semantics.External.Diverges instr prim c) ?_
    (Or.inl ⟨current, s, hloop, rfl⟩)
  intro c hc
  rcases hc with ⟨current, s, hloop, rfl⟩ | hd
  · cases hloop.unfold with
    | core core => cases core with
      | loop_body hd => exact .core (.follow_body (by decide) (Or.inr (hbody current s hd)))
      | loop_step head tail =>
          exact .core (.follow_next (by decide)
            (compile_eval head (hvars.bind _) (.case_inr .var (.br .var)))
            (Or.inl ⟨_, _, tail, rfl⟩))
  · exact hd.unfold.mono (fun _ h => Or.inr h)

/-- Every divergent source term compiles to a divergent region, for any
continuation and any environment agreeing on the source variables. -/
theorem compile_diverges {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {k : Region Φ} {s : σ}
    (hvars : Vars.Relates free bound env vars)
    (ht : LetIter.Semantics.External.Diverges instr free prim (.term bound t s)) :
    LambdaSSA.Semantics.External.Diverges instr prim (.region env (compile t vars k) s) := by
  induction t generalizing env k s with
  | fv | bv | unit => cases ht.unfold with | core core => cases core
  | op f a ih =>
      cases ht.unfold with
      | core core => cases core with | op hd => exact ih hvars hd
      | primitive arg div =>
          exact compile_eval_diverges arg hvars (.fold (.let₁_arg (.primitive .var div)))
  | let₁ a b iha ihb =>
      cases ht.unfold with
      | core core => cases core with
        | let₁_arg hd => exact iha hvars hd
        | let₁_body ha hd => exact compile_eval_diverges ha hvars (ihb (hvars.bind _) hd)
  | pair a b iha ihb =>
      cases ht.unfold with
      | core core => cases core with
        | pair_left hd => exact iha hvars hd
        | pair_right ha hd => exact compile_eval_diverges ha hvars (ihb (hvars.shift _) hd)
  | let₂ a b iha ihb =>
      cases ht.unfold with
      | core core => cases core with
        | let₂_arg hd => exact iha hvars hd
        | let₂_body ha hd =>
            exact compile_eval_diverges ha hvars
              (.fold_core (.let₂ .var (ihb (((hvars.shift _).bind _).bind _) hd)))
  | inl a ih => cases ht.unfold with | core core => cases core with | inl hd => exact ih hvars hd
  | inr a ih => cases ht.unfold with | core core => cases core with | inr hd => exact ih hvars hd
  | case a l r iha ihl ihr =>
      cases ht.unfold with
      | core core => cases core with
        | case_scrutinee hd => exact iha hvars hd
        | case_inl ha hd =>
            exact compile_eval_diverges ha hvars
              (.fold_core (.case_inl .var (ihl ((hvars.shift _).bind _) hd)))
        | case_inr ha hd =>
            exact compile_eval_diverges ha hvars
              (.fold_core (.case_inr .var (ihr ((hvars.shift _).bind _) hd)))
  | abort a ih => cases ht.unfold with | core core => cases core with | abort hd => exact ih hvars hd
  | iter init body ihInit ihBody =>
      cases ht.unfold with
      | core core => cases core with
        | iter_init hd => exact .fold_core (.cfg_entry (ihInit hvars hd))
        | iter_loop hi hd =>
            exact .fold_core (.cfg_follow (compile_return_eval hi hvars 0)
              (loop_compile_diverges hvars (fun current _ h => ihBody (hvars.bind current) h) hd))

/-- Infinite iteration of the compiled loop body comes from an infinite source
loop, or from a finite source loop whose continuation runs forever. The split
is classical: either some finite prefix escapes into the continuation, or none
does and the source loop itself is infinite. -/
theorem compile_loop_diverges_rev {free : FreeEnv ν α} {bound : BoundEnv α n}
    {body : Tm ν Φ (n + 1)} {env : Env α} {vars : Vars ν n} {k : Region Φ}
    (ihBody : ∀ {bound' : BoundEnv α (n + 1)} {env' : Env α} {vars' : Vars ν (n + 1)}
      {k' : Region Φ} {s₀ : σ},
      Vars.Relates free bound' env' vars' →
      LambdaSSA.Semantics.External.Diverges instr prim
        (.region env' (compile body vars' k') s₀) →
      LetIter.Semantics.External.Diverges instr free prim (.term bound' body s₀) ∨
      ∃ value s₁, LetIter.Semantics.Eval instr free bound' body s₀ value s₁ ∧
        LambdaSSA.Semantics.External.Diverges instr prim (.region (extend env' value) k' s₁))
    (hvars : Vars.Relates free bound env vars) {current : Value α} {s : σ}
    (h : LambdaSSA.Semantics.External.Diverges instr prim (.follow env
      (fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
        (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) 0 current s)) :
    LetIter.Semantics.External.Diverges instr free prim (.loop bound body current s) ∨
    ∃ w s', LetIter.Semantics.Loop instr free bound body current s w s' ∧
      LambdaSSA.Semantics.External.Diverges instr prim (.region (extend env w) k s') := by
  by_cases hP : ∃ w s', LetIter.Semantics.Loop instr free bound body current s w s' ∧
      LambdaSSA.Semantics.External.Diverges instr prim (.region (extend env w) k s')
  · exact Or.inr hP
  refine Or.inl (LetIter.Semantics.External.Diverges.coinduct
    (fun c => (∃ cur st, c = .loop bound body cur st ∧
      LambdaSSA.Semantics.External.Diverges instr prim (.follow env
        (fun (_ : Fin 1) => compile body vars.bind (.case (.var 0)
          (under (under (k.renameLabels Nat.succ))) (.br 0 (.var 0)))) 0 cur st) ∧
      ¬ ∃ w s', LetIter.Semantics.Loop instr free bound body cur st w s' ∧
        LambdaSSA.Semantics.External.Diverges instr prim (.region (extend env w) k s')) ∨
      LetIter.Semantics.External.Diverges instr free prim c)
    ?_ (Or.inl ⟨current, s, rfl, h, hP⟩))
  rintro c (⟨cur, st, rfl, hfollow, hnot⟩ | hdone)
  swap
  · exact hdone.unfold.mono (fun _ h => Or.inr h)
  cases hfollow.unfold with
  | core core => cases core with
    | follow_body inside rest =>
        rcases ihBody (hvars.bind cur) rest with hbd | ⟨w, sw, runBody, divCase⟩
        · exact .core (.loop_body (Or.inr hbd))
        · cases divCase.unfold with
          | case_arg div => cases div
          | core c₂ => cases c₂ with
            | case_inl arg rest' =>
                obtain ⟨hw, hs⟩ := eval_var_zero arg
                subst hw
                exact absurd ⟨_, _, .done (hs ▸ runBody),
                  (LambdaSSA.Semantics.External.Diverges.renameLabels_iff Nat.succ).mp
                    (diverges_under_iff.mp (diverges_under_iff.mp rest'))⟩ hnot
            | case_inr arg rest' =>
                cases rest'.unfold with
                | core c₃ => cases c₃
                | br div => cases div
    | follow_next inside head rest =>
        obtain ⟨w, sw, runBody, runCase⟩ := compile_eval_rev body (hvars.bind cur) head
        cases runCase with
        | case_inl arg branch =>
            obtain ⟨_hw, _hs⟩ := eval_var_zero arg
            obtain ⟨ℓ, hℓ, _⟩ :=
              LambdaSSA.Semantics.Region.Eval.of_renameLabels
                (eval_under_iff.mp (eval_under_iff.mp branch))
            subst hℓ
            exact absurd rest (by
              intro hd
              cases hd.unfold with | core c₄ => cases c₄ <;> omega)
        | case_inr arg branch =>
            obtain ⟨hw, hs⟩ := eval_var_zero arg
            subst hw
            cases branch with
            | br argBr =>
                obtain ⟨hmid, hs'⟩ := eval_var_zero argBr
                subst hmid
                refine .core (.loop_step (hs ▸ runBody) (Or.inl ⟨_, _, rfl, hs' ▸ rest, ?_⟩))
                rintro ⟨w', s', loop, divK⟩
                exact hnot ⟨w', s', .step (hs ▸ runBody) (hs' ▸ loop), divK⟩

/-- Every infinite execution of a compiled region comes from an infinite source
execution, or from a finite one followed by an infinite continuation. -/
theorem compile_diverges_rev {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {k : Region Φ} {s : σ}
    (hvars : Vars.Relates free bound env vars)
    (h : LambdaSSA.Semantics.External.Diverges instr prim
      (.region env (compile t vars k) s)) :
    LetIter.Semantics.External.Diverges instr free prim (.term bound t s) ∨
    ∃ value s', LetIter.Semantics.Eval instr free bound t s value s' ∧
      LambdaSSA.Semantics.External.Diverges instr prim (.region (extend env value) k s') := by
  induction t generalizing env k s with
  | fv x =>
      cases h.unfold with
      | let₁_arg div => cases div
      | core core => cases core with
        | let₁ arg rest =>
            cases arg
            exact Or.inr ⟨free x, s, .fv, by simpa only [hvars.free] using rest⟩
  | bv i =>
      cases h.unfold with
      | let₁_arg div => cases div
      | core core => cases core with
        | let₁ arg rest =>
            cases arg
            exact Or.inr ⟨bound i, s, .bv, by simpa only [hvars.bound] using rest⟩
  | unit =>
      cases h.unfold with
      | let₁_arg div => cases div
      | core core => cases core with
        | let₁ arg rest => cases arg; exact Or.inr ⟨.unit, s, .unit, rest⟩
  | op f a ih =>
      rcases ih hvars h with hd | ⟨va, s₁, runA, rest⟩
      · exact Or.inl (.fold (.core (.op hd)))
      · cases rest.unfold with
        | let₁_arg div =>
            cases div with
            | op_arg argDiv => cases argDiv
            | primitive argEval step =>
                obtain ⟨hv, hs⟩ := eval_var_zero argEval
                subst hv
                exact Or.inl (.fold (.primitive runA (hs ▸ step)))
        | core core => cases core with
          | let₁ arg rest' =>
              cases arg with
              | op argVar step =>
                  obtain ⟨hv, hs⟩ := eval_var_zero argVar
                  subst hv
                  exact Or.inr ⟨_, _, .op runA (hs ▸ step), diverges_under_iff.mp rest'⟩
  | pair a b iha ihb =>
      rcases iha hvars h with hd | ⟨va, s₁, runA, rest⟩
      · exact Or.inl (.fold (.core (.pair_left hd)))
      · rcases ihb (hvars.shift va) rest with hd | ⟨vb, s₂, runB, rest'⟩
        · exact Or.inl (.fold (.core (.pair_right runA hd)))
        · cases rest'.unfold with
          | let₁_arg div =>
              cases div with
              | pair_left left => cases left
              | pair_right _ right => cases right
          | core core => cases core with
            | let₁ arg rest'' =>
                cases arg with
                | pair left right =>
                    cases left; cases right
                    exact Or.inr ⟨_, _, .pair runA runB,
                      diverges_under_iff.mp (diverges_under_iff.mp rest'')⟩
  | let₁ a b iha ihb =>
      rcases iha hvars h with hd | ⟨va, s₁, runA, rest⟩
      · exact Or.inl (.fold (.core (.let₁_arg hd)))
      · rcases ihb (hvars.bind va) rest with hd | ⟨vb, s₂, runB, rest'⟩
        · exact Or.inl (.fold (.core (.let₁_body runA hd)))
        · exact Or.inr ⟨_, _, .let₁ runA runB, diverges_under_iff.mp rest'⟩
  | let₂ a b iha ihb =>
      rcases iha hvars h with hd | ⟨va, s₁, runA, rest⟩
      · exact Or.inl (.fold (.core (.let₂_arg hd)))
      · cases rest.unfold with
        | let₂_arg div => cases div
        | core core => cases core with
          | let₂ arg rest' =>
              obtain ⟨hv, hs⟩ := eval_var_zero arg
              subst hv
              rcases ihb (((hvars.shift _).bind _).bind _) rest' with hd | ⟨vb, s₂, runB, rest''⟩
              · exact Or.inl (.fold (.core (.let₂_body (hs ▸ runA) hd)))
              · exact Or.inr ⟨_, _, .let₂ (hs ▸ runA) runB,
                  diverges_under_iff.mp (diverges_under_iff.mp
                    (diverges_under_iff.mp rest''))⟩
  | inl a ih =>
      rcases ih hvars h with hd | ⟨va, s₁, runA, rest⟩
      · exact Or.inl (.fold (.core (.inl hd)))
      · cases rest.unfold with
        | let₁_arg div => cases div with | inl argDiv => cases argDiv
        | core core => cases core with
          | let₁ arg rest' =>
              cases arg with
              | inl argVar =>
                  obtain ⟨hv, hs⟩ := eval_var_zero argVar
                  subst hv
                  exact Or.inr ⟨_, _, hs ▸ (LetIter.Semantics.Eval.inl runA),
                    diverges_under_iff.mp rest'⟩
  | inr a ih =>
      rcases ih hvars h with hd | ⟨va, s₁, runA, rest⟩
      · exact Or.inl (.fold (.core (.inr hd)))
      · cases rest.unfold with
        | let₁_arg div => cases div with | inr argDiv => cases argDiv
        | core core => cases core with
          | let₁ arg rest' =>
              cases arg with
              | inr argVar =>
                  obtain ⟨hv, hs⟩ := eval_var_zero argVar
                  subst hv
                  exact Or.inr ⟨_, _, hs ▸ (LetIter.Semantics.Eval.inr runA),
                    diverges_under_iff.mp rest'⟩
  | case a l r iha ihl ihr =>
      rcases iha hvars h with hd | ⟨va, s₁, runA, rest⟩
      · exact Or.inl (.fold (.core (.case_scrutinee hd)))
      · cases rest.unfold with
        | case_arg div => cases div
        | core core => cases core with
          | case_inl arg rest' =>
              obtain ⟨hv, hs⟩ := eval_var_zero arg
              subst hv
              rcases ihl ((hvars.shift _).bind _) rest' with hd | ⟨v, s₂, runL, rest''⟩
              · exact Or.inl (.fold (.core (.case_inl (hs ▸ runA) hd)))
              · exact Or.inr ⟨_, _, .case_inl (hs ▸ runA) runL,
                  diverges_under_iff.mp (diverges_under_iff.mp rest'')⟩
          | case_inr arg rest' =>
              obtain ⟨hv, hs⟩ := eval_var_zero arg
              subst hv
              rcases ihr ((hvars.shift _).bind _) rest' with hd | ⟨v, s₂, runR, rest''⟩
              · exact Or.inl (.fold (.core (.case_inr (hs ▸ runA) hd)))
              · exact Or.inr ⟨_, _, .case_inr (hs ▸ runA) runR,
                  diverges_under_iff.mp (diverges_under_iff.mp rest'')⟩
  | abort a ih =>
      rcases ih hvars h with hd | ⟨va, s₁, runA, rest⟩
      · exact Or.inl (.fold (.core (.abort hd)))
      · cases rest.unfold with
        | let₁_arg div => cases div with | abort_arg argDiv => cases argDiv
        | core core => cases core with | let₁ arg _ => cases arg
  | iter init body ihInit ihBody =>
      cases h.unfold with
      | core core => cases core with
        | cfg_entry rest =>
            rcases ihInit hvars rest with hd | ⟨vi, s₁, _, restBr⟩
            · exact Or.inl (.fold (.core (.iter_init hd)))
            · cases restBr.unfold with
              | core c₂ => cases c₂
              | br div => cases div
        | cfg_follow run rest =>
            obtain ⟨vi, s₁, runInit, restEntry⟩ := compile_eval_rev init hvars run
            cases restEntry with
            | br arg =>
                obtain ⟨hv, hs⟩ := eval_var_zero arg
                subst hv
                rcases compile_loop_diverges_rev
                    (fun {_b _e _v _k _s₀} hv d => ihBody hv d) hvars (hs ▸ rest) with
                  hd | ⟨w, s₂, loop, divK⟩
                · exact Or.inl (.fold (.core (.iter_loop runInit hd)))
                · exact Or.inr ⟨w, s₂, .iter runInit loop, divK⟩

/-- A compiled region runs forever exactly when the source term does, or when
the source term finishes and the continuation runs forever. Explicitly
divergent primitives are tracked by the same predicate on both sides. -/
theorem compile_diverges_iff {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {k : Region Φ} {s : σ}
    (hvars : Vars.Relates free bound env vars) :
    LambdaSSA.Semantics.External.Diverges instr prim (.region env (compile t vars k) s) ↔
      LetIter.Semantics.External.Diverges instr free prim (.term bound t s) ∨
      ∃ value s', LetIter.Semantics.Eval instr free bound t s value s' ∧
        LambdaSSA.Semantics.External.Diverges instr prim
          (.region (extend env value) k s') :=
  ⟨compile_diverges_rev t hvars, fun h => by
    rcases h with hd | ⟨_value, _s', run, divK⟩
    · exact compile_diverges t hvars hd
    · exact compile_eval_diverges run hvars divK⟩

end External

/-- With a returning continuation the correspondence is exact: the compiled
region exits at the chosen label with the source result and final state. -/
theorem compile_return_eval_iff {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {s s' : σ} {exit label : Nat} {out : Value α}
    (hvars : Vars.Relates free bound env vars) :
    LambdaSSA.Semantics.Region.Eval instr env (compile t vars (.br exit (.var 0)))
        s label out s' ↔
      label = exit ∧ LetIter.Semantics.Eval instr free bound t s out s' := by
  rw [compile_eval_iff hvars]
  constructor
  · rintro ⟨value, s₀, run, rest⟩
    cases rest with
    | br arg =>
        obtain ⟨hv, hs⟩ := eval_var_zero arg
        subst hv
        exact ⟨rfl, hs ▸ run⟩
  · rintro ⟨rfl, run⟩
    exact ⟨out, s', run, .br .var⟩

/-- With a returning continuation the compiled region faults exactly when the
source term does. -/
theorem compile_return_fault_iff {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {s s' : σ} {exit : Nat}
    (hvars : Vars.Relates free bound env vars) :
    LambdaSSA.Semantics.Region.Fault instr faults env
        (compile t vars (.br exit (.var 0))) s s' ↔
      LetIter.Semantics.Fault instr faults free bound t s s' := by
  rw [compile_fault_iff t hvars]
  constructor
  · rintro (h | ⟨value, s₀, _, fault⟩)
    · exact h
    · cases fault with | br arg => cases arg
  · exact Or.inl

/-- With a returning continuation the compiled region runs forever exactly when
the source term does. -/
theorem compile_return_diverges_iff {prim : Φ → Value α → σ → Prop}
    {free : FreeEnv ν α} {bound : BoundEnv α n} (t : Tm ν Φ n)
    {env : Env α} {vars : Vars ν n} {s : σ} {exit : Nat}
    (hvars : Vars.Relates free bound env vars) :
    LambdaSSA.Semantics.External.Diverges instr prim
        (.region env (compile t vars (.br exit (.var 0))) s) ↔
      LetIter.Semantics.External.Diverges instr free prim (.term bound t s) := by
  rw [External.compile_diverges_iff t hvars]
  constructor
  · rintro (h | ⟨value, s₀, _, div⟩)
    · exact h
    · cases div.unfold with
      | core core => cases core
      | br div' => cases div'
  · exact Or.inl

end Silmaril.Isotope.Morphism.IterSSA

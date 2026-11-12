module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Structural
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault.Structural
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External.Structural

/-!
# Semantic substitution for the let-iter operational semantics

The operational development already knows that renaming bound variables
preserves and reflects evaluation, faults and divergence. Substitution is
strictly harder: a substituted term is *run*, and running it once per
occurrence duplicates and reorders its effects. The honest hypothesis is
therefore that the substitution behaves like an environment of
already-computed values.

`PureSubst instr free bound θ values` says exactly that: every component
`θ i` evaluates to `values i` from every machine state, leaves the state
alone, and has no other finite outcome. Under that hypothesis `Eval` through
`Tm.bsubst θ` is interchangeable with `Eval` in the environment `values`, in
both directions. The fault and divergence transfers need the two further
hypotheses that no component faults and no component diverges; these cannot be
derived from `PureSubst`, because the fault oracle and the
primitive-divergence oracle are independent parameters of the semantics.

This is the let-iter counterpart of `Silmaril.Isotope.LambdaSSA.Tm.Eval.congr_env_on`
and `Silmaril.Isotope.LambdaSSA.Tm.Eval.state_eq_of_pure`.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop}
    {prim : Φ → Value α → σ → Prop}
    {free : FreeEnv ν α}

/-- A substitution that behaves like an environment of already-computed values:
each component evaluates to its value from every machine state, without moving
it, and has no other finite outcome. -/
structure PureSubst (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α)
    {n m : Nat} (bound : BoundEnv α m) (θ : Fin n → Tm ν Φ m) (values : BoundEnv α n) : Prop where
  /-- Every component reaches its value from every state, leaving the state alone. -/
  eval : ∀ (i : Fin n) (s : σ), Eval instr free bound (θ i) s (values i) s
  /-- Every component has that one outcome and no other. -/
  unique : ∀ {i : Fin n} {s v s'}, Eval instr free bound (θ i) s v s' → v = values i ∧ s' = s

namespace PureSubst

/-- A substitution of values stays one under an extra common binder. -/
theorem up {n m : Nat} {bound : BoundEnv α m} {θ : Fin n → Tm ν Φ m}
    {values : BoundEnv α n} (h : PureSubst instr free bound θ values) (value : Value α) :
    PureSubst instr free (extend bound value) (Tm.upSub θ) (extend values value) where
  eval := by
    intro i s
    induction i using Fin.cases with
    | zero => exact .bv
    | succ j =>
        simpa only [Tm.upSub, Fin.cases_succ, Tm.lift, extend_succ] using
          (h.eval j s).rename Fin.succ (extend bound value) (fun _ => rfl)
  unique := by
    intro i s v s' hv
    induction i using Fin.cases with
    | zero => cases hv; exact ⟨rfl, rfl⟩
    | succ j =>
        simp only [Tm.upSub, Fin.cases_succ, Tm.lift] at hv
        exact (Eval.rename_iff (bound := bound) (ρ := Fin.succ) (t := θ j)
          (fun _ => rfl)).mp hv |> h.unique

/-- The substitution that opens the outermost binder with an already-evaluated
term, leaving every older variable alone. -/
theorem instantiate {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n} {value : Value α}
    (eval : ∀ s : σ, Eval instr free bound a s value s)
    (unique : ∀ {s v s'}, Eval instr free bound a s v s' → v = value ∧ s' = s) :
    PureSubst instr free bound (Fin.cases a (fun i => .bv i)) (extend bound value) where
  eval := by
    intro i s
    induction i using Fin.cases with
    | zero => exact eval s
    | succ j => exact .bv
  unique := by
    intro i s v s' hv
    induction i using Fin.cases with
    | zero => exact unique hv
    | succ j => cases hv; exact ⟨rfl, rfl⟩

end PureSubst

/-! ## Evaluation -/

/-- Evaluation transfers along a substitution of values: what the term does in
the environment of values, its substitution instance does in the ambient one. -/
theorem Eval.bsubst {n : Nat} {values : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {value : Value α} (h : Eval instr free values t s value s') :
    ∀ {m : Nat} {bound : BoundEnv α m} {θ : Fin n → Tm ν Φ m},
      PureSubst instr free bound θ values → Eval instr free bound (t.bsubst θ) s value s' := by
  induction h using Eval.rec
      (motive_2 := fun {n} values body current s value s' _ =>
        ∀ {m : Nat} {bound : BoundEnv α m} {θ : Fin n → Tm ν Φ m},
          PureSubst instr free bound θ values →
          Loop instr free bound (body.bsubst (Tm.upSub θ)) current s value s') with
  | fv => intro _ _ _ _; exact .fv
  | bv => intro _ _ _ hθ; exact hθ.eval _ _
  | unit => intro _ _ _ _; exact .unit
  | op _ step ih => intro _ _ _ hθ; exact .op (ih hθ) step
  | let₁ _ _ iha ihb => intro _ _ _ hθ; exact .let₁ (iha hθ) (ihb (hθ.up _))
  | pair _ _ ihl ihr => intro _ _ _ hθ; exact .pair (ihl hθ) (ihr hθ)
  | let₂ _ _ iha ihb => intro _ _ _ hθ; exact .let₂ (iha hθ) (ihb ((hθ.up _).up _))
  | inl _ ih => intro _ _ _ hθ; exact .inl (ih hθ)
  | inr _ ih => intro _ _ _ hθ; exact .inr (ih hθ)
  | case_inl _ _ ihe ihl => intro _ _ _ hθ; exact .case_inl (ihe hθ) (ihl (hθ.up _))
  | case_inr _ _ ihe ihr => intro _ _ _ hθ; exact .case_inr (ihe hθ) (ihr (hθ.up _))
  | iter _ _ ihi ihl => intro _ _ _ hθ; exact .iter (ihi hθ) (ihl hθ)
  | done _ ih => rename_i _ _ _ hθ; exact .done (ih (hθ.up _))
  | step _ _ ihh iht => rename_i _ _ _ hθ; exact .step (ihh (hθ.up _)) (iht hθ)

/-- Iterations transfer along a substitution of values. -/
theorem Loop.bsubst {n m : Nat} {values : BoundEnv α n} {bound : BoundEnv α m}
    {θ : Fin n → Tm ν Φ m} {body : Tm ν Φ (n + 1)} {current value : Value α} {s s' : σ}
    (hθ : PureSubst instr free bound θ values)
    (h : Loop instr free values body current s value s') :
    Loop instr free bound (body.bsubst (Tm.upSub θ)) current s value s' :=
  h.map_body (fun hb => hb.bsubst (hθ.up _))

/-- Evaluation also reflects along a substitution of values: the substitution
instance can do nothing the term could not do in the environment of values. -/
theorem Eval.of_bsubst {n m : Nat} {values : BoundEnv α n} {bound : BoundEnv α m}
    {θ : Fin n → Tm ν Φ m} {t : Tm ν Φ n} {s s' : σ} {value : Value α}
    (hθ : PureSubst instr free bound θ values)
    (h : Eval instr free bound (t.bsubst θ) s value s') :
    Eval instr free values t s value s' := by
  induction t generalizing m s s' value with
  | fv x => cases h; exact .fv
  | bv i => obtain ⟨rfl, rfl⟩ := hθ.unique h; exact .bv
  | op f a ih => cases h with | op arg step => exact .op (ih hθ arg) step
  | let₁ a b iha ihb =>
      cases h with | let₁ arg body => exact .let₁ (iha hθ arg) (ihb (hθ.up _) body)
  | unit => cases h; exact .unit
  | pair a b iha ihb =>
      cases h with | pair left right => exact .pair (iha hθ left) (ihb hθ right)
  | let₂ a b iha ihb =>
      cases h with
      | let₂ arg body => exact .let₂ (iha hθ arg) (ihb ((hθ.up _).up _) body)
  | inl a ih => cases h with | inl arg => exact .inl (ih hθ arg)
  | inr a ih => cases h with | inr arg => exact .inr (ih hθ arg)
  | case e l r ihe ihl ihr =>
      cases h with
      | case_inl arg branch => exact .case_inl (ihe hθ arg) (ihl (hθ.up _) branch)
      | case_inr arg branch => exact .case_inr (ihe hθ arg) (ihr (hθ.up _) branch)
  | abort a _ => cases h
  | iter init body ihInit ihBody =>
      cases h with
      | iter arg loop =>
          exact .iter (ihInit hθ arg)
            (loop.map_body (fun hb => ihBody (hθ.up _) hb))

/-- **Semantic substitution for evaluation.** A substitution of values may be
performed syntactically or semantically with the same observable outcome. -/
theorem Eval.bsubst_iff {n m : Nat} {values : BoundEnv α n} {bound : BoundEnv α m}
    {θ : Fin n → Tm ν Φ m} {t : Tm ν Φ n} {s s' : σ} {value : Value α}
    (hθ : PureSubst instr free bound θ values) :
    Eval instr free bound (t.bsubst θ) s value s' ↔ Eval instr free values t s value s' :=
  ⟨Eval.of_bsubst hθ, fun h => h.bsubst hθ⟩

/-- Iterations reflect along a substitution of values. -/
theorem Loop.of_bsubst {n m : Nat} {values : BoundEnv α n} {bound : BoundEnv α m}
    {θ : Fin n → Tm ν Φ m} {body : Tm ν Φ (n + 1)} {current value : Value α} {s s' : σ}
    (hθ : PureSubst instr free bound θ values)
    (h : Loop instr free bound (body.bsubst (Tm.upSub θ)) current s value s') :
    Loop instr free values body current s value s' :=
  h.map_body (fun hb => Eval.of_bsubst (hθ.up _) hb)

/-! ## Faults -/

/-- If no component of a substitution faults, none of the components of its
lifting under a binder faults either. -/
theorem upSub_not_fault {n m : Nat} {bound : BoundEnv α m} {θ : Fin n → Tm ν Φ m}
    {value : Value α}
    (h : ∀ (i : Fin n) {s₀ s₁ : σ}, ¬ Fault instr faults free bound (θ i) s₀ s₁) :
    ∀ (i : Fin (n + 1)) {s₀ s₁ : σ},
      ¬ Fault instr faults free (extend bound value) (Tm.upSub θ i) s₀ s₁ := by
  intro i s₀ s₁ hf
  induction i using Fin.cases with
  | zero => cases hf
  | succ j =>
      simp only [Tm.upSub, Fin.cases_succ, Tm.lift] at hf
      exact h j ((Fault.rename_iff (bound := bound) (ρ := Fin.succ) (t := θ j)
        (fun _ => rfl)).mp hf)

/-- If no component of a substitution diverges, none of the components of its
lifting under a binder diverges either. -/
theorem upSub_not_diverges {n m : Nat} {bound : BoundEnv α m} {θ : Fin n → Tm ν Φ m}
    {value : Value α}
    (h : ∀ (i : Fin n) {s₀ : σ},
      ¬ External.Diverges instr free prim (.term bound (θ i) s₀)) :
    ∀ (i : Fin (n + 1)) {s₀ : σ},
      ¬ External.Diverges instr free prim (.term (extend bound value) (Tm.upSub θ i) s₀) := by
  intro i s₀ hd
  induction i using Fin.cases with
  | zero => cases hd.unfold with | core c => cases c
  | succ j =>
      simp only [Tm.upSub, Fin.cases_succ, Tm.lift] at hd
      exact h j ((External.Diverges.rename_iff (bound := bound) (ρ := Fin.succ) (t := θ j)
        (fun _ => rfl)).mp hd)

/-- A fault of the term becomes a fault of its substitution instance. -/
theorem Fault.bsubst {n : Nat} {values : BoundEnv α n} {t : Tm ν Φ n} {s s' : σ}
    (h : Fault instr faults free values t s s') :
    ∀ {m : Nat} {bound : BoundEnv α m} {θ : Fin n → Tm ν Φ m},
      PureSubst instr free bound θ values →
      Fault instr faults free bound (t.bsubst θ) s s' := by
  induction h using Fault.rec
      (motive_2 := fun {n} values body current s s' _ =>
        ∀ {m : Nat} {bound : BoundEnv α m} {θ : Fin n → Tm ν Φ m},
          PureSubst instr free bound θ values →
          LoopFault instr faults free bound (body.bsubst (Tm.upSub θ)) current s s') with
  | op_arg _ ih => intro _ _ _ hθ; exact .op_arg (ih hθ)
  | op_fault arg fault => intro _ _ _ hθ; exact .op_fault (arg.bsubst hθ) fault
  | let₁_arg _ ih => intro _ _ _ hθ; exact .let₁_arg (ih hθ)
  | let₁_body arg _ ih => intro _ _ _ hθ; exact .let₁_body (arg.bsubst hθ) (ih (hθ.up _))
  | pair_left _ ih => intro _ _ _ hθ; exact .pair_left (ih hθ)
  | pair_right arg _ ih => intro _ _ _ hθ; exact .pair_right (arg.bsubst hθ) (ih hθ)
  | let₂_arg _ ih => intro _ _ _ hθ; exact .let₂_arg (ih hθ)
  | let₂_body arg _ ih =>
      intro _ _ _ hθ; exact .let₂_body (arg.bsubst hθ) (ih ((hθ.up _).up _))
  | inl _ ih => intro _ _ _ hθ; exact .inl (ih hθ)
  | inr _ ih => intro _ _ _ hθ; exact .inr (ih hθ)
  | case_arg _ ih => intro _ _ _ hθ; exact .case_arg (ih hθ)
  | case_inl arg _ ih => intro _ _ _ hθ; exact .case_inl (arg.bsubst hθ) (ih (hθ.up _))
  | case_inr arg _ ih => intro _ _ _ hθ; exact .case_inr (arg.bsubst hθ) (ih (hθ.up _))
  | abort_arg _ ih => intro _ _ _ hθ; exact .abort_arg (ih hθ)
  | iter_init _ ih => intro _ _ _ hθ; exact .iter_init (ih hθ)
  | iter_loop arg _ ih => intro _ _ _ hθ; exact .iter_loop (arg.bsubst hθ) (ih hθ)
  | body _ ih => rename_i _ _ _ hθ; exact .body (ih (hθ.up _))
  | step head _ ih => rename_i _ _ _ hθ; exact .step (head.bsubst (hθ.up _)) (ih hθ)

/-- A fault of a substitution instance comes from the term, provided no
component of the substitution can itself fault. -/
theorem Fault.of_bsubst {n m : Nat} {values : BoundEnv α n} {bound : BoundEnv α m}
    {θ : Fin n → Tm ν Φ m} {t : Tm ν Φ n} {s s' : σ}
    (hθ : PureSubst instr free bound θ values)
    (hfault : ∀ (i : Fin n) {s₀ s₁ : σ}, ¬ Fault instr faults free bound (θ i) s₀ s₁)
    (h : Fault instr faults free bound (t.bsubst θ) s s') :
    Fault instr faults free values t s s' := by
  induction t generalizing m s s' with
  | fv x => cases h
  | bv i => exact absurd h (hfault i)
  | unit => cases h
  | op f a ih =>
      cases h with
      | op_arg arg => exact .op_arg (ih hθ hfault arg)
      | op_fault arg fault => exact .op_fault (arg.of_bsubst hθ) fault
  | let₁ a b iha ihb =>
      cases h with
      | let₁_arg arg => exact .let₁_arg (iha hθ hfault arg)
      | let₁_body arg body =>
          exact .let₁_body (arg.of_bsubst hθ) (ihb (hθ.up _) (upSub_not_fault hfault) body)
  | pair a b iha ihb =>
      cases h with
      | pair_left left => exact .pair_left (iha hθ hfault left)
      | pair_right left right => exact .pair_right (left.of_bsubst hθ) (ihb hθ hfault right)
  | let₂ a b iha ihb =>
      cases h with
      | let₂_arg arg => exact .let₂_arg (iha hθ hfault arg)
      | let₂_body arg body =>
          exact .let₂_body (arg.of_bsubst hθ)
            (ihb ((hθ.up _).up _) (upSub_not_fault (upSub_not_fault hfault)) body)
  | inl a ih => cases h with | inl arg => exact .inl (ih hθ hfault arg)
  | inr a ih => cases h with | inr arg => exact .inr (ih hθ hfault arg)
  | case e l r ihe ihl ihr =>
      cases h with
      | case_arg arg => exact .case_arg (ihe hθ hfault arg)
      | case_inl arg branch =>
          exact .case_inl (arg.of_bsubst hθ) (ihl (hθ.up _) (upSub_not_fault hfault) branch)
      | case_inr arg branch =>
          exact .case_inr (arg.of_bsubst hθ) (ihr (hθ.up _) (upSub_not_fault hfault) branch)
  | abort a ih => cases h with | abort_arg arg => exact .abort_arg (ih hθ hfault arg)
  | iter init body ihInit ihBody =>
      cases h with
      | iter_init arg => exact .iter_init (ihInit hθ hfault arg)
      | iter_loop arg loop =>
          exact .iter_loop (arg.of_bsubst hθ)
            (loop.map_body (fun hb => Eval.of_bsubst (hθ.up _) hb)
              (fun hb => ihBody (hθ.up _) (upSub_not_fault hfault) hb))

/-- **Semantic substitution for faults.** -/
theorem Fault.bsubst_iff {n m : Nat} {values : BoundEnv α n} {bound : BoundEnv α m}
    {θ : Fin n → Tm ν Φ m} {t : Tm ν Φ n} {s s' : σ}
    (hθ : PureSubst instr free bound θ values)
    (hfault : ∀ (i : Fin n) {s₀ s₁ : σ}, ¬ Fault instr faults free bound (θ i) s₀ s₁) :
    Fault instr faults free bound (t.bsubst θ) s s' ↔ Fault instr faults free values t s s' :=
  ⟨Fault.of_bsubst hθ hfault, fun h => h.bsubst hθ⟩

/-! ## Divergence -/

/-- **Semantic substitution for divergence.** An infinite execution of a
substitution instance is an infinite execution of the term in the environment
of values, and conversely, provided no component of the substitution can itself
run forever. -/
theorem External.Diverges.bsubst_iff {n m : Nat} {values : BoundEnv α n}
    {bound : BoundEnv α m} {θ : Fin n → Tm ν Φ m} {t : Tm ν Φ n} {s : σ}
    (hθ : PureSubst instr free bound θ values)
    (hdiv : ∀ (i : Fin n) {s₀ : σ},
      ¬ External.Diverges instr free prim (.term bound (θ i) s₀)) :
    External.Diverges instr free prim (.term bound (t.bsubst θ) s) ↔
      External.Diverges instr free prim (.term values t s) := by
  induction t generalizing m s with
  | fv | unit => constructor <;> intro h <;> cases h.unfold with | core h => cases h
  | bv i =>
      constructor
      · intro h; exact absurd h (hdiv i)
      · intro h; cases h.unfold with | core h => cases h
  | op f a ih =>
      constructor
      · intro h
        cases h.unfold with
        | core h => cases h with | op arg => exact .fold_core (.op ((ih hθ hdiv).mp arg))
        | primitive arg div => exact .primitive (arg.of_bsubst hθ) div
      · intro h
        cases h.unfold with
        | core h => cases h with | op arg => exact .fold_core (.op ((ih hθ hdiv).mpr arg))
        | primitive arg div => exact .primitive (arg.bsubst hθ) div
  | let₁ a b iha ihb =>
      constructor
      · intro h
        cases h.unfold with | core h => cases h with
        | let₁_arg arg => exact .fold_core (.let₁_arg ((iha hθ hdiv).mp arg))
        | let₁_body arg body =>
            exact .fold_core (.let₁_body (arg.of_bsubst hθ)
              ((ihb (hθ.up _) (upSub_not_diverges hdiv)).mp body))
      · intro h
        cases h.unfold with | core h => cases h with
        | let₁_arg arg => exact .fold_core (.let₁_arg ((iha hθ hdiv).mpr arg))
        | let₁_body arg body =>
            exact .fold_core (.let₁_body (arg.bsubst hθ)
              ((ihb (hθ.up _) (upSub_not_diverges hdiv)).mpr body))
  | pair a b iha ihb =>
      constructor
      · intro h
        cases h.unfold with | core h => cases h with
        | pair_left left => exact .fold_core (.pair_left ((iha hθ hdiv).mp left))
        | pair_right left right =>
            exact .fold_core (.pair_right (left.of_bsubst hθ) ((ihb hθ hdiv).mp right))
      · intro h
        cases h.unfold with | core h => cases h with
        | pair_left left => exact .fold_core (.pair_left ((iha hθ hdiv).mpr left))
        | pair_right left right =>
            exact .fold_core (.pair_right (left.bsubst hθ) ((ihb hθ hdiv).mpr right))
  | let₂ a b iha ihb =>
      constructor
      · intro h
        cases h.unfold with | core h => cases h with
        | let₂_arg arg => exact .fold_core (.let₂_arg ((iha hθ hdiv).mp arg))
        | let₂_body arg body =>
            exact .fold_core (.let₂_body (arg.of_bsubst hθ)
              ((ihb ((hθ.up _).up _)
                (upSub_not_diverges (upSub_not_diverges hdiv))).mp body))
      · intro h
        cases h.unfold with | core h => cases h with
        | let₂_arg arg => exact .fold_core (.let₂_arg ((iha hθ hdiv).mpr arg))
        | let₂_body arg body =>
            exact .fold_core (.let₂_body (arg.bsubst hθ)
              ((ihb ((hθ.up _).up _)
                (upSub_not_diverges (upSub_not_diverges hdiv))).mpr body))
  | inl a ih =>
      constructor
      · intro h
        cases h.unfold with | core h => cases h with
          | inl arg => exact .fold_core (.inl ((ih hθ hdiv).mp arg))
      · intro h
        cases h.unfold with | core h => cases h with
          | inl arg => exact .fold_core (.inl ((ih hθ hdiv).mpr arg))
  | inr a ih =>
      constructor
      · intro h
        cases h.unfold with | core h => cases h with
          | inr arg => exact .fold_core (.inr ((ih hθ hdiv).mp arg))
      · intro h
        cases h.unfold with | core h => cases h with
          | inr arg => exact .fold_core (.inr ((ih hθ hdiv).mpr arg))
  | case e l r ihe ihl ihr =>
      constructor
      · intro h
        cases h.unfold with | core h => cases h with
        | case_scrutinee arg => exact .fold_core (.case_scrutinee ((ihe hθ hdiv).mp arg))
        | case_inl arg branch =>
            exact .fold_core (.case_inl (arg.of_bsubst hθ)
              ((ihl (hθ.up _) (upSub_not_diverges hdiv)).mp branch))
        | case_inr arg branch =>
            exact .fold_core (.case_inr (arg.of_bsubst hθ)
              ((ihr (hθ.up _) (upSub_not_diverges hdiv)).mp branch))
      · intro h
        cases h.unfold with | core h => cases h with
        | case_scrutinee arg => exact .fold_core (.case_scrutinee ((ihe hθ hdiv).mpr arg))
        | case_inl arg branch =>
            exact .fold_core (.case_inl (arg.bsubst hθ)
              ((ihl (hθ.up _) (upSub_not_diverges hdiv)).mpr branch))
        | case_inr arg branch =>
            exact .fold_core (.case_inr (arg.bsubst hθ)
              ((ihr (hθ.up _) (upSub_not_diverges hdiv)).mpr branch))
  | abort a ih =>
      constructor
      · intro h
        cases h.unfold with | core h => cases h with
          | abort arg => exact .fold_core (.abort ((ih hθ hdiv).mp arg))
      · intro h
        cases h.unfold with | core h => cases h with
          | abort arg => exact .fold_core (.abort ((ih hθ hdiv).mpr arg))
  | iter a b iha ihb =>
      constructor
      · intro h
        cases h.unfold with | core h => cases h with
        | iter_init arg => exact .fold_core (.iter_init ((iha hθ hdiv).mp arg))
        | iter_loop arg loop =>
            exact .fold_core (.iter_loop (arg.of_bsubst hθ)
              (loop.map_loop_body (fun hb => Eval.of_bsubst (hθ.up _) hb)
                (fun hb => (ihb (hθ.up _) (upSub_not_diverges hdiv)).mp hb)))
      · intro h
        cases h.unfold with | core h => cases h with
        | iter_init arg => exact .fold_core (.iter_init ((iha hθ hdiv).mpr arg))
        | iter_loop arg loop =>
            exact .fold_core (.iter_loop (arg.bsubst hθ)
              (loop.map_loop_body (fun hb => Eval.bsubst hb (hθ.up _))
                (fun hb => (ihb (hθ.up _) (upSub_not_diverges hdiv)).mpr hb)))

/-! ## Inert terms

The hypotheses of the substitution lemmas are semantic, and no purity contract
on the instruction relation can discharge them in general: the fault oracle and
the primitive-divergence oracle are parameters independent of `instr`, so an
opcode declared pure may still be declared faulting or divergent. The terms
that satisfy the hypotheses in *every* model are exactly those with no
instruction application and no elimination form. -/

/-- Terms that denote a value immediately: variables, unit, pairs and
injections. An inert term applies no instruction and eliminates nothing, so no
instruction relation, fault oracle or primitive-divergence oracle can make it
move the machine state, fail, get stuck or run forever. -/
inductive Inert : {n : Nat} → Tm ν Φ n → Prop where
  /-- A free variable is inert. -/
  | fv {n : Nat} (x : ν) : Inert (.fv (n := n) x)
  /-- A bound variable is inert. -/
  | bv {n : Nat} (i : Fin n) : Inert (.bv i)
  /-- The unit value is inert. -/
  | unit {n : Nat} : Inert (.unit (n := n))
  /-- A pair of inert terms is inert. -/
  | pair {n : Nat} {a b : Tm ν Φ n} : Inert a → Inert b → Inert (.pair a b)
  /-- A left injection of an inert term is inert. -/
  | inl {n : Nat} {a : Tm ν Φ n} : Inert a → Inert (.inl a)
  /-- A right injection of an inert term is inert. -/
  | inr {n : Nat} {a : Tm ν Φ n} : Inert a → Inert (.inr a)

/-- The value an inert term denotes. The clauses for the non-inert formers are
never used. -/
def inertValue (free : FreeEnv ν α) : {n : Nat} → BoundEnv α n → Tm ν Φ n → Value α
  | _, _, .fv x => free x
  | _, bound, .bv i => bound i
  | _, _, .unit => .unit
  | _, bound, .pair a b => .pair (inertValue free bound a) (inertValue free bound b)
  | _, bound, .inl a => .inl (inertValue free bound a)
  | _, bound, .inr a => .inr (inertValue free bound a)
  | _, _, .op _ _ => .unit
  | _, _, .let₁ _ _ => .unit
  | _, _, .let₂ _ _ => .unit
  | _, _, .case _ _ _ => .unit
  | _, _, .abort _ => .unit
  | _, _, .iter _ _ => .unit

namespace Inert

/-- Inertness is stable under renaming. -/
theorem rename {n m : Nat} {t : Tm ν Φ n} (h : Inert t) (ρ : Fin n → Fin m) :
    Inert (t.rename ρ) := by
  induction h generalizing m with
  | fv x => exact .fv x
  | bv i => exact .bv _
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha ρ) (ihb ρ)
  | inl _ ih => exact .inl (ih ρ)
  | inr _ ih => exact .inr (ih ρ)

/-- Inertness survives inserting a binder underneath the outermost one. -/
theorem underBinder {n : Nat} {t : Tm ν Φ (n + 1)} (h : Inert t) : Inert t.underBinder :=
  h.rename _

/-- An inert term reaches its value from every machine state, leaving the
state alone. -/
theorem eval {n : Nat} {t : Tm ν Φ n} (h : Inert t) {bound : BoundEnv α n} (s : σ) :
    Eval instr free bound t s (inertValue free bound t) s := by
  induction h with
  | fv x => exact .fv
  | bv i => exact .bv
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

/-- An inert term has that one outcome and no other. -/
theorem unique {n : Nat} {t : Tm ν Φ n} (h : Inert t) {bound : BoundEnv α n}
    {s s' : σ} {value : Value α} (run : Eval instr free bound t s value s') :
    value = inertValue free bound t ∧ s' = s := by
  induction h generalizing s s' value with
  | fv x => cases run; exact ⟨rfl, rfl⟩
  | bv i => cases run; exact ⟨rfl, rfl⟩
  | unit => cases run; exact ⟨rfl, rfl⟩
  | pair _ _ iha ihb =>
      cases run with
      | pair left right =>
          obtain ⟨rfl, rfl⟩ := iha left
          obtain ⟨rfl, rfl⟩ := ihb right
          exact ⟨rfl, rfl⟩
  | inl _ ih => cases run with | inl arg => obtain ⟨rfl, rfl⟩ := ih arg; exact ⟨rfl, rfl⟩
  | inr _ ih => cases run with | inr arg => obtain ⟨rfl, rfl⟩ := ih arg; exact ⟨rfl, rfl⟩

/-- An inert term cannot fault, whatever the fault oracle says. -/
theorem not_fault {n : Nat} {t : Tm ν Φ n} (h : Inert t) {bound : BoundEnv α n} {s s' : σ} :
    ¬ Fault instr faults free bound t s s' := by
  induction h generalizing s s' with
  | fv x | bv i | unit => intro f; cases f
  | pair _ _ iha ihb =>
      intro f
      cases f with
      | pair_left left => exact iha left
      | pair_right _ right => exact ihb right
  | inl _ ih => intro f; cases f with | inl arg => exact ih arg
  | inr _ ih => intro f; cases f with | inr arg => exact ih arg

/-- An inert term cannot run forever, whatever the primitive-divergence
oracle says. -/
theorem not_diverges {n : Nat} {t : Tm ν Φ n} (h : Inert t) {bound : BoundEnv α n} {s : σ} :
    ¬ External.Diverges instr free prim (.term bound t s) := by
  induction h generalizing s with
  | fv x | bv i | unit => intro d; cases d.unfold with | core c => cases c
  | pair _ _ iha ihb =>
      intro d
      cases d.unfold with
      | core c => cases c with
        | pair_left left => exact iha left
        | pair_right _ right => exact ihb right
  | inl _ ih => intro d; cases d.unfold with | core c => cases c with | inl arg => exact ih arg
  | inr _ ih => intro d; cases d.unfold with | core c => cases c with | inr arg => exact ih arg

/-- Opening a binder with an inert term is a substitution of values. -/
theorem pureSubst {n : Nat} {a : Tm ν Φ n} (h : Inert a) {bound : BoundEnv α n} :
    PureSubst instr free bound (Fin.cases a (fun i => .bv i))
      (extend bound (inertValue free bound a)) :=
  PureSubst.instantiate (fun s => h.eval s) (fun run => h.unique run)

end Inert

/-! ## Opening a binder with an inert term -/

/-- **Semantic beta for evaluation.** -/
theorem Eval.instantiate_iff {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n}
    {b : Tm ν Φ (n + 1)} {s s' : σ} {value : Value α} (h : Inert a) :
    Eval instr free bound (b.instantiate a) s value s' ↔
      Eval instr free (extend bound (inertValue free bound a)) b s value s' :=
  Eval.bsubst_iff h.pureSubst

/-- **Semantic beta for faults.** -/
theorem Fault.instantiate_iff {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n}
    {b : Tm ν Φ (n + 1)} {s s' : σ} (h : Inert a) :
    Fault instr faults free bound (b.instantiate a) s s' ↔
      Fault instr faults free (extend bound (inertValue free bound a)) b s s' :=
  Fault.bsubst_iff h.pureSubst
    (fun i => by
      intro s₀ s₁
      induction i using Fin.cases with
      | zero => exact h.not_fault
      | succ j => intro f; cases f)

/-- **Semantic beta for divergence.** -/
theorem External.Diverges.instantiate_iff {n : Nat} {bound : BoundEnv α n} {a : Tm ν Φ n}
    {b : Tm ν Φ (n + 1)} {s : σ} (h : Inert a) :
    External.Diverges instr free prim (.term bound (b.instantiate a) s) ↔
      External.Diverges instr free prim
        (.term (extend bound (inertValue free bound a)) b s) :=
  External.Diverges.bsubst_iff h.pureSubst
    (fun i => by
      intro s₀
      induction i using Fin.cases with
      | zero => exact h.not_diverges
      | succ j => intro d; cases d.unfold with | core c => cases c)

end Silmaril.Isotope.LetIter.Semantics

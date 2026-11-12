module

public import Silmaril.SSA.Isotope.LambdaSSA.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.DivergenceStructural
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.External

/-!
# Renaming reflects lambda-SSA execution

`Tm.Eval.rename`, `Region.Eval.renameVars` and `Region.Eval.renameLabels`
transport an execution along a renaming. This module proves the converse: an
execution of a renamed term or region comes from an execution of the original,
provided the environments agree at every image index. Label renamings are
reflected up to the image of the exit label.

Both directions are needed to turn the existing one-sided simulation theorems
for the lambda-SSA translations into exact correspondences; the administrative
binders introduced by continuation-passing compilation are value renamings, and
the extra label introduced by a control-flow-graph binder is a label renaming.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- An execution of a renamed expression comes from one of the original. -/
theorem Tm.Eval.of_rename {a : LambdaSSA.Tm Φ} {ρ : Nat → Nat} {env env' : Env α}
    {s s' : σ} {value : Value α} (hρ : ∀ i, env' (ρ i) = env i)
    (h : Tm.Eval instr env' (a.rename ρ) s value s') :
    Tm.Eval instr env a s value s' := by
  induction a generalizing ρ env env' s s' value with
  | var i => cases h; exact hρ i ▸ .var
  | op f a ih => cases h with | op arg step => exact .op (ih hρ arg) step
  | let₁ a b iha ihb =>
      cases h with
      | let₁ arg body => exact .let₁ (iha hρ arg) (ihb (extend_rename hρ _) body)
  | pair a b iha ihb =>
      cases h with | pair left right => exact .pair (iha hρ left) (ihb hρ right)
  | unit => cases h; exact .unit
  | let₂ a b iha ihb =>
      cases h with
      | let₂ arg body =>
          exact .let₂ (iha hρ arg) (ihb (extend_rename (extend_rename hρ _) _) body)
  | inl a ih => cases h with | inl arg => exact .inl (ih hρ arg)
  | inr a ih => cases h with | inr arg => exact .inr (ih hρ arg)
  | case e l r ihe ihl ihr =>
      cases h with
      | case_inl arg branch => exact .case_inl (ihe hρ arg) (ihl (extend_rename hρ _) branch)
      | case_inr arg branch => exact .case_inr (ihe hρ arg) (ihr (extend_rename hρ _) branch)
  | abort a _ => cases h

/-- Execution of an expression is invariant under a renaming whose images the
two environments agree on. -/
theorem Tm.Eval.rename_iff {a : LambdaSSA.Tm Φ} {ρ : Nat → Nat} {env env' : Env α}
    {s s' : σ} {value : Value α} (hρ : ∀ i, env' (ρ i) = env i) :
    Tm.Eval instr env' (a.rename ρ) s value s' ↔ Tm.Eval instr env a s value s' :=
  ⟨Tm.Eval.of_rename hρ, fun h => h.rename hρ⟩

/-- Control transfer respects a simulation of each block execution. -/
theorem Region.Follow.map_block {n : Nat} {env env' : Env α}
    {blocks blocks' : Fin n → LambdaSSA.Region Φ}
    (hblock : ∀ (i : Fin n) (current : Value α) {s : σ} {next : Nat} {value : Value α} {s' : σ},
      Region.Eval instr (extend env' current) (blocks' i) s next value s' →
      Region.Eval instr (extend env current) (blocks i) s next value s')
    {first : Nat} {current : Value α} {s : σ} {label : Nat} {value : Value α} {s' : σ}
    (h : Region.Follow instr env' blocks' first current s label value s') :
    Region.Follow instr env blocks first current s label value s' := by
  induction h using Region.Follow.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside => exact .exit outside
  | step inside head _ _ ih => exact .step inside (hblock _ _ head) (ih hblock)
  | _ => trivial

/-- An execution of a value-renamed region comes from one of the original. -/
theorem Region.Eval.of_renameVars {r : LambdaSSA.Region Φ} {ρ : Nat → Nat} {env env' : Env α}
    {s s' : σ} {label : Nat} {value : Value α} (hρ : ∀ i, env' (ρ i) = env i)
    (h : Region.Eval instr env' (r.renameVars ρ) s label value s') :
    Region.Eval instr env r s label value s' := by
  induction r generalizing ρ env env' s s' label value with
  | br ℓ a => cases h with | br arg => exact .br (Tm.Eval.of_rename hρ arg)
  | case a l r ihl ihr =>
      cases h with
      | case_inl arg branch =>
          exact .case_inl (Tm.Eval.of_rename hρ arg) (ihl (extend_rename hρ _) branch)
      | case_inr arg branch =>
          exact .case_inr (Tm.Eval.of_rename hρ arg) (ihr (extend_rename hρ _) branch)
  | let₁ a b ih =>
      cases h with
      | let₁ arg body => exact .let₁ (Tm.Eval.of_rename hρ arg) (ih (extend_rename hρ _) body)
  | let₂ a b ih =>
      cases h with
      | let₂ arg body =>
          exact .let₂ (Tm.Eval.of_rename hρ arg)
            (ih (extend_rename (extend_rename hρ _) _) body)
  | cfg entry count blocks ihe ihb =>
      cases h with
      | cfg entryRun follow =>
          exact .cfg (ihe hρ entryRun)
            (follow.map_block
              (fun i current {_s _next _value _s'} run => ihb i (extend_rename hρ _) run))

/-- Execution of a region is invariant under a value renaming whose images the
two environments agree on. -/
theorem Region.Eval.renameVars_iff {r : LambdaSSA.Region Φ} {ρ : Nat → Nat} {env env' : Env α}
    {s s' : σ} {label : Nat} {value : Value α} (hρ : ∀ i, env' (ρ i) = env i) :
    Region.Eval instr env' (r.renameVars ρ) s label value s' ↔
      Region.Eval instr env r s label value s' :=
  ⟨Region.Eval.of_renameVars hρ, fun h => h.renameVars hρ⟩

/-- A label renaming lifted through a control-flow-graph binder keeps internal
labels fixed, so a renamed control transfer comes from an original one. -/
theorem Region.Follow.of_renameLabels {n : Nat} {env : Env α}
    {blocks blocks' : Fin n → LambdaSSA.Region Φ} {ρ : Nat → Nat}
    {first' : Nat} {current : Value α} {s : σ} {label : Nat} {value : Value α} {s' : σ}
    (hblock : ∀ (i : Fin n) (cur : Value α) {s : σ} {next : Nat} {v : Value α} {s' : σ},
      Region.Eval instr (extend env cur) (blocks' i) s next v s' →
      ∃ ℓ, next = Silmaril.DeBruijn.liftN n ρ ℓ ∧ Region.Eval instr (extend env cur) (blocks i) s ℓ v s')
    (h : Region.Follow instr env blocks' first' current s label value s') :
    ∀ first, first' = Silmaril.DeBruijn.liftN n ρ first →
      ∃ ℓ, label = ρ ℓ ∧ Region.Follow instr env blocks first current s ℓ value s' := by
  induction h using Region.Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | @exit env n first' blocks' value s outside =>
      intro first hfirst
      have hge : n ≤ first := by
        by_contra hlt
        rw [hfirst, Silmaril.DeBruijn.liftN_lt ρ (Nat.lt_of_not_le hlt)] at outside
        omega
      refine ⟨first - n, ?_, .exit hge⟩
      rw [hfirst, Silmaril.DeBruijn.liftN_ge ρ hge, Nat.add_sub_cancel_left]
  | @step env n first' next out blocks' current middle value s s₁ s₂ inside head _ _ ih =>
      intro first hfirst
      have hlt : first < n := by
        by_contra hge
        rw [hfirst, Silmaril.DeBruijn.liftN_ge ρ (Nat.le_of_not_lt hge)] at inside
        omega
      have hfirst' : first' = first := by rw [hfirst, Silmaril.DeBruijn.liftN_lt ρ hlt]
      subst hfirst'
      obtain ⟨m, hm, run⟩ := hblock ⟨first', inside⟩ current head
      obtain ⟨ℓ, hℓ, tail⟩ := ih hblock m hm
      exact ⟨ℓ, hℓ, .step hlt (by simpa using run) tail⟩
  | _ => trivial

/-- An execution of a label-renamed region comes from one of the original,
exiting at a label whose image is the observed one. -/
theorem Region.Eval.of_renameLabels {r : LambdaSSA.Region Φ} {ρ : Nat → Nat} {env : Env α}
    {s s' : σ} {label : Nat} {value : Value α}
    (h : Region.Eval instr env (r.renameLabels ρ) s label value s') :
    ∃ ℓ, label = ρ ℓ ∧ Region.Eval instr env r s ℓ value s' := by
  induction r generalizing ρ env s s' label value with
  | br ℓ a => cases h with | br arg => exact ⟨ℓ, rfl, .br arg⟩
  | case a l r ihl ihr =>
      cases h with
      | case_inl arg branch =>
          obtain ⟨ℓ, hℓ, run⟩ := ihl branch
          exact ⟨ℓ, hℓ, .case_inl arg run⟩
      | case_inr arg branch =>
          obtain ⟨ℓ, hℓ, run⟩ := ihr branch
          exact ⟨ℓ, hℓ, .case_inr arg run⟩
  | let₁ a b ih =>
      cases h with
      | let₁ arg body =>
          obtain ⟨ℓ, hℓ, run⟩ := ih body
          exact ⟨ℓ, hℓ, .let₁ arg run⟩
  | let₂ a b ih =>
      cases h with
      | let₂ arg body =>
          obtain ⟨ℓ, hℓ, run⟩ := ih body
          exact ⟨ℓ, hℓ, .let₂ arg run⟩
  | cfg entry count blocks ihe ihb =>
      cases h with
      | cfg entryRun follow =>
          obtain ⟨f, hf, run⟩ := ihe entryRun
          obtain ⟨ℓ, hℓ, tail⟩ :=
            Region.Follow.of_renameLabels
              (blocks := blocks) (ρ := ρ)
              (fun i cur {_s _next _v _s'} h => ihb i h) follow f hf
          exact ⟨ℓ, hℓ, .cfg run tail⟩

/-! ## Faults -/

variable {faults : Φ → Value α → σ → σ → Prop}

/-- A faulting expression stays faulting under renaming. -/
theorem Tm.Fault.rename {a : LambdaSSA.Tm Φ} {ρ : Nat → Nat} {env env' : Env α} {s s' : σ}
    (h : Tm.Fault instr faults env a s s') (hρ : ∀ i, env' (ρ i) = env i) :
    Tm.Fault instr faults env' (a.rename ρ) s s' := by
  induction h generalizing env' ρ with
  | op_arg _ ih => exact .op_arg (ih hρ)
  | op_fault arg fault => exact .op_fault (arg.rename hρ) fault
  | let₁_arg _ ih => exact .let₁_arg (ih hρ)
  | let₁_body arg _ ih => exact .let₁_body (arg.rename hρ) (ih (extend_rename hρ _))
  | pair_left _ ih => exact .pair_left (ih hρ)
  | pair_right left _ ih => exact .pair_right (left.rename hρ) (ih hρ)
  | let₂_arg _ ih => exact .let₂_arg (ih hρ)
  | let₂_body arg _ ih =>
      exact .let₂_body (arg.rename hρ) (ih (extend_rename (extend_rename hρ _) _))
  | inl _ ih => exact .inl (ih hρ)
  | inr _ ih => exact .inr (ih hρ)
  | case_arg _ ih => exact .case_arg (ih hρ)
  | case_inl arg _ ih => exact .case_inl (arg.rename hρ) (ih (extend_rename hρ _))
  | case_inr arg _ ih => exact .case_inr (arg.rename hρ) (ih (extend_rename hρ _))
  | abort_arg _ ih => exact .abort_arg (ih hρ)

/-- A fault of a renamed expression comes from a fault of the original. -/
theorem Tm.Fault.of_rename {a : LambdaSSA.Tm Φ} {ρ : Nat → Nat} {env env' : Env α}
    {s s' : σ} (hρ : ∀ i, env' (ρ i) = env i)
    (h : Tm.Fault instr faults env' (a.rename ρ) s s') :
    Tm.Fault instr faults env a s s' := by
  induction a generalizing ρ env env' s s' with
  | var i => cases h
  | op f a ih =>
      cases h with
      | op_arg arg => exact .op_arg (ih hρ arg)
      | op_fault arg fault => exact .op_fault (Tm.Eval.of_rename hρ arg) fault
  | let₁ a b iha ihb =>
      cases h with
      | let₁_arg arg => exact .let₁_arg (iha hρ arg)
      | let₁_body arg body =>
          exact .let₁_body (Tm.Eval.of_rename hρ arg) (ihb (extend_rename hρ _) body)
  | pair a b iha ihb =>
      cases h with
      | pair_left left => exact .pair_left (iha hρ left)
      | pair_right left right => exact .pair_right (Tm.Eval.of_rename hρ left) (ihb hρ right)
  | unit => cases h
  | let₂ a b iha ihb =>
      cases h with
      | let₂_arg arg => exact .let₂_arg (iha hρ arg)
      | let₂_body arg body =>
          exact .let₂_body (Tm.Eval.of_rename hρ arg)
            (ihb (extend_rename (extend_rename hρ _) _) body)
  | inl a ih => cases h with | inl arg => exact .inl (ih hρ arg)
  | inr a ih => cases h with | inr arg => exact .inr (ih hρ arg)
  | case e l r ihe ihl ihr =>
      cases h with
      | case_arg arg => exact .case_arg (ihe hρ arg)
      | case_inl arg branch =>
          exact .case_inl (Tm.Eval.of_rename hρ arg) (ihl (extend_rename hρ _) branch)
      | case_inr arg branch =>
          exact .case_inr (Tm.Eval.of_rename hρ arg) (ihr (extend_rename hρ _) branch)
  | abort a ih => cases h with | abort_arg arg => exact .abort_arg (ih hρ arg)

/-- A faulting control transfer respects a simulation of each block. -/
theorem Region.FollowFault.map_block {n : Nat} {env env' : Env α}
    {blocks blocks' : Fin n → LambdaSSA.Region Φ}
    (hrun : ∀ (i : Fin n) (cur : Value α) {s : σ} {next : Nat} {v : Value α} {s' : σ},
      Region.Eval instr (extend env' cur) (blocks' i) s next v s' →
      Region.Eval instr (extend env cur) (blocks i) s next v s')
    (hfault : ∀ (i : Fin n) (cur : Value α) {s s' : σ},
      Region.Fault instr faults (extend env' cur) (blocks' i) s s' →
      Region.Fault instr faults (extend env cur) (blocks i) s s')
    {label : Nat} {arg : Value α} {s s' : σ}
    (h : Region.FollowFault instr faults env' blocks' label arg s s') :
    Region.FollowFault instr faults env blocks label arg s s' := by
  induction h using Region.FollowFault.rec (motive_1 := fun _ _ _ _ _ => True) with
  | body inside fault _ => exact .body inside (hfault _ _ fault)
  | step inside run _ ih => exact .step inside (hrun _ _ run) (ih hrun hfault)
  | _ => trivial

/-- A fault of a region stays a fault under a value renaming. -/
theorem Region.Fault.renameVars {r : LambdaSSA.Region Φ} {env : Env α} {s s' : σ}
    (h : Region.Fault instr faults env r s s') {env' : Env α} {ρ : Nat → Nat}
    (hρ : ∀ i, env' (ρ i) = env i) :
    Region.Fault instr faults env' (r.renameVars ρ) s s' := by
  induction h using Region.Fault.rec
      (motive_2 := fun env n blocks label arg s s' _ =>
        ∀ {env' : Env α} {ρ : Nat → Nat}, (∀ i, env' (ρ i) = env i) →
          Region.FollowFault instr faults env'
            (fun i => (blocks i).renameVars (Silmaril.DeBruijn.lift ρ)) label arg s s')
      generalizing env' ρ with
  | br arg => exact .br (arg.rename hρ)
  | let₁_arg arg => exact .let₁_arg (arg.rename hρ)
  | let₁_body arg _ ih => exact .let₁_body (arg.rename hρ) (ih (extend_rename hρ _))
  | let₂_arg arg => exact .let₂_arg (arg.rename hρ)
  | let₂_body arg _ ih =>
      exact .let₂_body (arg.rename hρ) (ih (extend_rename (extend_rename hρ _) _))
  | case_arg arg => exact .case_arg (arg.rename hρ)
  | case_inl arg _ ih => exact .case_inl (arg.rename hρ) (ih (extend_rename hρ _))
  | case_inr arg _ ih => exact .case_inr (arg.rename hρ) (ih (extend_rename hρ _))
  | cfg_entry _ ih => exact .cfg_entry (ih hρ)
  | cfg_follow run _ ih => exact .cfg_follow (run.renameVars hρ) (ih hρ)
  | body inside _ ih =>
      rename_i env' ρ hρ
      exact .body inside (ih (extend_rename hρ _))
  | step inside run _ ih =>
      rename_i env' ρ hρ
      exact .step inside (run.renameVars (extend_rename hρ _)) (ih hρ)

/-- A fault of a region stays a fault under a label renaming. -/
theorem Region.Fault.renameLabels {r : LambdaSSA.Region Φ} {env : Env α} {s s' : σ}
    (h : Region.Fault instr faults env r s s') (ρ : Nat → Nat) :
    Region.Fault instr faults env (r.renameLabels ρ) s s' := by
  induction h using Region.Fault.rec
      (motive_2 := fun env n blocks label arg s s' _ =>
        ∀ ρ, Region.FollowFault instr faults env
          (fun i => (blocks i).renameLabels (Silmaril.DeBruijn.liftN n ρ))
          (Silmaril.DeBruijn.liftN n ρ label) arg s s')
      generalizing ρ with
  | br arg => exact .br arg
  | let₁_arg arg => exact .let₁_arg arg
  | let₁_body arg _ ih => exact .let₁_body arg (ih ρ)
  | let₂_arg arg => exact .let₂_arg arg
  | let₂_body arg _ ih => exact .let₂_body arg (ih ρ)
  | case_arg arg => exact .case_arg arg
  | case_inl arg _ ih => exact .case_inl arg (ih ρ)
  | case_inr arg _ ih => exact .case_inr arg (ih ρ)
  | cfg_entry _ ih => exact .cfg_entry (ih (Silmaril.DeBruijn.liftN _ ρ))
  | cfg_follow run _ ih =>
      exact .cfg_follow (run.renameLabels (Silmaril.DeBruijn.liftN _ ρ)) (ih ρ)
  | body inside _ ih =>
      rename_i ρ
      rw [Silmaril.DeBruijn.liftN_lt ρ inside]
      exact .body inside (ih (Silmaril.DeBruijn.liftN _ ρ))
  | step inside run _ ih =>
      rename_i ρ
      rw [Silmaril.DeBruijn.liftN_lt ρ inside]
      exact .step inside (run.renameLabels (Silmaril.DeBruijn.liftN _ ρ)) (ih ρ)

/-- A fault of a value-renamed region comes from a fault of the original. -/
theorem Region.Fault.of_renameVars {r : LambdaSSA.Region Φ} {ρ : Nat → Nat} {env env' : Env α}
    {s s' : σ} (hρ : ∀ i, env' (ρ i) = env i)
    (h : Region.Fault instr faults env' (r.renameVars ρ) s s') :
    Region.Fault instr faults env r s s' := by
  induction r generalizing ρ env env' s s' with
  | br ℓ a => cases h with | br arg => exact .br (Tm.Fault.of_rename hρ arg)
  | case a l r ihl ihr =>
      cases h with
      | case_arg arg => exact .case_arg (Tm.Fault.of_rename hρ arg)
      | case_inl arg branch =>
          exact .case_inl (Tm.Eval.of_rename hρ arg) (ihl (extend_rename hρ _) branch)
      | case_inr arg branch =>
          exact .case_inr (Tm.Eval.of_rename hρ arg) (ihr (extend_rename hρ _) branch)
  | let₁ a b ih =>
      cases h with
      | let₁_arg arg => exact .let₁_arg (Tm.Fault.of_rename hρ arg)
      | let₁_body arg body =>
          exact .let₁_body (Tm.Eval.of_rename hρ arg) (ih (extend_rename hρ _) body)
  | let₂ a b ih =>
      cases h with
      | let₂_arg arg => exact .let₂_arg (Tm.Fault.of_rename hρ arg)
      | let₂_body arg body =>
          exact .let₂_body (Tm.Eval.of_rename hρ arg)
            (ih (extend_rename (extend_rename hρ _) _) body)
  | cfg entry count blocks ihe ihb =>
      cases h with
      | cfg_entry fault => exact .cfg_entry (ihe hρ fault)
      | cfg_follow run fault =>
          refine .cfg_follow (Region.Eval.of_renameVars hρ run) (fault.map_block ?_ ?_)
          · exact fun i cur {_s _next _v _s'} h =>
              Region.Eval.of_renameVars (extend_rename hρ _) h
          · exact fun i cur {_s _s'} h => ihb i (extend_rename hρ _) h

/-- A faulting control transfer under a lifted label renaming comes from an
original one. -/
theorem Region.FollowFault.of_renameLabels {n : Nat} {env : Env α}
    {blocks blocks' : Fin n → LambdaSSA.Region Φ} {ρ : Nat → Nat}
    (hrun : ∀ (i : Fin n) (cur : Value α) {s : σ} {next : Nat} {v : Value α} {s' : σ},
      Region.Eval instr (extend env cur) (blocks' i) s next v s' →
      ∃ ℓ, next = Silmaril.DeBruijn.liftN n ρ ℓ ∧ Region.Eval instr (extend env cur) (blocks i) s ℓ v s')
    (hfault : ∀ (i : Fin n) (cur : Value α) {s s' : σ},
      Region.Fault instr faults (extend env cur) (blocks' i) s s' →
      Region.Fault instr faults (extend env cur) (blocks i) s s')
    {label' : Nat} {arg : Value α} {s s' : σ}
    (h : Region.FollowFault instr faults env blocks' label' arg s s') :
    ∀ label, label' = Silmaril.DeBruijn.liftN n ρ label →
      Region.FollowFault instr faults env blocks label arg s s' := by
  induction h using Region.FollowFault.rec (motive_1 := fun _ _ _ _ _ => True) with
  | @body env n label' blocks' arg s s' inside fault _ =>
      intro label hlabel
      have hlt : label < n := by
        by_contra hge
        rw [hlabel, Silmaril.DeBruijn.liftN_ge ρ (Nat.le_of_not_lt hge)] at inside
        omega
      have : label' = label := by rw [hlabel, Silmaril.DeBruijn.liftN_lt ρ hlt]
      subst this
      exact .body hlt (by simpa using hfault ⟨label', inside⟩ arg fault)
  | @step env n label' next blocks' arg value s mid s' inside run _ ih =>
      intro label hlabel
      have hlt : label < n := by
        by_contra hge
        rw [hlabel, Silmaril.DeBruijn.liftN_ge ρ (Nat.le_of_not_lt hge)] at inside
        omega
      have heq : label' = label := by rw [hlabel, Silmaril.DeBruijn.liftN_lt ρ hlt]
      subst heq
      obtain ⟨m, hm, run'⟩ := hrun ⟨label', inside⟩ arg run
      exact .step hlt (by simpa using run') (ih hrun hfault m hm)
  | _ => trivial

/-- A fault of a label-renamed region comes from a fault of the original. -/
theorem Region.Fault.of_renameLabels {r : LambdaSSA.Region Φ} {ρ : Nat → Nat} {env : Env α}
    {s s' : σ} (h : Region.Fault instr faults env (r.renameLabels ρ) s s') :
    Region.Fault instr faults env r s s' := by
  induction r generalizing ρ env s s' with
  | br ℓ a => cases h with | br arg => exact .br arg
  | case a l r ihl ihr =>
      cases h with
      | case_arg arg => exact .case_arg arg
      | case_inl arg branch => exact .case_inl arg (ihl branch)
      | case_inr arg branch => exact .case_inr arg (ihr branch)
  | let₁ a b ih =>
      cases h with
      | let₁_arg arg => exact .let₁_arg arg
      | let₁_body arg body => exact .let₁_body arg (ih body)
  | let₂ a b ih =>
      cases h with
      | let₂_arg arg => exact .let₂_arg arg
      | let₂_body arg body => exact .let₂_body arg (ih body)
  | cfg entry count blocks ihe ihb =>
      cases h with
      | cfg_entry fault => exact .cfg_entry (ihe fault)
      | cfg_follow run fault =>
          obtain ⟨f, hf, run'⟩ := Region.Eval.of_renameLabels run
          refine .cfg_follow run' (Region.FollowFault.of_renameLabels (blocks := blocks)
            (ρ := ρ) ?_ ?_ fault f hf)
          · exact fun i cur {_s _next _v _s'} h => Region.Eval.of_renameLabels h
          · exact fun i cur {_s _s'} h => ihb i h

/-- Faults of a value-renamed region agree with faults of the original. -/
theorem Region.Fault.renameVars_iff {r : LambdaSSA.Region Φ} {ρ : Nat → Nat} {env env' : Env α}
    {s s' : σ} (hρ : ∀ i, env' (ρ i) = env i) :
    Region.Fault instr faults env' (r.renameVars ρ) s s' ↔
      Region.Fault instr faults env r s s' :=
  ⟨Region.Fault.of_renameVars hρ, fun h => h.renameVars hρ⟩

/-- Faults of a label-renamed region agree with faults of the original. -/
theorem Region.Fault.renameLabels_iff {r : LambdaSSA.Region Φ} {env : Env α} {s s' : σ}
    (ρ : Nat → Nat) :
    Region.Fault instr faults env (r.renameLabels ρ) s s' ↔
      Region.Fault instr faults env r s s' :=
  ⟨Region.Fault.of_renameLabels, fun h => h.renameLabels ρ⟩

/-! ## Divergence with explicitly divergent primitives -/

variable {prim : Φ → Value α → σ → Prop}

/-- An externally divergent expression stays divergent under renaming. -/
theorem Tm.ExternalDiverges.rename {a : LambdaSSA.Tm Φ} {env env' : Env α} {s : σ}
    {ρ : Nat → Nat} (h : Tm.ExternalDiverges instr prim env a s)
    (hρ : ∀ i, env' (ρ i) = env i) :
    Tm.ExternalDiverges instr prim env' (a.rename ρ) s := by
  induction h generalizing env' ρ with
  | op_arg _ ih => exact .op_arg (ih hρ)
  | primitive arg div => exact .primitive (arg.rename hρ) div
  | let₁_arg _ ih => exact .let₁_arg (ih hρ)
  | let₁_body arg _ ih => exact .let₁_body (arg.rename hρ) (ih (extend_rename hρ _))
  | pair_left _ ih => exact .pair_left (ih hρ)
  | pair_right left _ ih => exact .pair_right (left.rename hρ) (ih hρ)
  | let₂_arg _ ih => exact .let₂_arg (ih hρ)
  | let₂_body arg _ ih =>
      exact .let₂_body (arg.rename hρ) (ih (extend_rename (extend_rename hρ _) _))
  | inl _ ih => exact .inl (ih hρ)
  | inr _ ih => exact .inr (ih hρ)
  | case_arg _ ih => exact .case_arg (ih hρ)
  | case_inl arg _ ih => exact .case_inl (arg.rename hρ) (ih (extend_rename hρ _))
  | case_inr arg _ ih => exact .case_inr (arg.rename hρ) (ih (extend_rename hρ _))
  | abort_arg _ ih => exact .abort_arg (ih hρ)

/-- External divergence of a renamed expression comes from the original. -/
theorem Tm.ExternalDiverges.of_rename {a : LambdaSSA.Tm Φ} {env env' : Env α} {s : σ}
    {ρ : Nat → Nat} (hρ : ∀ i, env' (ρ i) = env i)
    (h : Tm.ExternalDiverges instr prim env' (a.rename ρ) s) :
    Tm.ExternalDiverges instr prim env a s := by
  induction a generalizing env env' ρ s with
  | var i => cases h
  | op f a ih =>
      cases h with
      | op_arg arg => exact .op_arg (ih hρ arg)
      | primitive arg div => exact .primitive (Tm.Eval.of_rename hρ arg) div
  | let₁ a b iha ihb =>
      cases h with
      | let₁_arg arg => exact .let₁_arg (iha hρ arg)
      | let₁_body arg body =>
          exact .let₁_body (Tm.Eval.of_rename hρ arg) (ihb (extend_rename hρ _) body)
  | pair a b iha ihb =>
      cases h with
      | pair_left left => exact .pair_left (iha hρ left)
      | pair_right left right => exact .pair_right (Tm.Eval.of_rename hρ left) (ihb hρ right)
  | unit => cases h
  | let₂ a b iha ihb =>
      cases h with
      | let₂_arg arg => exact .let₂_arg (iha hρ arg)
      | let₂_body arg body =>
          exact .let₂_body (Tm.Eval.of_rename hρ arg)
            (ihb (extend_rename (extend_rename hρ _) _) body)
  | inl a ih => cases h with | inl arg => exact .inl (ih hρ arg)
  | inr a ih => cases h with | inr arg => exact .inr (ih hρ arg)
  | case e l r ihe ihl ihr =>
      cases h with
      | case_arg arg => exact .case_arg (ihe hρ arg)
      | case_inl arg branch =>
          exact .case_inl (Tm.Eval.of_rename hρ arg) (ihl (extend_rename hρ _) branch)
      | case_inr arg branch =>
          exact .case_inr (Tm.Eval.of_rename hρ arg) (ihr (extend_rename hρ _) branch)
  | abort a ih => cases h with | abort_arg arg => exact .abort_arg (ih hρ arg)

namespace External

/-- Infinite execution, internal or primitive, transports along a value renaming. -/
theorem Diverges.of_varRenaming {c c' : Config α Φ σ}
    (h : Diverges instr prim c) (hr : Config.VarRenaming c c') : Diverges instr prim c' := by
  refine Diverges.coinduct
    (fun d => ∃ e, Diverges instr prim e ∧ Config.VarRenaming e d) ?_ ⟨c, h, hr⟩
  rintro d ⟨e, he, hr⟩
  cases hr with
  | region hρ =>
      cases he.unfold with
      | core core => cases core with
        | let₁ arg rest =>
            exact .core (.let₁ (arg.rename hρ) ⟨_, rest, .region (extend_rename hρ _)⟩)
        | let₂ arg rest =>
            exact .core (.let₂ (arg.rename hρ)
              ⟨_, rest, .region (extend_rename (extend_rename hρ _) _)⟩)
        | case_inl arg rest =>
            exact .core (.case_inl (arg.rename hρ) ⟨_, rest, .region (extend_rename hρ _)⟩)
        | case_inr arg rest =>
            exact .core (.case_inr (arg.rename hρ) ⟨_, rest, .region (extend_rename hρ _)⟩)
        | cfg_entry rest => exact .core (.cfg_entry ⟨_, rest, .region hρ⟩)
        | cfg_follow entry rest =>
            exact .core (.cfg_follow (entry.renameVars hρ) ⟨_, rest, .follow hρ⟩)
      | br div => exact .br (div.rename hρ)
      | let₁_arg div => exact .let₁_arg (div.rename hρ)
      | let₂_arg div => exact .let₂_arg (div.rename hρ)
      | case_arg div => exact .case_arg (div.rename hρ)
  | follow hρ =>
      cases he.unfold with
      | core core => cases core with
        | follow_body inside rest =>
            exact .core (.follow_body inside ⟨_, rest, .region (extend_rename hρ _)⟩)
        | follow_next inside head rest =>
            exact .core (.follow_next inside (head.renameVars (extend_rename hρ _))
              ⟨_, rest, .follow hρ⟩)

/-- Infinite execution of a value-renamed configuration comes from the original. -/
theorem Diverges.of_varRenaming_rev {c c' : Config α Φ σ}
    (hr : Config.VarRenaming c c') (h : Diverges instr prim c') : Diverges instr prim c := by
  refine Diverges.coinduct
    (fun d => ∃ e, Config.VarRenaming d e ∧ Diverges instr prim e) ?_ ⟨c', hr, h⟩
  rintro d ⟨e, hr, he⟩
  cases hr with
  | @region env env' r s ρ hρ =>
      cases r with
      | br ℓ a =>
          cases he.unfold with
          | core core => cases core
          | br div => exact .br (Tm.ExternalDiverges.of_rename hρ div)
      | let₁ a b =>
          cases he.unfold with
          | core core => cases core with
            | let₁ arg rest =>
                exact .core (.let₁ (Tm.Eval.of_rename hρ arg)
                  ⟨_, .region (extend_rename hρ _), rest⟩)
          | let₁_arg div => exact .let₁_arg (Tm.ExternalDiverges.of_rename hρ div)
      | let₂ a b =>
          cases he.unfold with
          | core core => cases core with
            | let₂ arg rest =>
                exact .core (.let₂ (Tm.Eval.of_rename hρ arg)
                  ⟨_, .region (extend_rename (extend_rename hρ _) _), rest⟩)
          | let₂_arg div => exact .let₂_arg (Tm.ExternalDiverges.of_rename hρ div)
      | case a l r =>
          cases he.unfold with
          | core core => cases core with
            | case_inl arg rest =>
                exact .core (.case_inl (Tm.Eval.of_rename hρ arg)
                  ⟨_, .region (extend_rename hρ _), rest⟩)
            | case_inr arg rest =>
                exact .core (.case_inr (Tm.Eval.of_rename hρ arg)
                  ⟨_, .region (extend_rename hρ _), rest⟩)
          | case_arg div => exact .case_arg (Tm.ExternalDiverges.of_rename hρ div)
      | cfg entry count blocks =>
          cases he.unfold with
          | core core => cases core with
            | cfg_entry rest => exact .core (.cfg_entry ⟨_, .region hρ, rest⟩)
            | cfg_follow run rest =>
                exact .core (.cfg_follow (Region.Eval.of_renameVars hρ run)
                  ⟨_, .follow hρ, rest⟩)
  | @follow env env' n blocks label value s ρ hρ =>
      cases he.unfold with
      | core core => cases core with
        | follow_body inside rest =>
            exact .core (.follow_body inside ⟨_, .region (extend_rename hρ _), rest⟩)
        | follow_next inside head rest =>
            exact .core (.follow_next inside
              (Region.Eval.of_renameVars (extend_rename hρ _) head)
              ⟨_, .follow hρ, rest⟩)

/-- Infinite execution of a value-renamed region agrees with the original. -/
theorem Diverges.renameVars_iff {env env' : Env α} {r : LambdaSSA.Region Φ} {s : σ}
    {ρ : Nat → Nat} (hρ : ∀ i, env' (ρ i) = env i) :
    Diverges instr prim (.region env' (r.renameVars ρ) s) ↔
      Diverges instr prim (.region env r s) :=
  ⟨fun h => h.of_varRenaming_rev (.region hρ), fun h => h.of_varRenaming (.region hρ)⟩

/-- Infinite execution, internal or primitive, transports along a label renaming. -/
theorem Diverges.of_labelRenaming {c c' : Config α Φ σ}
    (h : Diverges instr prim c) (hr : Config.LabelRenaming c c') : Diverges instr prim c' := by
  refine Diverges.coinduct
    (fun d => ∃ e, Diverges instr prim e ∧ Config.LabelRenaming e d) ?_ ⟨c, h, hr⟩
  rintro d ⟨e, he, hr⟩
  cases hr with
  | region ρ =>
      cases he.unfold with
      | core core => cases core with
        | let₁ arg rest => exact .core (.let₁ arg ⟨_, rest, .region ρ⟩)
        | let₂ arg rest => exact .core (.let₂ arg ⟨_, rest, .region ρ⟩)
        | case_inl arg rest => exact .core (.case_inl arg ⟨_, rest, .region ρ⟩)
        | case_inr arg rest => exact .core (.case_inr arg ⟨_, rest, .region ρ⟩)
        | cfg_entry rest => exact .core (.cfg_entry ⟨_, rest, .region (Silmaril.DeBruijn.liftN _ ρ)⟩)
        | cfg_follow entry rest =>
            exact .core (.cfg_follow (entry.renameLabels (Silmaril.DeBruijn.liftN _ ρ))
              ⟨_, rest, .follow ρ⟩)
      | br div => exact .br div
      | let₁_arg div => exact .let₁_arg div
      | let₂_arg div => exact .let₂_arg div
      | case_arg div => exact .case_arg div
  | follow ρ =>
      cases he.unfold with
      | core core => cases core with
        | follow_body inside rest =>
            simp only [Silmaril.DeBruijn.liftN_lt ρ inside]
            exact .core (.follow_body inside ⟨_, rest, .region (Silmaril.DeBruijn.liftN _ ρ)⟩)
        | follow_next inside head rest =>
            simp only [Silmaril.DeBruijn.liftN_lt ρ inside]
            exact .core (.follow_next inside (head.renameLabels (Silmaril.DeBruijn.liftN _ ρ))
              ⟨_, rest, .follow ρ⟩)

/-- Infinite execution of a label-renamed configuration comes from the original. -/
theorem Diverges.of_labelRenaming_rev {c c' : Config α Φ σ}
    (hr : Config.LabelRenaming c c') (h : Diverges instr prim c') : Diverges instr prim c := by
  refine Diverges.coinduct
    (fun d => ∃ e, Config.LabelRenaming d e ∧ Diverges instr prim e) ?_ ⟨c', hr, h⟩
  rintro d ⟨e, hr, he⟩
  cases hr with
  | @region env r s ρ =>
      cases r with
      | br ℓ a =>
          cases he.unfold with
          | core core => cases core
          | br div => exact .br div
      | let₁ a b =>
          cases he.unfold with
          | core core => cases core with
            | let₁ arg rest => exact .core (.let₁ arg ⟨_, .region ρ, rest⟩)
          | let₁_arg div => exact .let₁_arg div
      | let₂ a b =>
          cases he.unfold with
          | core core => cases core with
            | let₂ arg rest => exact .core (.let₂ arg ⟨_, .region ρ, rest⟩)
          | let₂_arg div => exact .let₂_arg div
      | case a l r =>
          cases he.unfold with
          | core core => cases core with
            | case_inl arg rest => exact .core (.case_inl arg ⟨_, .region ρ, rest⟩)
            | case_inr arg rest => exact .core (.case_inr arg ⟨_, .region ρ, rest⟩)
          | case_arg div => exact .case_arg div
      | cfg entry count blocks =>
          cases he.unfold with
          | core core => cases core with
            | cfg_entry rest => exact .core (.cfg_entry ⟨_, .region (Silmaril.DeBruijn.liftN _ ρ), rest⟩)
            | cfg_follow run rest =>
                obtain ⟨ℓ, hℓ, run'⟩ := Region.Eval.of_renameLabels run
                subst hℓ
                exact .core (.cfg_follow run' ⟨_, .follow ρ, rest⟩)
  | @follow env n blocks label value s ρ =>
      cases he.unfold with
      | core core => cases core with
        | @follow_body _ _ label' _ _ _ inside rest =>
            have hlt : label < n := by
              by_contra hge
              rw [Silmaril.DeBruijn.liftN_ge ρ (Nat.le_of_not_lt hge)] at inside
              omega
            have hfin : (⟨Silmaril.DeBruijn.liftN n ρ label, inside⟩ : Fin n) = ⟨label, hlt⟩ :=
              Fin.ext (Silmaril.DeBruijn.liftN_lt ρ hlt)
            rw [hfin] at rest
            exact .core (.follow_body hlt ⟨_, .region (Silmaril.DeBruijn.liftN n ρ), rest⟩)
        | @follow_next _ _ label' next _ _ _ _ _ inside head rest =>
            have hlt : label < n := by
              by_contra hge
              rw [Silmaril.DeBruijn.liftN_ge ρ (Nat.le_of_not_lt hge)] at inside
              omega
            have hfin : (⟨Silmaril.DeBruijn.liftN n ρ label, inside⟩ : Fin n) = ⟨label, hlt⟩ :=
              Fin.ext (Silmaril.DeBruijn.liftN_lt ρ hlt)
            rw [hfin] at head
            obtain ⟨m, hm, head'⟩ := Region.Eval.of_renameLabels head
            subst hm
            exact .core (.follow_next hlt head' ⟨_, .follow ρ, rest⟩)

/-- Infinite execution of a label-renamed region agrees with the original. -/
theorem Diverges.renameLabels_iff {env : Env α} {r : LambdaSSA.Region Φ} {s : σ}
    (ρ : Nat → Nat) :
    Diverges instr prim (.region env (r.renameLabels ρ) s) ↔
      Diverges instr prim (.region env r s) :=
  ⟨fun h => h.of_labelRenaming_rev (.region ρ), fun h => h.of_labelRenaming (.region ρ)⟩

end External

end Silmaril.Isotope.LambdaSSA.Semantics

module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.RegionReflection
public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Fault.Reflection
public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.External.Region
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ScopeStructural
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.External

/-!
# Untagging the packed exit of an encoded region

`encodeRegion` collapses the `labels` exits of a lambda-SSA region into a
single let-iter result, tagged by `SSA.FiniteSum.sumTy` through
`SSAIter.inject`. Recovering the original exits therefore needs an explicit
inverse on each side.

`untag` is the lambda-SSA region that dispatches a packed value held in the
newest variable back to the `labels` exit labels; it is an isomorphism in the
sense that it exits at label `i` with payload `v` exactly when the packed value
is `tagValue i v`, and it neither faults nor diverges. The empty case is stuck,
matching the stuckness of `abort` on both sides.

`unpackSingle` is the let-iter inverse for the degenerate case of one exit
label, where the packed type is `coprod A empty`.
-/

@[expose] public section

universe u v w x y

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open LetIter.Semantics
open LambdaSSA (Region)
open SSA.FiniteSum (sumTy)

variable {Φ : Type v}

/-- Dispatch a packed exit value, held in the newest variable, to the lambda-SSA
exit label `base + i` carrying the payload of alternative `i`. With no
alternatives the packed value inhabits the empty type and the region is stuck,
exactly as `abort` is in both calculi. -/
def untagFrom : (labels base : Nat) → Region Φ
  | 0, _ => .cfg (.let₁ (.abort (.var 0)) (.br 0 (.var 0))) 1 (fun _ => .br 0 (.var 0))
  | labels + 1, base => .case (.var 0) (.br base (.var 0)) (untagFrom labels (base + 1))

/-- Dispatch a packed exit value back to the `labels` lambda-SSA exit labels. -/
def untag (labels : Nat) : Region Φ := untagFrom labels 0

/-- Untagging only inspects the newest variable and only exits at the labels it
dispatches to. -/
theorem untagFrom_scoped : ∀ (labels base n m : Nat), base + labels ≤ n →
    (untagFrom (Φ := Φ) labels base).Scoped n (m + 1)
  | 0, base, n, m, h =>
      ⟨⟨Nat.zero_lt_succ _, by omega, Nat.zero_lt_succ _⟩,
        fun _ => ⟨by omega, Nat.zero_lt_succ _⟩⟩
  | labels + 1, base, n, m, h =>
      ⟨Nat.zero_lt_succ _, ⟨by omega, Nat.zero_lt_succ _⟩,
        untagFrom_scoped labels (base + 1) n (m + 1) (by omega)⟩

/-- The untagging region is scoped at the exit labels it dispatches to, under
any ambient value context holding the packed result. -/
theorem untag_scoped (labels m : Nat) : (untag (Φ := Φ) labels).Scoped labels (m + 1) :=
  untagFrom_scoped labels 0 labels m (by omega)

variable {α : Type u} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- Reading a variable yields its value and performs no state transition. -/
theorem eval_var_result {env : LambdaSSA.Semantics.Env α} {i : Nat} {s s' : σ}
    {value : Value α} (h : LambdaSSA.Semantics.Tm.Eval instr env (.var i) s value s') :
    value = env i ∧ s' = s := by cases h; exact ⟨rfl, rfl⟩

/-- Untagging exits at the label of the tag with the tagged payload, performs no
machine-state transition, and has no other finite behaviour. -/
theorem untagFrom_eval_iff {labels base : Nat} {env : LambdaSSA.Semantics.Env α}
    {s s' : σ} {label : Nat} {out : Value α} :
    LambdaSSA.Semantics.Region.Eval instr env (untagFrom labels base) s label out s' ↔
      ∃ i : Fin labels, label = base + i.val ∧ env 0 = tagValue i out ∧ s' = s := by
  induction labels generalizing base env s s' label out with
  | zero =>
      constructor
      · intro h
        cases h with
        | cfg entryRun _ => cases entryRun with | let₁ arg _ => cases arg
      · rintro ⟨i, _⟩; exact i.elim0
  | succ labels ih =>
      constructor
      · intro h
        cases h with
        | case_inl arg branch =>
            obtain ⟨henv, hs⟩ := eval_var_result arg
            subst hs
            cases branch with
            | br argBr =>
                obtain ⟨hout, hs'⟩ := eval_var_result argBr
                subst hs'
                exact ⟨0, by simp, by simpa [hout] using henv.symm, rfl⟩
        | case_inr arg branch =>
            obtain ⟨henv, hs⟩ := eval_var_result arg
            subst hs
            obtain ⟨j, hj, hpayload, hs'⟩ := ih.mp branch
            refine ⟨j.succ, by simp only [Fin.val_succ]; omega, ?_, hs'⟩
            simp only [LambdaSSA.Semantics.extend] at hpayload
            simpa [hpayload] using henv.symm
      · rintro ⟨i, hlabel, henv, rfl⟩
        cases i using Fin.cases with
        | zero =>
            simp only [Fin.val_zero, Nat.add_zero] at hlabel
            subst hlabel
            refine .case_inl (LambdaSSA.Semantics.Tm.Eval.var_of_eq ?_)
              (.br LambdaSSA.Semantics.Tm.Eval.var)
            simpa using henv
        | succ j =>
            refine LambdaSSA.Semantics.Region.Eval.case_inr (va := tagValue j out)
              (LambdaSSA.Semantics.Tm.Eval.var_of_eq (by simpa using henv))
              (ih.mpr ⟨j, ?_, rfl, rfl⟩)
            simp only [Fin.val_succ] at hlabel
            omega

/-- The untagging region exits at exit label `i` with the payload of the tag. -/
theorem untag_eval_iff {labels : Nat} {env : LambdaSSA.Semantics.Env α}
    {s s' : σ} {label : Nat} {out : Value α} :
    LambdaSSA.Semantics.Region.Eval instr env (untag labels) s label out s' ↔
      ∃ i : Fin labels, label = i.val ∧ env 0 = tagValue i out ∧ s' = s := by
  have h := untagFrom_eval_iff (instr := instr) (labels := labels) (base := 0)
    (env := env) (s := s) (s' := s') (label := label) (out := out)
  simpa only [untag, Nat.zero_add] using h

/-- Untagging runs no instruction, so it cannot fault. -/
theorem untagFrom_not_fault {faults : Φ → Value α → σ → σ → Prop} {labels base : Nat}
    {env : LambdaSSA.Semantics.Env α} {s s' : σ} :
    ¬ LambdaSSA.Semantics.Region.Fault instr faults env (untagFrom labels base) s s' := by
  induction labels generalizing base env s s' with
  | zero =>
      intro h
      cases h with
      | cfg_entry fault =>
          cases fault with
          | let₁_arg arg => cases arg with | abort_arg argArg => cases argArg
          | let₁_body argEval _ => cases argEval
      | cfg_follow run _ => cases run with | let₁ arg _ => cases arg
  | succ labels ih =>
      intro h
      cases h with
      | case_arg arg => cases arg
      | case_inl _ branch => cases branch with | br argBr => cases argBr
      | case_inr _ branch => exact ih branch

/-- Untagging makes finitely many control transfers and runs no instruction, so
it cannot diverge. -/
theorem untagFrom_not_diverges {prim : Φ → Value α → σ → Prop} {labels base : Nat}
    {env : LambdaSSA.Semantics.Env α} {s : σ} :
    ¬ LambdaSSA.Semantics.External.Diverges instr prim
        (.region env (untagFrom labels base) s) := by
  induction labels generalizing base env s with
  | zero =>
      intro h
      cases h.unfold with
      | core core => cases core with
        | cfg_entry rest =>
            cases rest.unfold with
            | let₁_arg div => cases div with | abort_arg argDiv => cases argDiv
            | core c₂ => cases c₂ with | let₁ arg _ => cases arg
        | cfg_follow run _ => cases run with | let₁ arg _ => cases arg
  | succ labels ih =>
      intro h
      cases h.unfold with
      | case_arg div => cases div
      | core core => cases core with
        | case_inl _ rest =>
            cases rest.unfold with
            | core c₂ => cases c₂
            | br div => cases div
        | case_inr _ rest => exact ih rest

variable {τ : Type x} [TypeFormers τ] [HasTy Φ τ]

/-- Untagging consumes the packed sum and lands in every exit at its own
payload type. -/
theorem untagFrom_hasType : ∀ {labels : Nat} {L : Fin labels → τ} {Γ : SSA.VCtx τ}
    {K : SSA.LCtx τ} (base : Nat), (∀ i : Fin labels, SSA.At K (base + i.val) (L i)) →
    Region.HasType (Φ := Φ) (sumTy L :: Γ) (untagFrom labels base) K
  | 0, L, Γ, K, base, _ => by
      refine Region.HasType.cfg (fun _ : Fin 1 => Silmaril.empty) ?_ (fun _ => .br rfl (.var rfl))
      exact .let₁ (.abort (.var rfl)) (.br rfl (.var rfl))
  | labels + 1, L, Γ, K, base, h => by
      refine Region.HasType.case (.var rfl) (.br ?_ (.var rfl)) ?_
      · simpa using h 0
      · refine untagFrom_hasType (L := fun i => L i.succ) (base + 1) (fun i => ?_)
        rw [show base + 1 + i.val = base + (i.val + 1) from by omega]
        exact h i.succ

/-- Untagging is exactly typed against the exit context the encoding packed. -/
theorem untag_hasType {labels : Nat} {L : Fin labels → τ} {Γ : SSA.VCtx τ} :
    Region.HasType (Φ := Φ) (sumTy L :: Γ) (untag labels) (List.ofFn L) :=
  untagFrom_hasType 0 (fun i => by
    simpa only [Nat.zero_add] using SSA.FiniteSum.at_ofFn L i)

variable {ν : Type y} {n : Nat}

/-- Strip the one-alternative sum tag that a single-exit label context
introduces, inverting the `coprod A empty` packing of `encodeRegion`. -/
def unpackSingle (a : Tm ν Φ n) : Tm ν Φ n := dispatch a (fun _ : Fin 1 => .bv 0)

variable {free : FreeEnv ν α}

/-- Unpacking returns the payload of a left-tagged result and nothing else. -/
theorem unpackSingle_eval_iff {bound : BoundEnv α n} {a : Tm ν Φ n} {s s' : σ}
    {result : Value α} :
    Eval instr free bound (unpackSingle a) s result s' ↔
      Eval instr free bound a s (.inl result) s' := by
  rw [unpackSingle, dispatch_eval_iff]
  constructor
  · rintro ⟨i, payload, mid, run, branch⟩
    cases branch
    have : i = 0 := Subsingleton.elim _ _
    subst this
    simpa using run
  · intro h
    exact ⟨0, result, s', by simpa using h, .bv⟩

/-- Unpacking faults exactly when its argument does. -/
theorem unpackSingle_fault_iff {faults : Φ → Value α → σ → σ → Prop}
    {bound : BoundEnv α n} {a : Tm ν Φ n} {s s' : σ} :
    Fault instr faults free bound (unpackSingle a) s s' ↔
      Fault instr faults free bound a s s' := by
  rw [unpackSingle, dispatch_fault_iff]
  constructor
  · rintro (h | ⟨i, payload, mid, _, branch⟩)
    · exact h
    · cases branch
  · exact Or.inl

/-- Unpacking diverges exactly when its argument does. -/
theorem unpackSingle_diverges_iff {prim : Φ → Value α → σ → Prop}
    {bound : BoundEnv α n} {a : Tm ν Φ n} {s : σ} :
    External.Diverges instr free prim (.term bound (unpackSingle a) s) ↔
      External.Diverges instr free prim (.term bound a s) := by
  rw [unpackSingle, External.dispatch_diverges_iff]
  constructor
  · rintro (h | ⟨i, payload, mid, _, branch⟩)
    · exact h
    · cases branch.unfold with
      | core core => cases core
  · exact Or.inl

/-- Unpacking inverts the one-alternative packing at the level of types. -/
theorem unpackSingle_hasType [DecidableEq ν] {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β a (sumTy (fun _ : Fin 1 => A))) :
    HasType Φ Γ β (unpackSingle a) A :=
  dispatch_hasType (fun _ : Fin 1 => A) h (fun _ => .bv)

end Silmaril.Isotope.Morphism.SSAIter

module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Untag
public import Silmaril.Raw.SSA.Isotope.Morphism.IterSSAReflection
public import Silmaril.Raw.SSA.Isotope.Morphism.IterSSAScope
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Observation
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Observation
public import Mathlib.Logic.Equiv.Defs

/-!
# The lambda-SSA / let-iter round trips

`SSAIter.encodeRegion` turns a scoped lambda-SSA region into a let-iter term,
and `IterSSA.compile` turns a let-iter term into a lambda-SSA region in
continuation-passing style. Both are known to preserve typing and semantics.
This module closes the loop.

An on-the-nose isomorphism is impossible for two reasons. The encoding packs
the `labels` exits of a region into one tagged value, so the two sides disagree
syntactically on how control leaves a region; and lambda-SSA has no equational
theory, so the only available notion of sameness is observational equivalence
of the operational semantics. The theorems below are therefore stated against
explicit untagging wrappers and up to `LambdaSSA.Region.Obs` and
`LetIter.LocallyNameless.Tm.Obs`.

The deliverable is `quotEquiv`: at a single exit label the induced maps on the
observational quotients are mutually inverse bijections.
-/

@[expose] public section

universe u v w x

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open LambdaSSA (Region)
open SSA.FiniteSum (sumTy)

variable {Φ : Type v} {n : Nat}

/-- Compile a positional let-iter term to a lambda-SSA region with a single
exit label carrying the term's result. -/
def compileSingle (t : Tm Empty Φ n) : Region Φ :=
  IterSSA.compile t (IterSSA.Vars.identity n) (.br 0 (.var 0))

/-- The compiled region uses exactly one exit label and the ambient variables. -/
theorem compileSingle_scoped (t : Tm Empty Φ n) : (compileSingle t).Scoped 1 n :=
  IterSSA.compile_return_scoped t

/-- Decode a let-iter term whose result is a packed exit value into a lambda-SSA
region with `labels` exits: run the term, then dispatch its tagged result. -/
def decode (labels : Nat) (t : Tm Empty Φ n) : Region Φ :=
  Region.sequence (compileSingle t) (untag labels)

/-- The decoded region uses exactly the exits its untagging dispatches to. -/
theorem decode_scoped (labels : Nat) (t : Tm Empty Φ n) : (decode labels t).Scoped labels n :=
  Region.Scoped.sequence (compileSingle_scoped t) (untag_scoped labels n)

/-- Encode a scoped single-exit region, removing the one-alternative tag that
its exit context introduces. -/
def encodeSingle (r : Region Φ) (h : r.Scoped 1 n) : Tm Empty Φ n :=
  unpackSingle (encodeRegion r h)

variable {α : Type u} {σ : Type w}

/-- The positional environment read off a bound environment, undefined slots
being filled with the unit value. -/
def envOfBound {m : Nat} (bound : LetIter.Semantics.BoundEnv α m) :
    LambdaSSA.Semantics.Env α := fun i => if h : i < m then bound ⟨i, h⟩ else .unit

/-- The read-off environment agrees with the bound environment it came from. -/
theorem envOfBound_agrees {m : Nat} (bound : LetIter.Semantics.BoundEnv α m) :
    CaseSSA.EnvAgrees (envOfBound bound) bound := fun i => by simp [envOfBound, i.isLt]

/-- The identity assignment relates a positional environment to the bound
environment it agrees with; there are no free variables to place. -/
theorem identity_relates {free : LetIter.Semantics.FreeEnv Empty α}
    {bound : LetIter.Semantics.BoundEnv α n} {env : LambdaSSA.Semantics.Env α}
    (agree : CaseSSA.EnvAgrees env bound) :
    IterSSA.Vars.Relates free bound env (IterSSA.Vars.identity n) where
  free x := x.elim
  bound i := agree i

variable {instr : Φ → Value α → σ → Value α → σ → Prop}
variable {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}
variable {free : LetIter.Semantics.FreeEnv Empty α}

/-! ## Single-exit regions and their untagged encodings -/

/-- A compiled single-exit region exits at label zero with the term's result. -/
theorem compileSingle_eval_iff {t : Tm Empty Φ n} {bound : LetIter.Semantics.BoundEnv α n}
    {env : LambdaSSA.Semantics.Env α} {s s' : σ} {label : Nat} {out : Value α}
    (agree : CaseSSA.EnvAgrees env bound) :
    LambdaSSA.Semantics.Region.Eval instr env (compileSingle t) s label out s' ↔
      label = 0 ∧ LetIter.Semantics.Eval instr free bound t s out s' :=
  IterSSA.compile_return_eval_iff t (identity_relates agree)

/-- A compiled single-exit region faults exactly when its term does. -/
theorem compileSingle_fault_iff {t : Tm Empty Φ n} {bound : LetIter.Semantics.BoundEnv α n}
    {env : LambdaSSA.Semantics.Env α} {s s' : σ} (agree : CaseSSA.EnvAgrees env bound) :
    LambdaSSA.Semantics.Region.Fault instr faults env (compileSingle t) s s' ↔
      LetIter.Semantics.Fault instr faults free bound t s s' :=
  IterSSA.compile_return_fault_iff t (identity_relates agree)

/-- A compiled single-exit region diverges exactly when its term does. -/
theorem compileSingle_diverges_iff {t : Tm Empty Φ n}
    {bound : LetIter.Semantics.BoundEnv α n} {env : LambdaSSA.Semantics.Env α} {s : σ}
    (agree : CaseSSA.EnvAgrees env bound) :
    LambdaSSA.Semantics.External.Diverges instr prim (.region env (compileSingle t) s) ↔
      LetIter.Semantics.External.Diverges instr free prim (.term bound t s) :=
  IterSSA.compile_return_diverges_iff t (identity_relates agree)

/-- The untagged encoding of a single-exit region has exactly its results. -/
theorem encodeSingle_eval_iff {r : Region Φ} (h : r.Scoped 1 n)
    {bound : LetIter.Semantics.BoundEnv α n} {env : LambdaSSA.Semantics.Env α}
    {s s' : σ} {out : Value α} (agree : CaseSSA.EnvAgrees env bound) :
    LetIter.Semantics.Eval instr free bound (encodeSingle r h) s out s' ↔
      LambdaSSA.Semantics.Region.Eval instr env r s 0 out s' := by
  rw [encodeSingle, unpackSingle_eval_iff, encodeRegion_eval_iff h agree]
  constructor
  · rintro ⟨i, value, run, heq⟩
    have : i = 0 := Subsingleton.elim _ _
    subst this
    simp only [tagValue_zero, Value.inl.injEq] at heq
    exact heq ▸ run
  · intro run
    exact ⟨0, out, run, by simp⟩

/-- The untagged encoding of a single-exit region has exactly its faults. -/
theorem encodeSingle_fault_iff {r : Region Φ} (h : r.Scoped 1 n)
    {bound : LetIter.Semantics.BoundEnv α n} {env : LambdaSSA.Semantics.Env α} {s s' : σ}
    (agree : CaseSSA.EnvAgrees env bound) :
    LetIter.Semantics.Fault instr faults free bound (encodeSingle r h) s s' ↔
      LambdaSSA.Semantics.Region.Fault instr faults env r s s' := by
  rw [encodeSingle, unpackSingle_fault_iff, encodeRegion_fault_iff h agree]

/-- The untagged encoding of a single-exit region has exactly its divergences. -/
theorem encodeSingle_diverges_iff {r : Region Φ} (h : r.Scoped 1 n)
    {bound : LetIter.Semantics.BoundEnv α n} {env : LambdaSSA.Semantics.Env α} {s : σ}
    (agree : CaseSSA.EnvAgrees env bound) :
    LetIter.Semantics.External.Diverges instr free prim (.term bound (encodeSingle r h) s) ↔
      LambdaSSA.Semantics.External.Diverges instr prim (.region env r s) := by
  rw [encodeSingle, unpackSingle_diverges_iff, External.encodeRegion_diverges_iff h agree]

/-! ## Decoding a packed exit -/

/-- Decoding runs the term and dispatches its tagged result to the matching
exit label, with no further state transition. -/
theorem decode_eval_iff {labels : Nat} {t : Tm Empty Φ n}
    {bound : LetIter.Semantics.BoundEnv α n} {env : LambdaSSA.Semantics.Env α}
    {s s' : σ} {label : Nat} {out : Value α} (agree : CaseSSA.EnvAgrees env bound) :
    LambdaSSA.Semantics.Region.Eval instr env (decode labels t) s label out s' ↔
      ∃ i : Fin labels, label = i.val ∧
        LetIter.Semantics.Eval instr free bound t s (tagValue i out) s' := by
  constructor
  · intro h
    cases h with
    | cfg entryRun follow =>
        obtain ⟨rfl, runTerm⟩ := (compileSingle_eval_iff agree).mp entryRun
        cases follow with
        | exit outside => omega
        | step inside head tail =>
            obtain ⟨ℓ, hℓ, runUntag⟩ :=
              LambdaSSA.Semantics.Region.Eval.of_renameLabels head
            obtain ⟨i, hi, hpacked, hstate⟩ := untag_eval_iff.mp runUntag
            subst hstate
            cases tail with
            | exit outside =>
                refine ⟨i, ?_, ?_⟩
                · simp only [hℓ, hi]; omega
                · simpa only [LambdaSSA.Semantics.extend] using hpacked ▸ runTerm
            | step inside' _ _ => omega
  · rintro ⟨i, rfl, runTerm⟩
    have head : LambdaSSA.Semantics.Region.Eval instr
        (LambdaSSA.Semantics.extend env (tagValue i out))
        ((untag labels).renameLabels Nat.succ) s' (i.val + 1) out s' :=
      LambdaSSA.Semantics.Region.Eval.renameLabels
        (untag_eval_iff.mpr ⟨i, rfl, rfl, rfl⟩) Nat.succ
    refine LambdaSSA.Semantics.Region.Eval.cfg
      ((compileSingle_eval_iff agree).mpr ⟨rfl, runTerm⟩)
      (LambdaSSA.Semantics.Region.Follow.step (by decide) head ?_)
    simpa using LambdaSSA.Semantics.Region.Follow.exit
      (instr := instr) (env := env)
      (blocks := fun _ : Fin 1 => (untag labels).renameLabels Nat.succ)
      (value := out) (s := s') (Nat.le_add_left 1 i.val)

/-- Decoding faults exactly when its term does: dispatching cannot fault. -/
theorem decode_fault_iff {labels : Nat} {t : Tm Empty Φ n}
    {bound : LetIter.Semantics.BoundEnv α n} {env : LambdaSSA.Semantics.Env α} {s s' : σ}
    (agree : CaseSSA.EnvAgrees env bound) :
    LambdaSSA.Semantics.Region.Fault instr faults env (decode labels t) s s' ↔
      LetIter.Semantics.Fault instr faults free bound t s s' := by
  constructor
  · intro h
    cases h with
    | cfg_entry fault => exact (compileSingle_fault_iff agree).mp fault
    | cfg_follow run fault =>
        cases fault with
        | body inside faultBlock =>
            exact absurd (LambdaSSA.Semantics.Region.Fault.of_renameLabels faultBlock)
              untagFrom_not_fault
        | step inside runBlock tail =>
            obtain ⟨ℓ, hℓ, runUntag⟩ :=
              LambdaSSA.Semantics.Region.Eval.of_renameLabels runBlock
            obtain ⟨i, hi, _, _⟩ := untag_eval_iff.mp runUntag
            subst hℓ
            cases tail <;> omega
  · intro h
    exact .cfg_entry ((compileSingle_fault_iff agree).mpr h)

/-- Decoding diverges exactly when its term does: dispatching is finite. -/
theorem decode_diverges_iff {labels : Nat} {t : Tm Empty Φ n}
    {bound : LetIter.Semantics.BoundEnv α n} {env : LambdaSSA.Semantics.Env α} {s : σ}
    (agree : CaseSSA.EnvAgrees env bound) :
    LambdaSSA.Semantics.External.Diverges instr prim (.region env (decode labels t) s) ↔
      LetIter.Semantics.External.Diverges instr free prim (.term bound t s) := by
  constructor
  · intro h
    cases h.unfold with
    | core core => cases core with
      | cfg_entry rest => exact (compileSingle_diverges_iff agree).mp rest
      | cfg_follow run rest =>
          cases rest.unfold with
          | core c₂ => cases c₂ with
            | follow_body inside restBlock =>
                exact absurd
                  ((LambdaSSA.Semantics.External.Diverges.renameLabels_iff Nat.succ).mp restBlock)
                  untagFrom_not_diverges
            | follow_next inside runBlock restNext =>
                obtain ⟨ℓ, hℓ, runUntag⟩ :=
                  LambdaSSA.Semantics.Region.Eval.of_renameLabels runBlock
                obtain ⟨i, hi, _, _⟩ := untag_eval_iff.mp runUntag
                subst hℓ
                cases restNext.unfold with
                | core c₃ => cases c₃ <;> omega
  · intro h
    exact .fold_core (.cfg_entry ((compileSingle_diverges_iff agree).mpr h))

/-! ## The two round trips -/

/-- **Lambda-SSA round trip.** Encoding a scoped region into let-iter, compiling
it back, and dispatching the packed exit gives an observationally equivalent
region: the same exit labels with the same results and final states, the same
faults, and the same divergences. -/
theorem roundTrip_region {labels : Nat} (r : Region Φ) (h : r.Scoped labels n) :
    Region.Obs.{v, u, w} (decode labels (encodeRegion r h)) r where
  eval := by
    intro α' σ' instr' env s s' label out
    rw [decode_eval_iff (free := Empty.elim) (fun i => rfl)]
    constructor
    · rintro ⟨i, rfl, run⟩
      obtain ⟨j, value, source, heq⟩ := (encodeRegion_eval_iff h (fun i => rfl)).mp run
      obtain ⟨rfl, rfl⟩ := (tagValue_eq_iff ..).mp heq.symm
      exact source
    · intro run
      refine ⟨⟨_, h.eval_label_lt run⟩, rfl, ?_⟩
      exact (encodeRegion_eval_iff h (fun i => rfl)).mpr ⟨_, _, run, rfl⟩
  fault := by
    intro α' σ' instr' faults' env s s'
    rw [decode_fault_iff (free := Empty.elim) (fun i => rfl),
      encodeRegion_fault_iff h (fun i => rfl)]
  diverges := by
    intro α' σ' instr' prim' env s
    rw [decode_diverges_iff (free := Empty.elim) (fun i => rfl),
      External.encodeRegion_diverges_iff h (fun i => rfl)]

/-- The single-exit specialization of the lambda-SSA round trip, phrased with
the let-iter untagging wrapper used by the quotient bijection. -/
theorem roundTrip_single (r : Region Φ) (h : r.Scoped 1 n) :
    Region.Obs.{v, u, w} (compileSingle (encodeSingle r h)) r where
  eval := by
    intro α' σ' instr' env s s' label out
    rw [compileSingle_eval_iff (free := Empty.elim) (fun i => rfl),
      encodeSingle_eval_iff h (fun i => rfl)]
    constructor
    · rintro ⟨rfl, run⟩; exact run
    · intro run
      exact ⟨Nat.lt_one_iff.mp (h.eval_label_lt run), by
        simpa only [Nat.lt_one_iff.mp (h.eval_label_lt run)] using run⟩
  fault := by
    intro α' σ' instr' faults' env s s'
    rw [compileSingle_fault_iff (free := Empty.elim) (fun i => rfl),
      encodeSingle_fault_iff h (fun i => rfl)]
  diverges := by
    intro α' σ' instr' prim' env s
    rw [compileSingle_diverges_iff (free := Empty.elim) (fun i => rfl),
      encodeSingle_diverges_iff h (fun i => rfl)]

/-- **Let-iter round trip.** Compiling a term to a single-exit region and
encoding it back gives an observationally equivalent term, once the
`coprod A empty` tag that the single-exit label context introduces is removed. -/
theorem roundTrip_term (t : Tm Empty Φ n) :
    Tm.Obs.{v, u, w, 0} (encodeSingle (compileSingle t) (compileSingle_scoped t)) t where
  eval := by
    intro α' σ' instr' free' bound s s' value
    rw [encodeSingle_eval_iff (free := free') _ (envOfBound_agrees bound),
      compileSingle_eval_iff (free := free') (envOfBound_agrees bound)]
    simp
  fault := by
    intro α' σ' instr' faults' free' bound s s'
    rw [encodeSingle_fault_iff (free := free') _ (envOfBound_agrees bound),
      compileSingle_fault_iff (free := free') (envOfBound_agrees bound)]
  diverges := by
    intro α' σ' instr' prim' free' bound s
    rw [encodeSingle_diverges_iff (free := free') _ (envOfBound_agrees bound),
      compileSingle_diverges_iff (free := free') (envOfBound_agrees bound)]

/-! ## Transfer of observational equivalence -/

/-- The encoding is full and faithful for observational equivalence: encoded
regions agree observationally exactly when the regions do. -/
theorem encodeRegion_obs_iff {labels : Nat} {r r' : Region Φ}
    (h : r.Scoped labels n) (h' : r'.Scoped labels n) :
    Tm.Obs.{v, u, w, 0} (encodeRegion r h) (encodeRegion r' h') ↔ Region.Obs.{v, u, w} r r' := by
  constructor
  · intro hobs
    refine ⟨?_, ?_, ?_⟩
    · intro α' σ' instr' env s s' label out
      by_cases hlabel : label < labels
      · have key := @Tm.Obs.eval _ _ _ _ _ hobs α' σ' instr' Empty.elim
          (fun i : Fin n => env i.val) s s' (tagValue ⟨label, hlabel⟩ out)
        rw [encodeRegion_eval_iff h (fun i => rfl),
          encodeRegion_eval_iff h' (fun i => rfl)] at key
        constructor
        · intro run
          obtain ⟨j, value, source, heq⟩ := key.mp ⟨⟨label, hlabel⟩, out, run, rfl⟩
          obtain ⟨rfl, rfl⟩ := (tagValue_eq_iff ..).mp heq.symm
          exact source
        · intro run
          obtain ⟨j, value, source, heq⟩ := key.mpr ⟨⟨label, hlabel⟩, out, run, rfl⟩
          obtain ⟨rfl, rfl⟩ := (tagValue_eq_iff ..).mp heq.symm
          exact source
      · constructor
        · intro run; exact absurd (h.eval_label_lt run) hlabel
        · intro run; exact absurd (h'.eval_label_lt run) hlabel
    · intro α' σ' instr' faults' env s s'
      have key := @Tm.Obs.fault _ _ _ _ _ hobs α' σ' instr' faults' Empty.elim
        (fun i : Fin n => env i.val) s s'
      rwa [encodeRegion_fault_iff h (fun i => rfl),
        encodeRegion_fault_iff h' (fun i => rfl)] at key
    · intro α' σ' instr' prim' env s
      have key := @Tm.Obs.diverges _ _ _ _ _ hobs α' σ' instr' prim' Empty.elim
        (fun i : Fin n => env i.val) s
      rwa [External.encodeRegion_diverges_iff h (fun i => rfl),
        External.encodeRegion_diverges_iff h' (fun i => rfl)] at key
  · intro hobs
    refine ⟨?_, ?_, ?_⟩
    · intro α' σ' instr' free' bound s s' value
      rw [encodeRegion_eval_iff h (envOfBound_agrees bound),
        encodeRegion_eval_iff h' (envOfBound_agrees bound)]
      exact exists_congr (fun i => exists_congr (fun v => and_congr_left'
        (@Region.Obs.eval _ _ _ hobs α' σ' instr' _ _ _ _ _)))
    · intro α' σ' instr' faults' free' bound s s'
      rw [encodeRegion_fault_iff h (envOfBound_agrees bound),
        encodeRegion_fault_iff h' (envOfBound_agrees bound)]
      exact @Region.Obs.fault _ _ _ hobs α' σ' instr' faults' _ _ _
    · intro α' σ' instr' prim' free' bound s
      rw [External.encodeRegion_diverges_iff h (envOfBound_agrees bound),
        External.encodeRegion_diverges_iff h' (envOfBound_agrees bound)]
      exact @Region.Obs.diverges _ _ _ hobs α' σ' instr' prim' _ _

/-- Untagged single-exit encoding is full and faithful for observational
equivalence. -/
theorem encodeSingle_obs_iff {r r' : Region Φ} (h : r.Scoped 1 n) (h' : r'.Scoped 1 n) :
    Tm.Obs.{v, u, w, 0} (encodeSingle r h) (encodeSingle r' h') ↔ Region.Obs.{v, u, w} r r' := by
  constructor
  · intro hobs
    refine ⟨?_, ?_, ?_⟩
    · intro α' σ' instr' env s s' label out
      by_cases hlabel : label = 0
      · subst hlabel
        have key := @Tm.Obs.eval _ _ _ _ _ hobs α' σ' instr' Empty.elim
          (fun i : Fin n => env i.val) s s' out
        rwa [encodeSingle_eval_iff h (fun i => rfl),
          encodeSingle_eval_iff h' (fun i => rfl)] at key
      · constructor
        · intro run; exact absurd (Nat.lt_one_iff.mp (h.eval_label_lt run)) hlabel
        · intro run; exact absurd (Nat.lt_one_iff.mp (h'.eval_label_lt run)) hlabel
    · intro α' σ' instr' faults' env s s'
      have key := @Tm.Obs.fault _ _ _ _ _ hobs α' σ' instr' faults' Empty.elim
        (fun i : Fin n => env i.val) s s'
      rwa [encodeSingle_fault_iff h (fun i => rfl),
        encodeSingle_fault_iff h' (fun i => rfl)] at key
    · intro α' σ' instr' prim' env s
      have key := @Tm.Obs.diverges _ _ _ _ _ hobs α' σ' instr' prim' Empty.elim
        (fun i : Fin n => env i.val) s
      rwa [encodeSingle_diverges_iff h (fun i => rfl),
        encodeSingle_diverges_iff h' (fun i => rfl)] at key
  · intro hobs
    refine ⟨?_, ?_, ?_⟩
    · intro α' σ' instr' free' bound s s' value
      rw [encodeSingle_eval_iff h (envOfBound_agrees bound),
        encodeSingle_eval_iff h' (envOfBound_agrees bound)]
      exact @Region.Obs.eval _ _ _ hobs α' σ' instr' _ _ _ _ _
    · intro α' σ' instr' faults' free' bound s s'
      rw [encodeSingle_fault_iff h (envOfBound_agrees bound),
        encodeSingle_fault_iff h' (envOfBound_agrees bound)]
      exact @Region.Obs.fault _ _ _ hobs α' σ' instr' faults' _ _ _
    · intro α' σ' instr' prim' free' bound s
      rw [encodeSingle_diverges_iff h (envOfBound_agrees bound),
        encodeSingle_diverges_iff h' (envOfBound_agrees bound)]
      exact @Region.Obs.diverges _ _ _ hobs α' σ' instr' prim' _ _

/-- Compilation is full and faithful for observational equivalence. -/
theorem compileSingle_obs_iff (t t' : Tm Empty Φ n) :
    Region.Obs.{v, u, w} (compileSingle t) (compileSingle t') ↔ Tm.Obs.{v, u, w, 0} t t' := by
  constructor
  · intro hobs
    refine ⟨?_, ?_, ?_⟩
    · intro α' σ' instr' free' bound s s' value
      have key := @Region.Obs.eval _ _ _ hobs α' σ' instr' (envOfBound bound) s s' 0 value
      rw [compileSingle_eval_iff (free := free') (envOfBound_agrees bound),
        compileSingle_eval_iff (free := free') (envOfBound_agrees bound)] at key
      simpa using key
    · intro α' σ' instr' faults' free' bound s s'
      have key := @Region.Obs.fault _ _ _ hobs α' σ' instr' faults' (envOfBound bound) s s'
      rwa [compileSingle_fault_iff (free := free') (envOfBound_agrees bound),
        compileSingle_fault_iff (free := free') (envOfBound_agrees bound)] at key
    · intro α' σ' instr' prim' free' bound s
      have key := @Region.Obs.diverges _ _ _ hobs α' σ' instr' prim' (envOfBound bound) s
      rwa [compileSingle_diverges_iff (free := free') (envOfBound_agrees bound),
        compileSingle_diverges_iff (free := free') (envOfBound_agrees bound)] at key
  · intro hobs
    refine ⟨?_, ?_, ?_⟩
    · intro α' σ' instr' env s s' label out
      rw [compileSingle_eval_iff (free := Empty.elim) (fun i => rfl),
        compileSingle_eval_iff (free := Empty.elim) (fun i => rfl)]
      exact and_congr_right' (@Tm.Obs.eval _ _ _ _ _ hobs α' σ' instr' _ _ _ _ _)
    · intro α' σ' instr' faults' env s s'
      rw [compileSingle_fault_iff (free := Empty.elim) (fun i => rfl),
        compileSingle_fault_iff (free := Empty.elim) (fun i => rfl)]
      exact @Tm.Obs.fault _ _ _ _ _ hobs α' σ' instr' faults' _ _ _ _
    · intro α' σ' instr' prim' env s
      rw [compileSingle_diverges_iff (free := Empty.elim) (fun i => rfl),
        compileSingle_diverges_iff (free := Empty.elim) (fun i => rfl)]
      exact @Tm.Obs.diverges _ _ _ _ _ hobs α' σ' instr' prim' _ _ _

/-! ## Typing -/

variable {τ : Type x} [TypeFormers τ] [HasTy Φ τ]

/-- Compiling a typed term gives a region with one exit at the term's type. -/
theorem compileSingle_hasType {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (ht : HasType Φ .nil β t A) : Region.HasType β.toList (compileSingle t) [A] :=
  IterSSA.compile_typed ht (IterSSA.Vars.identity_hasType β) (.br rfl (.var rfl))

/-- Decoding a term whose result is a packed exit value is exactly typed against
the exit context that packing came from. -/
theorem decode_hasType {labels : Nat} {L : Fin labels → τ} {β : BoundCtx τ n}
    {t : Tm Empty Φ n} (ht : HasType Φ .nil β t (sumTy L)) :
    Region.HasType β.toList (decode labels t) (List.ofFn L) :=
  Region.HasType.sequence (compileSingle_hasType ht) untag_hasType

/-- The lambda-SSA round trip preserves exact typing. -/
theorem roundTrip_region_hasType {labels : Nat} {r : Region Φ} (h : r.Scoped labels n)
    {L : Fin labels → τ} {β : BoundCtx τ n} (ht : Region.HasType β.toList r (List.ofFn L)) :
    Region.HasType β.toList (decode labels (encodeRegion r h)) (List.ofFn L) :=
  decode_hasType (encodeRegion_hasType h ht)

/-- Encoding a typed single-exit region and removing its tag preserves exact typing. -/
theorem encodeSingle_hasType {r : Region Φ} (h : r.Scoped 1 n) {A : τ} {β : BoundCtx τ n}
    (ht : Region.HasType β.toList r [A]) : HasType Φ .nil β (encodeSingle r h) A :=
  show HasType Φ .nil β (unpackSingle (encodeRegion r h)) A from
    unpackSingle_hasType (encodeRegion_hasType (L := fun _ : Fin 1 => A) h (by simpa using ht))

/-- The let-iter round trip preserves exact typing. -/
theorem roundTrip_term_hasType {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (ht : HasType Φ .nil β t A) :
    HasType Φ .nil β (encodeSingle (compileSingle t) (compileSingle_scoped t)) A :=
  encodeSingle_hasType _ (compileSingle_hasType ht)

/-! ## The bijection on observational quotients -/

/-- Scoped regions, the carrier of the lambda-SSA observational quotient. -/
def ScopedRegion (Φ : Type v) (labels n : Nat) : Type v := { r : Region Φ // r.Scoped labels n }

/-- Observational equivalence of scoped regions, at a fixed pair of value and
machine-state universes. -/
def regionSetoid.{uu, vv, ww} (Φ : Type uu) (labels n : Nat) :
    Setoid (ScopedRegion Φ labels n) where
  r a b := Region.Obs.{uu, vv, ww} a.val b.val
  iseqv := ⟨fun a => Region.Obs.refl a.val, Region.Obs.symm, Region.Obs.trans⟩

/-- Observational equivalence of positional let-iter terms, at a fixed pair of
value and machine-state universes. -/
def termSetoid.{uu, vv, ww} (Φ : Type uu) (n : Nat) : Setoid (Tm Empty Φ n) where
  r a b := Tm.Obs.{uu, vv, ww, 0} a b
  iseqv := ⟨Tm.Obs.refl, Tm.Obs.symm, Tm.Obs.trans⟩

/-- The induced map from single-exit regions to terms. -/
def encodeQuot :
    Quotient (regionSetoid.{v, u, w} Φ 1 n) → Quotient (termSetoid.{v, u, w} Φ n) :=
  Quotient.map (fun r => encodeSingle r.val r.property)
    (fun _ _ h => (encodeSingle_obs_iff _ _).mpr h)

/-- The induced map from terms to single-exit regions. -/
def compileQuot :
    Quotient (termSetoid.{v, u, w} Φ n) → Quotient (regionSetoid.{v, u, w} Φ 1 n) :=
  Quotient.map (fun t => ⟨compileSingle t, compileSingle_scoped t⟩)
    (fun _ _ h => (compileSingle_obs_iff _ _).mpr h)

/-- Compiling then encoding is the identity on the let-iter quotient. -/
theorem encodeQuot_compileQuot (q : Quotient (termSetoid.{v, u, w} Φ n)) :
    encodeQuot (compileQuot q) = q := by
  induction q using Quotient.inductionOn with
  | h t => exact Quotient.sound (roundTrip_term t)

/-- Encoding then compiling is the identity on the lambda-SSA quotient. -/
theorem compileQuot_encodeQuot (q : Quotient (regionSetoid.{v, u, w} Φ 1 n)) :
    compileQuot (encodeQuot q) = q := by
  induction q using Quotient.inductionOn with
  | h r => exact Quotient.sound (roundTrip_single r.val r.property)

/-- **The isomorphism.** Single-exit lambda-SSA regions modulo observational
equivalence and positional let-iter terms modulo observational equivalence are
in bijection, realized by the two existing translations. -/
def quotEquiv :
    Quotient (regionSetoid.{v, u, w} Φ 1 n) ≃ Quotient (termSetoid.{v, u, w} Φ n) where
  toFun := encodeQuot
  invFun := compileQuot
  left_inv := compileQuot_encodeQuot
  right_inv := encodeQuot_compileQuot

end Silmaril.Isotope.Morphism.SSAIter

module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.Agreement
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.Divergence
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.ExternalAgreement
public import Silmaril.Semantics.Behaviour.Thms

/-!
# LetIter as a `Machine.Behaviour.Semantics`

`Machine.Behaviour` is the target-independent vocabulary the compiler theorems
of `Silmaril/Machine/` are stated in: a small-step `step : S → S → Prop`, a
`final : S → Outcome R T F → Prop`, and `Beh`, `Safe`, `Refines`, `Implements`
built on top of them. For LetIter to appear on the source side of that
vocabulary — which is what the pipeline

```
LetIter  ≅  λSSA  ≅  RTL.SSA  ←  RTL  →  Lir  →  x86-64
```

needs — it has to be presented as one small-step relation with a notion of
final state.

LetIter's own operational semantics is big-step (`Semantics.Eval`,
`Semantics.Fault`, `Semantics.Diverges`, `Semantics.External.Diverges`), so the
packaging runs through the CK machine of
`Silmaril/Isotope/LetIter/Semantics/Machine.lean`: configurations
`Machine.Config`, one small-step relation `Machine.Step instr free`, and
`Machine.eval_iff_steps` / `Machine.loop_iff_steps` — which are **unconditional
`iff`s**, with no determinism, totality or typing hypothesis — tying the machine
back to `Eval` and `Loop`.

## The choice of `final`

Following `Silmaril/Machine/RTL/Behaviour.lean`:

| configuration | outcome |
| --- | --- |
| `.ret v .halt s` | `.returned (v, s)` |
| no successor, not halted | `.undefined` |
| has a successor | not final |

Mapping stuck configurations to `.undefined` rather than leaving them without
an outcome is the same decision RTL makes, and it buys the same two things:
`Progress` holds unconditionally (`sem_progress`), so every configuration has a
behaviour; and `Safe` becomes a statement with content — "no reachable
configuration is stuck" (`safe_iff_no_stuck`).

Stuck configurations are real and are not an artefact. `Kont.abort` has no
consuming rule, a missing primitive transition leaves `.ret a (.op f k) s` with
no successor, and so does a value of the wrong shape at a `let₂`, `case` or
`iterBody` frame. `Machine.primitive_stuck` and `Machine.abort_stuck` are the
two the machine files single out.

## What is an `iff`, and what is not

This is the part of the packaging that has to be stated honestly, because the
four judgements do not all transport equally.

* **Returning is an `iff`.** `beh_returned_iff` and `beh_loop_returned_iff`:
  `(sem instr free).Beh (.eval bound t .halt s) (.returned (v, s'))` holds
  exactly when `Eval instr free bound t s v s'` does, with no hypotheses. Both
  directions come from `Machine.eval_iff_steps`, which is itself an `iff`.
* **Machine divergence is an `iff`**, trivially: `Beh c .diverges` unfolds to
  `Silmaril.InfiniteTrace (Step instr free) c`, which is `Machine.Diverges` by
  `Machine.Diverges.iff_infiniteTrace`.
* **Source divergence transports in one direction only.**
  `Machine.source_diverges` gives `Semantics.Diverges instr free (.term bound t s)
  → Machine.Diverges instr free (.eval bound t k s)`, and there is **no converse
  in the repository**: no theorem takes an infinite machine path back to a
  source divergence derivation. `beh_diverges_of_source` and
  `beh_diverges_of_loop_source` are therefore implications, not `iff`s, and are
  stated as such. The nearest thing to the missing direction is negative —
  `Machine.Steps.not_diverges`, that a halting run cannot also diverge, under
  `InstrDeterministic`.
* **External divergence does not package as `.diverges` at all**, and this is
  not a gap in the proofs but a difference of definition.
  `Machine.External.Diverges instr free prim c` admits a *finite* path ending at
  a configuration `AtPrimitive prim`, where a primitive is declared to diverge
  by fiat; `Beh c .diverges` is an actual infinite `Step` path. The two agree
  exactly when there are no divergent primitives, which is
  `Machine.External.Diverges.false_iff`, and that is the case
  `beh_diverges_of_external` is stated for. Packaging a divergent primitive
  would mean giving it a self-loop in `Step`, which would change the machine.
* **Faults do not transport at all.** `Semantics.Fault` takes a fault relation
  `faults : Φ → Value α → σ → σ → Prop` as a *third* parameter, separate from
  `instr`; `Machine.Step` has no such parameter and `Machine/` never mentions
  `Fault`. A faulting primitive simply has no machine transition, so the machine
  is stuck and this packaging reports `.undefined`. The fault payload type is
  therefore `Empty`, and there is **no theorem here relating `Semantics.Fault` to
  `.faulted`, or to `.undefined`**. Giving LetIter a `.faulted` outcome needs a
  `Step` that carries `faults` and an agreement theorem for it; that is a file of
  its own.

So `T = Empty` (the machine has no traps) and `F = Empty` (the machine has no
faults), and the outcomes a LetIter configuration can actually show are
`.returned`, `.undefined` and `.diverges` — `not_beh_trapped`,
`not_beh_faulted` and `not_beh_exhausted` rule out the other three.

## `Steps` against `ReflTransGen`

`Machine.Steps` is a bespoke reflexive-transitive closure and `Beh` is stated
with `Relation.ReflTransGen`. `steps_iff_reflTransGen` is the one-line bridge,
and every agreement theorem below goes through it.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.Machine

open LocallyNameless
open Silmaril.Machine.Behaviour (Semantics Outcome)
open Relation

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

/-! ## Finite executions as a `ReflTransGen` -/

/-- `Machine.Steps` is `Relation.ReflTransGen` of `Machine.Step`. The machine
files define their own closure; `Behaviour.Semantics.Beh` uses Mathlib's, and
this is the bridge. -/
theorem steps_iff_reflTransGen {a b : Config α ν Φ σ} :
    Steps instr free a b ↔ ReflTransGen (Step instr free) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | cons hstep _ ih => exact .head hstep ih
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ hstep ih => exact ih.trans hstep.steps

/-! ## Halted and stuck configurations -/

/-- What a halted configuration returns: the value and the state at
`Kont.halt`, and nothing anywhere else. -/
def result? : Config α ν Φ σ → Option (Value α × σ)
  | .ret v .halt s => some (v, s)
  | _ => none

/-- A configuration that returns is the halted one it returns from. -/
theorem eq_ret_halt_of_result? {c : Config α ν Φ σ} {r : Value α × σ}
    (h : result? c = some r) : c = .ret r.1 .halt r.2 := by
  match c, h with
  | .ret _ .halt _, h =>
    simp only [result?, Option.some.injEq] at h
    subst h
    rfl

/-- A halted configuration has no successor: no `Step` rule matches
`Kont.halt`. -/
theorem not_step_ret_halt {v : Value α} {s : σ} :
    ∀ d, ¬ Step instr free (.ret v .halt s) d := by
  intro d h
  cases h

/-- A configuration that returns has no successor. -/
theorem not_step_of_result? {c : Config α ν Φ σ} {r : Value α × σ}
    (h : result? c = some r) : ∀ d, ¬ Step instr free c d := by
  rw [eq_ret_halt_of_result? h]
  exact not_step_ret_halt

/-- **A stuck configuration**: one that has no successor and is not halted.
`Kont.abort`, a missing primitive transition and a value of the wrong shape at
an eliminating frame are the three ways to reach one. -/
def Stuck (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α)
    (c : Config α ν Φ σ) : Prop :=
  result? c = none ∧ ∀ d, ¬ Step instr free c d

/-! ## The semantics -/

/-- **LetIter's CK machine as a `Machine.Behaviour.Semantics`.** The step
relation is `Machine.Step`; a configuration is final when it has halted, with
outcome `.returned (v, s)`, or when it is stuck, with outcome `.undefined`.
There are no traps and no faults, so both payloads are `Empty`. -/
def sem (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    Semantics (Config α ν Φ σ) (Value α × σ) Empty Empty where
  step := Step instr free
  final c o :=
    (∃ r, result? c = some r ∧ o = .returned r) ∨ (Stuck instr free c ∧ o = .undefined)

@[simp] theorem sem_step (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    (sem instr free).step = Step instr free := rfl

theorem sem_final_iff {c : Config α ν Φ σ} {o : Outcome (Value α × σ) Empty Empty} :
    (sem instr free).final c o ↔
      (∃ r, result? c = some r ∧ o = .returned r) ∨ (Stuck instr free c ∧ o = .undefined) :=
  Iff.rfl

/-- The configuration a closed run starts from: the term under the empty
continuation. -/
def entryConfig {n : Nat} (bound : BoundEnv α n) (t : Tm ν Φ n) (s : σ) : Config α ν Φ σ :=
  .eval bound t .halt s

/-! ## Determinism and progress -/

/-- **The machine is deterministic exactly when the primitive relation is.**
`Machine.Step.deterministic` gives the step clause; the two final clauses are
exclusive because `Stuck` asks for `result? c = none`, and a final configuration
does not step because a halted one does not and a stuck one does not by
definition. -/
theorem sem_deterministic (hd : InstrDeterministic instr) (free : FreeEnv ν α) :
    (sem instr free).Deterministic where
  step_unique _ _ _ ha hb := Step.deterministic hd ha hb
  final_unique c o o' h h' := by
    rcases h with ⟨r, hr, rfl⟩ | ⟨hst, rfl⟩ <;> rcases h' with ⟨r', hr', rfl⟩ | ⟨hst', rfl⟩
    · exact congrArg _ (Option.some.inj (hr.symm.trans hr'))
    · exact absurd (hr.symm.trans hst'.1) (by simp)
    · exact absurd (hst.1.symm.trans hr') (by simp)
    · rfl
  final_stop c _ h d hstep := by
    rcases h with ⟨r, hr, -⟩ | ⟨hst, -⟩
    · exact not_step_of_result? hr d hstep
    · exact hst.2 d hstep

/-- **The machine has progress**, with no hypotheses: a configuration either
steps, has halted, or is stuck, and the last two are final outcomes. This is
cheap for the reason `Silmaril/Machine/RTL/Behaviour.lean` records — `.undefined`
is a *final* outcome rather than an absent one — and the corresponding content
lives in `Safe`. -/
theorem sem_progress (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    (sem instr free).Progress := by
  classical
  intro c
  by_cases hs : ∃ d, Step instr free c d
  · exact .inl hs
  · cases hr : result? c with
    | some r => exact .inr ⟨.returned r, .inl ⟨r, hr, rfl⟩, by simp⟩
    | none => exact .inr ⟨.undefined, .inr ⟨⟨hr, fun d hd => hs ⟨d, hd⟩⟩, rfl⟩, by simp⟩

/-- Every configuration has a behaviour. -/
theorem beh_exists (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α)
    (c : Config α ν Φ σ) : ∃ o, (sem instr free).Beh c o :=
  Semantics.Beh.exists (sem_progress instr free) c

/-- A configuration has at most one behaviour when the primitive relation is
deterministic. -/
theorem beh_unique (hd : InstrDeterministic instr) {c : Config α ν Φ σ}
    {o o' : Outcome (Value α × σ) Empty Empty} (h : (sem instr free).Beh c o)
    (h' : (sem instr free).Beh c o') : o = o' :=
  Semantics.Beh.unique (sem_deterministic hd free) h h'

/-! ## The outcomes the machine cannot show -/

/-- The machine has no traps: `trap` is a `Lir` notion, not a LetIter one. -/
theorem not_beh_trapped {c : Config α ν Φ σ} {t : Empty} :
    ¬ (sem instr free).Beh c (.trapped t) := t.elim

/-- The machine has no faults. `Semantics.Fault` is a judgement over a fault
relation `Machine.Step` does not carry; a faulting primitive leaves the machine
stuck, which this packaging reports as `.undefined`. -/
theorem not_beh_faulted {c : Config α ν Φ σ} {f : Empty} :
    ¬ (sem instr free).Beh c (.faulted f) := f.elim

/-- The machine has no resource bound, so it never exhausts one. -/
theorem not_beh_exhausted {c : Config α ν Φ σ} : ¬ (sem instr free).Beh c .exhausted := by
  rw [Semantics.beh_of_ne (by simp)]
  rintro ⟨d, -, hf⟩
  rcases hf with ⟨r, -, h⟩ | ⟨-, h⟩ <;> exact absurd h (by simp)

/-! ## Returning agrees with `Eval` -/

/-- A reachable final configuration showing `.returned r` is the halted
configuration `.ret r.1 .halt r.2`. -/
theorem beh_returned_iff_reach {c : Config α ν Φ σ} {r : Value α × σ} :
    (sem instr free).Beh c (.returned r) ↔ ReflTransGen (Step instr free) c (.ret r.1 .halt r.2) := by
  rw [Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨d, hd, hf⟩
    rcases hf with ⟨r', hr', heq⟩ | ⟨-, heq⟩
    · cases heq
      exact eq_ret_halt_of_result? hr' ▸ hd
    · exact absurd heq (by simp)
  · intro h
    exact ⟨_, h, .inl ⟨r, rfl, rfl⟩⟩

/-- **Returning agrees with `Eval`**, with no hypotheses on `instr` and no
typing. `Machine.eval_iff_steps` is an `iff` in both directions, so this is one
too: the packaged semantics returns `(v, s')` from the term `t` exactly when the
big-step judgement evaluates `t` to `v` with final state `s'`. -/
theorem beh_returned_iff {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s s' : σ}
    {v : Value α} :
    (sem instr free).Beh (entryConfig bound t s) (.returned (v, s')) ↔
      Eval instr free bound t s v s' := by
  rw [beh_returned_iff_reach, ← steps_iff_reflTransGen]
  exact eval_iff_steps.symm

/-- **Returning from a loop agrees with `Loop`**, by `Machine.loop_iff_steps`,
and for the same reason an `iff`. -/
theorem beh_loop_returned_iff {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {current v : Value α} {s s' : σ} :
    (sem instr free).Beh (.loop bound body current .halt s) (.returned (v, s')) ↔
      Loop instr free bound body current s v s' := by
  rw [beh_returned_iff_reach, ← steps_iff_reflTransGen]
  exact loop_iff_steps.symm

/-! ## Divergence -/

/-- **Divergence is machine divergence**, definitionally: `Beh _ .diverges` is
an infinite `Step` path, and `Machine.Diverges` is the same thing presented as a
greatest fixed point (`Machine.Diverges.iff_infiniteTrace`). -/
theorem beh_diverges_iff {c : Config α ν Φ σ} :
    (sem instr free).Beh c .diverges ↔ Diverges instr free c :=
  Diverges.iff_infiniteTrace.symm

/-- **A diverging term diverges on the machine**, under any continuation.
`Machine.source_diverges`, read through `beh_diverges_iff`.

This is an implication and **not** an `iff`: nothing in the repository takes an
infinite machine path back to a `Semantics.Diverges` derivation. The available
partial converse is negative — `Machine.Steps.not_diverges`, that a run reaching
`.ret v .halt s'` does not also diverge, under `InstrDeterministic`. -/
theorem beh_diverges_of_source {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s : σ}
    (h : Semantics.Diverges instr free (.term bound t s)) (k : Kont α ν Φ) :
    (sem instr free).Beh (.eval bound t k s) .diverges :=
  Diverges.iff_infiniteTrace.mp (source_diverges h k)

/-- **A diverging loop diverges on the machine**, under any continuation. The
same implication, for `Semantics.Diverges` at a `loop` configuration. -/
theorem beh_diverges_of_loop_source {n : Nat} {bound : BoundEnv α n}
    {body : Tm ν Φ (n + 1)} {current : Value α} {s : σ}
    (h : Semantics.Diverges instr free (.loop bound body current s)) (k : Kont α ν Φ) :
    (sem instr free).Beh (.loop bound body current k s) .diverges :=
  Diverges.iff_infiniteTrace.mp (source_loop_diverges h k)

/-- **External divergence packages as `.diverges` exactly when no primitive
diverges.** `Semantics.External.Diverges` with the primitive-divergence
predicate set to `False` is the internal judgement
(`Semantics.External.Diverges.false_iff`), and `Machine.External.Diverges` with
the same predicate is `Machine.Diverges`
(`Machine.External.Diverges.false_iff`), which is an infinite `Step` path.

With a primitive that does diverge the statement is **false as an outcome**, and
not because a proof is missing: `Machine.External.Diverges` admits a *finite*
path ending at an `AtPrimitive` configuration, while `Beh _ .diverges` is an
actual infinite path. `Machine.External.term_diverges` is the general statement,
and it lands in `Machine.External.Diverges`, not in `Beh`. -/
theorem beh_diverges_of_external {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s : σ}
    (h : Semantics.External.Diverges instr free (fun _ _ _ => False) (.term bound t s))
    (k : Kont α ν Φ) :
    (sem instr free).Beh (.eval bound t k s) .diverges :=
  Diverges.iff_infiniteTrace.mp (External.Diverges.false_iff.mp (External.term_diverges h k))

/-! ## Safety -/

/-- **`Safe` is "no reachable configuration is stuck".** The undefined behaviour
of this packaging is exactly `Machine.Stuck` — `Kont.abort`, a missing primitive
transition, or a value of the wrong shape at an eliminating frame — so a safe
configuration is one from which the machine always either halts or keeps
running. -/
theorem beh_undefined_iff {c : Config α ν Φ σ} :
    (sem instr free).Beh c .undefined ↔
      ∃ d, ReflTransGen (Step instr free) c d ∧ Stuck instr free d := by
  rw [Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨d, hd, hf⟩
    rcases hf with ⟨r, -, heq⟩ | ⟨hst, -⟩
    · exact absurd heq (by simp)
    · exact ⟨d, hd, hst⟩
  · rintro ⟨d, hd, hst⟩
    exact ⟨d, hd, .inr ⟨hst, rfl⟩⟩

/-- `Safe` in the `Machine.Behaviour` vocabulary, spelled out. -/
theorem safe_iff_no_stuck {c : Config α ν Φ σ} :
    (sem instr free).Safe c ↔ ¬ ∃ d, ReflTransGen (Step instr free) c d ∧ Stuck instr free d :=
  not_congr beh_undefined_iff

/-- **An evaluating term is safe**, with no hypotheses: a finite evaluation
reaches the halted configuration, and a halted configuration is not stuck, so by
determinism of the run there is nothing stuck in between.

The determinism hypothesis is `InstrDeterministic`, and it is needed: without it
the machine may have a stuck branch beside the evaluating one, and
`Machine.Steps.not_diverges` is stated with the same premise for the same
reason. -/
theorem safe_of_eval (hd : InstrDeterministic instr) {n : Nat} {bound : BoundEnv α n}
    {t : Tm ν Φ n} {s s' : σ} {v : Value α} (h : Eval instr free bound t s v s') :
    (sem instr free).Safe (entryConfig bound t s) := by
  intro hu
  have hr : (sem instr free).Beh (entryConfig bound t s) (.returned (v, s')) :=
    beh_returned_iff.mpr h
  exact absurd (beh_unique hd hu hr) (by simp)

end Silmaril.Isotope.LetIter.Semantics.Machine

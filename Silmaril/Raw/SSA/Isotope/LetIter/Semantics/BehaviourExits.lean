module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Behaviour

/-!
# LetIter read at the machine's outcome vocabulary

`Silmaril/Isotope/LetIter/Semantics/Behaviour.lean` packages LetIter's CK
machine as a `Machine.Behaviour.Semantics` whose only finite outcomes are
`.returned` and `.undefined`. That is the right reading of a *closed* term, and
it is the wrong reading of a term that stands for a λSSA region with two exits.

## Why a second reading is needed

`Silmaril/Machine/RTL/ToLambdaSSA.lean` fixes the convention that an SSA-form
RTL function becomes a λSSA region with **two external labels**: label `0` is
`ret`, carrying the packed returned words, and label `1` is `trap`, carrying
`unit`. `Silmaril/Isotope/Morphism/SSAIter/` encodes a region with `labels`
exits as a let-iter term whose *result value* is tagged with the exit it left
by — `tagValue (i : Fin labels) v`, which is `i` nested `.inr`s around `.inl v`.

At two exits that means

| the region leaves by | the term returns |
| --- | --- |
| label `0` with the packed results `v` | `.inl v` |
| label `1` with `unit` | `.inr (.inl .unit)` |

So **a trap arrives at the LetIter level as a returned tagged value**, not as a
trap. `Machine.Behaviour.Outcome.Rel` has no case relating a target `.trapped`
to a source `.returned` — that entry of the table is `False` — so a plain
`Implements` whose source is `Machine.sem` and whose target is x86-64, where
the `trap` block compiles to a `UD2`, **cannot hold**, and must not be stated.

## The fix is an adapter, not a weakening

`semExits` is the *same machine*: the same `Step`, the same stuck
configurations, the same infinite runs. Only `final` differs, and it differs
exactly by decoding the tag that the λSSA encoding introduced. `exitOutcome` is
that decoding, and it is total: a halted configuration whose value carries
neither tag — `.unit`, an `.atom`, a `.pair`, or an `.inr` of something that is
not an `.inl` — is reported `.undefined`, which is the same convention a stuck
configuration gets and keeps `Progress` unconditional.

Nothing is smuggled in by the change of vocabulary, and the theorems that say
so are the `beh_exits_*_iff` family: each outcome of `semExits` is *equivalent*
to a statement about `sem`, with the tag written out. In particular
`beh_exits_diverges_iff` is `Iff.rfl` — the two semantics have the same `step`,
so they have literally the same infinite runs — and `beh_exits_undefined_iff`
shows exactly which extra configurations the decoding sends to `.undefined`.

## What this file does not do

It does not give LetIter a fault outcome: `Semantics.Fault` is a judgement over
a fault relation `Machine.Step` does not carry, so `F = Empty` here as it is in
`Behaviour.lean`, for the reason that file's docstring gives. It does not
observe an exhausted resource either. And it fixes the arity at **two** exits,
because that is the arity `toLambdaSSA` produces; a general `Fin labels`
version would have to choose, for each `i`, which of the six outcomes the
`i`-th exit stands for, and no such choice is canonical.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.Machine

open LocallyNameless
open Silmaril.Machine.Behaviour (Semantics Outcome)
open Relation

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

/-! ## Decoding the exit tag -/

/-- **The two-exit decoding.** A result tagged as the first exit is a return
carrying the untagged payload; a result tagged as the second exit is a trap
carrying the state; anything else is undefined behaviour.

The two tags are `tagValue (0 : Fin 2) v = .inl v` and
`tagValue (1 : Fin 2) v = .inr (.inl v)`, which is why the second pattern is
`.inr (.inl _)` and not merely `.inr _`: a bare `.inr (.inr v)` is not the
image of any exit of a two-exit region, and reporting it as a trap would be
reading a tag that is not there. -/
def exitOutcome : Value α → σ → Outcome (Value α × σ) σ Empty
  | .inl v, s => .returned (v, s)
  | .inr (.inl _), s => .trapped s
  | _, s => let _ := s; .undefined

@[simp] theorem exitOutcome_inl (v : Value α) (s : σ) :
    exitOutcome v.inl s = .returned (v, s) := rfl

@[simp] theorem exitOutcome_inr_inl (v : Value α) (s : σ) :
    exitOutcome (Value.inr v.inl) s = .trapped s := rfl

@[simp] theorem exitOutcome_unit (s : σ) : exitOutcome (Value.unit : Value α) s = .undefined :=
  rfl

@[simp] theorem exitOutcome_atom (a : α) (s : σ) : exitOutcome (Value.atom a) s = .undefined :=
  rfl

@[simp] theorem exitOutcome_pair (a b : Value α) (s : σ) :
    exitOutcome (Value.pair a b) s = .undefined := rfl

@[simp] theorem exitOutcome_inr_inr (v : Value α) (s : σ) :
    exitOutcome (Value.inr v.inr) s = .undefined := rfl

@[simp] theorem exitOutcome_inr_unit (s : σ) :
    exitOutcome (Value.inr Value.unit : Value α) s = .undefined := rfl

@[simp] theorem exitOutcome_inr_atom (a : α) (s : σ) :
    exitOutcome (Value.inr (Value.atom a)) s = .undefined := rfl

@[simp] theorem exitOutcome_inr_pair (a b : Value α) (s : σ) :
    exitOutcome (Value.inr (Value.pair a b)) s = .undefined := rfl

/-- The decoding never produces a fault: the fault payload is `Empty`. -/
theorem exitOutcome_ne_faulted {v : Value α} {s : σ} {e : Empty} :
    exitOutcome v s ≠ .faulted e := e.elim

/-- The decoding never produces exhaustion or divergence: both are outcomes of
a *run*, and this is a function of one halted configuration. -/
theorem exitOutcome_ne_diverges {v : Value α} {s : σ} : exitOutcome v s ≠ .diverges := by
  match v with
  | .inl _ | .inr (.inl _) | .unit | .atom _ | .pair _ _ | .inr (.inr _) | .inr .unit
  | .inr (.atom _) | .inr (.pair _ _) => simp [exitOutcome]

theorem exitOutcome_ne_exhausted {v : Value α} {s : σ} : exitOutcome v s ≠ .exhausted := by
  match v with
  | .inl _ | .inr (.inl _) | .unit | .atom _ | .pair _ _ | .inr (.inr _) | .inr .unit
  | .inr (.atom _) | .inr (.pair _ _) => simp [exitOutcome]

/-- `exitOutcome` returns exactly at the first tag. -/
theorem exitOutcome_eq_returned_iff {v : Value α} {s : σ} {r : Value α × σ} :
    exitOutcome v s = .returned r ↔ v = .inl r.1 ∧ s = r.2 := by
  match v with
  | .inl w =>
    simp only [exitOutcome_inl, Outcome.returned.injEq, Value.inl.injEq]
    exact ⟨fun h => ⟨congrArg Prod.fst h.symm ▸ rfl, congrArg Prod.snd h.symm ▸ rfl⟩,
      fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩
  | .inr (.inl _) | .unit | .atom _ | .pair _ _ | .inr (.inr _) | .inr .unit
  | .inr (.atom _) | .inr (.pair _ _) => simp [exitOutcome]

/-- `exitOutcome` traps exactly at the second tag, and the trap payload is the
state the machine halted in. -/
theorem exitOutcome_eq_trapped_iff {v : Value α} {s s' : σ} :
    exitOutcome v s = .trapped s' ↔ (∃ w, v = .inr (.inl w)) ∧ s = s' := by
  match v with
  | .inr (.inl w) =>
    simp only [exitOutcome_inr_inl, Outcome.trapped.injEq]
    exact ⟨fun h => ⟨⟨w, rfl⟩, h⟩, fun h => h.2⟩
  | .inl _ | .unit | .atom _ | .pair _ _ | .inr (.inr _) | .inr .unit
  | .inr (.atom _) | .inr (.pair _ _) => simp [exitOutcome]

/-- `exitOutcome` is undefined exactly on the untagged values. -/
theorem exitOutcome_eq_undefined_iff {v : Value α} {s : σ} :
    exitOutcome v s = .undefined ↔ (¬ ∃ w, v = .inl w) ∧ ¬ ∃ w, v = .inr (.inl w) := by
  match v with
  | .inl _ | .inr (.inl _) | .unit | .atom _ | .pair _ _ | .inr (.inr _) | .inr .unit
  | .inr (.atom _) | .inr (.pair _ _) => simp [exitOutcome]

/-! ## The semantics -/

/-- **LetIter read at the machine's outcome vocabulary.** The step relation is
`Machine.Step`, exactly as in `sem`; a halted configuration shows the outcome
`exitOutcome` decodes from its value, and a stuck configuration shows
`.undefined`.

This is the same machine as `sem`. Only `final` differs, and it differs exactly
by decoding the tag that the λSSA encoding introduced: the trap payload type is
`σ` rather than `Empty`, because a trap is now reachable, and the fault payload
is still `Empty`, because nothing here carries a fault relation. -/
def semExits (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    Semantics (Config α ν Φ σ) (Value α × σ) σ Empty where
  step := Step instr free
  final c o :=
    (∃ r, result? c = some r ∧ o = exitOutcome r.1 r.2) ∨ (Stuck instr free c ∧ o = .undefined)

@[simp] theorem semExits_step (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) : (semExits instr free).step = Step instr free := rfl

/-- The two semantics have the same transition relation, on the nose. -/
theorem semExits_step_eq_sem_step (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) : (semExits instr free).step = (sem instr free).step := rfl

theorem semExits_final_iff {c : Config α ν Φ σ} {o : Outcome (Value α × σ) σ Empty} :
    (semExits instr free).final c o ↔
      (∃ r, result? c = some r ∧ o = exitOutcome r.1 r.2) ∨
        (Stuck instr free c ∧ o = .undefined) :=
  Iff.rfl

/-! ## Determinism and progress, as `sem` has them -/

/-- **The machine is deterministic exactly when the primitive relation is**, by
the same argument as `sem_deterministic`: the step clause is
`Machine.Step.deterministic`, the two final clauses are exclusive because
`Stuck` asks for `result? c = none`, and a final configuration does not step. -/
theorem semExits_deterministic (hd : InstrDeterministic instr) (free : FreeEnv ν α) :
    (semExits instr free).Deterministic where
  step_unique _ _ _ ha hb := Step.deterministic hd ha hb
  final_unique c o o' h h' := by
    rcases h with ⟨r, hr, rfl⟩ | ⟨hst, rfl⟩ <;> rcases h' with ⟨r', hr', rfl⟩ | ⟨hst', rfl⟩
    · obtain rfl : r = r' := Option.some.inj (hr.symm.trans hr')
      rfl
    · exact absurd (hr.symm.trans hst'.1) (by simp)
    · exact absurd (hst.1.symm.trans hr') (by simp)
    · rfl
  final_stop c _ h d hstep := by
    rcases h with ⟨r, hr, -⟩ | ⟨hst, -⟩
    · exact not_step_of_result? hr d hstep
    · exact hst.2 d hstep

/-- **The machine has progress**, with no hypotheses, for the reason `sem` does:
a configuration either steps, has halted — and then `exitOutcome` gives it an
outcome, total by construction — or is stuck. -/
theorem semExits_progress (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) : (semExits instr free).Progress := by
  classical
  intro c
  by_cases hs : ∃ d, Step instr free c d
  · exact .inl hs
  · cases hr : result? c with
    | some r => exact .inr ⟨exitOutcome r.1 r.2, .inl ⟨r, hr, rfl⟩, exitOutcome_ne_diverges⟩
    | none => exact .inr ⟨.undefined, .inr ⟨⟨hr, fun d hd => hs ⟨d, hd⟩⟩, rfl⟩, by simp⟩

/-- Every configuration has a behaviour. -/
theorem beh_exits_exists (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α)
    (c : Config α ν Φ σ) : ∃ o, (semExits instr free).Beh c o :=
  Semantics.Beh.exists (semExits_progress instr free) c

/-- A configuration has at most one behaviour when the primitive relation is
deterministic. -/
theorem beh_exits_unique (hd : InstrDeterministic instr) {c : Config α ν Φ σ}
    {o o' : Outcome (Value α × σ) σ Empty} (h : (semExits instr free).Beh c o)
    (h' : (semExits instr free).Beh c o') : o = o' :=
  Semantics.Beh.unique (semExits_deterministic hd free) h h'

/-- The machine still has no faults: `Semantics.Fault` is a judgement over a
fault relation `Machine.Step` does not carry. -/
theorem not_beh_exits_faulted {c : Config α ν Φ σ} {f : Empty} :
    ¬ (semExits instr free).Beh c (.faulted f) := f.elim

/-- The machine has no resource bound, so it never exhausts one. -/
theorem not_beh_exits_exhausted {c : Config α ν Φ σ} :
    ¬ (semExits instr free).Beh c .exhausted := by
  rw [Semantics.beh_of_ne (by simp)]
  rintro ⟨d, -, hf⟩
  rcases hf with ⟨r, -, h⟩ | ⟨-, h⟩
  · exact exitOutcome_ne_exhausted h.symm
  · exact absurd h (by simp)

/-! ## The adapter is faithful

Each outcome of `semExits` is *equivalent* to a statement about `sem` with the
tag written out. Nothing is gained and nothing is lost by the change of
vocabulary; what changes is which halted configurations are called returns. -/

/-- A reachable final configuration showing `.returned (v, s)` is the halted
configuration `.ret (.inl v) .halt s`. -/
theorem beh_exits_returned_iff_reach {c : Config α ν Φ σ} {v : Value α} {s : σ} :
    (semExits instr free).Beh c (.returned (v, s)) ↔
      ReflTransGen (Step instr free) c (.ret v.inl .halt s) := by
  rw [Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨d, hd, hf⟩
    rcases hf with ⟨r, hr, heq⟩ | ⟨-, heq⟩
    · obtain ⟨hv, hs⟩ := exitOutcome_eq_returned_iff.mp heq.symm
      have hdr : d = .ret r.1 .halt r.2 := eq_ret_halt_of_result? hr
      rw [hdr] at hd
      simpa only [hv, hs, semExits_step] using hd
    · exact absurd heq (by simp)
  · intro h
    exact ⟨_, h, .inl ⟨(Value.inl v, s), rfl, rfl⟩⟩

/-- **A return of `semExits` is a return of `sem` under the first tag.** -/
theorem beh_exits_returned_iff {c : Config α ν Φ σ} {v : Value α} {s : σ} :
    (semExits instr free).Beh c (.returned (v, s)) ↔
      (sem instr free).Beh c (.returned (v.inl, s)) := by
  rw [beh_exits_returned_iff_reach, beh_returned_iff_reach]

/-- A reachable final configuration showing `.trapped s` is a halted
configuration carrying the second tag. -/
theorem beh_exits_trapped_iff_reach {c : Config α ν Φ σ} {s : σ} :
    (semExits instr free).Beh c (.trapped s) ↔
      ∃ w : Value α, ReflTransGen (Step instr free) c (.ret (Value.inr (Value.inl w)) .halt s)
      := by
  rw [Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨d, hd, hf⟩
    rcases hf with ⟨r, hr, heq⟩ | ⟨-, heq⟩
    · obtain ⟨⟨w, hv⟩, hs⟩ := exitOutcome_eq_trapped_iff.mp heq.symm
      refine ⟨w, ?_⟩
      have hdr : d = .ret r.1 .halt r.2 := eq_ret_halt_of_result? hr
      rw [hdr] at hd
      simpa only [hv, hs, semExits_step] using hd
    · exact absurd heq (by simp)
  · rintro ⟨w, h⟩
    exact ⟨_, h, .inl ⟨(Value.inr (Value.inl w), s), rfl, rfl⟩⟩

/-- **A trap of `semExits` is a return of `sem` under the second tag.** This is
the whole of the adapter in one statement: the trap the machine reports is the
tagged value the λSSA encoding produced, and nothing else. -/
theorem beh_exits_trapped_iff {c : Config α ν Φ σ} {s : σ} :
    (semExits instr free).Beh c (.trapped s) ↔
      ∃ w : Value α, (sem instr free).Beh c (.returned (Value.inr (Value.inl w), s)) := by
  rw [beh_exits_trapped_iff_reach]
  exact exists_congr fun w =>
    (beh_returned_iff_reach (r := (Value.inr (Value.inl w), s))).symm

/-- **Divergence is unchanged**, definitionally: the two semantics have the same
`step`, so they have the same infinite runs. -/
theorem beh_exits_diverges_iff {c : Config α ν Φ σ} :
    (semExits instr free).Beh c .diverges ↔ (sem instr free).Beh c .diverges := Iff.rfl

/-- **Divergence is machine divergence**, as it is for `sem`. -/
theorem beh_exits_diverges_iff_diverges {c : Config α ν Φ σ} :
    (semExits instr free).Beh c .diverges ↔ Diverges instr free c :=
  beh_diverges_iff

/-- **Undefined behaviour is `sem`'s, plus the untagged returns.** This is the
honest statement of what the decoding costs: a configuration that halts with a
value carrying neither exit tag was a *return* for `sem` and is undefined
behaviour here. Such a configuration cannot arise from a two-exit λSSA region,
but nothing in this file's types says so, so it is reported rather than
excluded. -/
theorem beh_exits_undefined_iff {c : Config α ν Φ σ} :
    (semExits instr free).Beh c .undefined ↔
      (sem instr free).Beh c .undefined ∨
        ∃ v s, (sem instr free).Beh c (.returned (v, s)) ∧
          (¬ ∃ w, v = .inl w) ∧ ¬ ∃ w, v = .inr (.inl w) := by
  rw [Semantics.beh_of_ne (by simp), beh_undefined_iff]
  constructor
  · rintro ⟨d, hd, hf⟩
    rcases hf with ⟨r, hr, heq⟩ | ⟨hst, -⟩
    · refine .inr ⟨r.1, r.2, ?_, exitOutcome_eq_undefined_iff.mp heq.symm⟩
      rw [beh_returned_iff_reach]
      exact eq_ret_halt_of_result? hr ▸ hd
    · exact .inl ⟨d, hd, hst⟩
  · rintro (⟨d, hd, hst⟩ | ⟨v, s, hb, hv⟩)
    · exact ⟨d, hd, .inr ⟨hst, rfl⟩⟩
    · rw [beh_returned_iff_reach] at hb
      exact ⟨_, hb, .inl ⟨(v, s), rfl, (exitOutcome_eq_undefined_iff.mpr hv).symm⟩⟩

/-- **A safe configuration for `semExits` is safe for `sem` as well**, and
returns only tagged values. The converse fails, and the counterexample is the
whole content of `beh_exits_undefined_iff`: a term returning `.unit` is safe for
`sem` and unsafe here. -/
theorem semExits_safe_iff {c : Config α ν Φ σ} :
    (semExits instr free).Safe c ↔
      (sem instr free).Safe c ∧
        ∀ v s, (sem instr free).Beh c (.returned (v, s)) →
          (∃ w, v = .inl w) ∨ ∃ w, v = .inr (.inl w) := by
  classical
  rw [Semantics.Safe, Semantics.Safe, beh_exits_undefined_iff]
  constructor
  · intro h
    refine ⟨fun hu => h (.inl hu), fun v s hb => ?_⟩
    by_contra hc
    exact h (.inr ⟨v, s, hb, fun hl => hc (.inl hl), fun hr => hc (.inr hr)⟩)
  · rintro ⟨h₁, h₂⟩ (hu | ⟨v, s, hb, hl, hr⟩)
    · exact h₁ hu
    · rcases h₂ v s hb with h | h
      · exact hl h
      · exact hr h

/-! ## Agreement with the big-step judgement

The two statements the pipeline consumes: the term returns under the first tag,
and the term returns under the second. Both are `iff`s with no hypotheses,
because `Machine.eval_iff_steps` is. -/

/-- **Returning agrees with `Eval` at the first tag.** The packaged semantics
returns `(v, s')` from the term `t` exactly when the big-step judgement
evaluates `t` to the *tagged* value `.inl v`. -/
theorem beh_exits_returned_iff_eval {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} {v : Value α} :
    (semExits instr free).Beh (entryConfig bound t s) (.returned (v, s')) ↔
      Eval instr free bound t s (Value.inl v) s' := by
  rw [beh_exits_returned_iff]
  exact beh_returned_iff

/-- **Trapping agrees with `Eval` at the second tag.** The packaged semantics
traps in `s'` exactly when the big-step judgement evaluates `t` to a value
tagged as the second exit. -/
theorem beh_exits_trapped_iff_eval {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} :
    (semExits instr free).Beh (entryConfig bound t s) (.trapped s') ↔
      ∃ w : Value α, Eval instr free bound t s (Value.inr (Value.inl w)) s' := by
  rw [beh_exits_trapped_iff]
  exact exists_congr fun _ => beh_returned_iff

/-- **A diverging term diverges on the machine**, under any continuation: the
implication of `beh_diverges_of_source`, read at the new vocabulary. It is an
implication and not an `iff` for the reason `Behaviour.lean` gives — nothing in
the repository takes an infinite machine path back to a `Semantics.Diverges`
derivation. -/
theorem beh_exits_diverges_of_source {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s : σ}
    (h : Semantics.Diverges instr free (.term bound t s)) (k : Kont α ν Φ) :
    (semExits instr free).Beh (.eval bound t k s) .diverges :=
  beh_diverges_of_source h k

/-- **An evaluating term is safe**, provided it evaluates to a tagged value.
The tag hypothesis is exactly what `semExits_safe_iff`'s second conjunct asks
for, and it is not decoration: a term evaluating to `.unit` is safe for `sem`
and unsafe here. -/
theorem semExits_safe_of_eval (hd : InstrDeterministic instr) {n : Nat}
    {bound : BoundEnv α n} {t : Tm ν Φ n} {s s' : σ} {v : Value α}
    (h : Eval instr free bound t s v s')
    (hv : (∃ w, v = .inl w) ∨ ∃ w, v = .inr (.inl w)) :
    (semExits instr free).Safe (entryConfig bound t s) := by
  refine semExits_safe_iff.mpr ⟨safe_of_eval hd h, fun w u hb => ?_⟩
  have : (sem instr free).Beh (entryConfig bound t s) (.returned (v, s')) :=
    beh_returned_iff.mpr h
  obtain ⟨hw, -⟩ := Prod.mk.injEq _ _ _ _ ▸
    Outcome.returned.inj (beh_unique hd hb this)
  exact hw ▸ hv

end Silmaril.Isotope.LetIter.Semantics.Machine

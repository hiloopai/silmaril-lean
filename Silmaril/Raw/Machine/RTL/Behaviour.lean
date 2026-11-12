module

public import Silmaril.Raw.Machine.RTL.Semantics
public import Silmaril.Semantics.Behaviour.Thms

/-!
# RTL as a `Machine.Behaviour.Semantics`

`RTL/Semantics.lean` already presents RTL as a small-step machine with a
determinism theorem and a four-way classification of whole runs. This file
repackages it in the shared vocabulary of `Machine/Behaviour`, following
`Silmaril/Wasm/Compile/Behaviour.lean`, so that RTL can appear on either side of
`Refines` and `Implements`.

The outcome of a stopped state is read off `step`:

| `step p s` | outcome |
| --- | --- |
| `.returned vs m` | `.returned (vs, m)` |
| `.trapped m` | `.trapped m` |
| `.stuck` | `.undefined` |
| `.running s'` | not final |

**`.stuck` is mapped to `.undefined`, not to `.faulted`.** RTL's stuck states
are the source-level undefined behaviour of `Lir`'s convention — division by
zero, out-of-bounds memory, unwritten registers — and not machine faults. The
fault payload type is therefore `Empty`. The point of the choice is `Safe`:
`(sem p).Safe s` unfolds to "no execution from `s` gets stuck"
(`safe_iff_not_stuck`), which is exactly the side condition a CompCert-style
refinement wants from its source.

**Progress holds, and it is cheap.** Because `.stuck` is a *final* outcome
rather than an absent one, every state either steps or shows a finite outcome,
so `(sem p).Progress` is provable (`sem_progress`) and every state has a
behaviour.

It is worth being precise about what this does *not* buy, because the word
`Progress` is also what `Silmaril/Wasm/Compile/ImplementsX86.lean` has to work
hard for. There, `live` — no state reachable from the loaded program is stuck —
is the real content of the compiler theorem, and it is hard precisely because
the x86 target does *not* declare its stuck states final: a target state with no
decoding has no behaviour at all, so a refinement statement about it is vacuous
until liveness is proved. RTL declares its stuck states final with outcome
`undefined`, so the same vacuity cannot arise and progress is free. The
corresponding content for RTL lives in `Safe`: `(sem p).Safe s` unfolds to "no
execution from `s` gets stuck" (`safe_iff_not_stuck`). Callers that want "the
program does not go wrong" must ask for `Safe`; progress will not tell them.
-/

@[expose] public section

namespace Silmaril.Machine.RTL

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.Behaviour (Semantics Outcome)
open Relation

variable {R : Type} [DecidableEq R]

/-- The payload of an RTL return: the returned values and the final memory. -/
abbrev Ret := List Word × Memory

/-- The outcome a result shows when a run stops there; `none` for a running
state, which is not final. -/
def outcomeOf : Result R → Option (Silmaril.Machine.Behaviour.Outcome Ret Memory Empty)
  | .returned vs m => some (.returned (vs, m))
  | .trapped m => some (.trapped m)
  | .stuck => some .undefined
  | .running _ => none

/-- RTL as a small-step semantics with behaviours. -/
def sem (p : Prog R) : Silmaril.Machine.Behaviour.Semantics (State R) Ret Memory Empty where
  step := Step p
  final s o := outcomeOf (step p s) = some o

@[simp] theorem sem_step (p : Prog R) : (sem p).step = Step p := rfl

theorem sem_final_iff {p : Prog R} {s : State R} {o : Silmaril.Machine.Behaviour.Outcome Ret Memory Empty} :
    (sem p).final s o ↔ outcomeOf (step p s) = some o := Iff.rfl

/-- **RTL is deterministic**: one successor per state, one outcome per final
state, and a final state does not step. -/
theorem sem_deterministic (p : Prog R) : (sem p).Deterministic where
  step_unique _ _ _ ha hb := Step.deterministic ha hb
  final_unique _ _ _ h h' := by
    rw [sem_final_iff] at h h'
    rw [h] at h'
    exact Option.some.inj h'
  final_stop s _ h t ht := by
    have hs : step p s = .running t := ht
    rw [sem_final_iff, hs] at h
    simp [outcomeOf] at h

/-- **RTL has progress**: every state steps or shows a finite outcome, because
a stuck state shows `undefined`. -/
theorem sem_progress (p : Prog R) : (sem p).Progress := by
  intro s
  cases h : step p s with
  | running s' => exact .inl ⟨s', h⟩
  | returned vs m => exact .inr ⟨.returned (vs, m), by rw [sem_final_iff, h]; rfl, by simp⟩
  | trapped m => exact .inr ⟨.trapped m, by rw [sem_final_iff, h]; rfl, by simp⟩
  | stuck => exact .inr ⟨.undefined, by rw [sem_final_iff, h]; rfl, by simp⟩

/-- Every state has exactly one behaviour. -/
theorem beh_exists (p : Prog R) (s : State R) : ∃ o, (sem p).Beh s o :=
  Silmaril.Machine.Behaviour.Semantics.Beh.exists (sem_progress p) s

theorem beh_unique {p : Prog R} {s : State R} {o o' : Silmaril.Machine.Behaviour.Outcome Ret Memory Empty}
    (h : (sem p).Beh s o) (h' : (sem p).Beh s o') : o = o' :=
  Silmaril.Machine.Behaviour.Semantics.Beh.unique (sem_deterministic p) h h'

/-! ## Agreement with `Behaves` -/

theorem beh_returned_iff {p : Prog R} {s : State R} {vs : List Word} {m : Memory} :
    (sem p).Beh s (.returned (vs, m)) ↔ Behaves p s (.returned vs m) := by
  rw [Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨t, ht, hf⟩
    rw [sem_final_iff] at hf
    cases hs : step p t with
    | returned vs' m' =>
      rw [hs] at hf
      simp only [outcomeOf, Option.some.injEq, Outcome.returned.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨t, ht, hs⟩
    | _ => rw [hs] at hf; simp [outcomeOf] at hf
  · rintro ⟨t, ht, hf⟩
    exact ⟨t, ht, by rw [sem_final_iff, hf]; rfl⟩

theorem beh_trapped_iff {p : Prog R} {s : State R} {m : Memory} :
    (sem p).Beh s (.trapped m) ↔ Behaves p s (.trapped m) := by
  rw [Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨t, ht, hf⟩
    rw [sem_final_iff] at hf
    cases hs : step p t with
    | trapped m' =>
      rw [hs] at hf
      simp only [outcomeOf, Option.some.injEq, Outcome.trapped.injEq] at hf
      exact ⟨t, ht, hf ▸ hs⟩
    | _ => rw [hs] at hf; simp [outcomeOf] at hf
  · rintro ⟨t, ht, hf⟩
    exact ⟨t, ht, by rw [sem_final_iff, hf]; rfl⟩

theorem beh_undefined_iff {p : Prog R} {s : State R} :
    (sem p).Beh s .undefined ↔ Behaves p s .stuck := by
  rw [Semantics.beh_of_ne (by simp)]
  constructor
  · rintro ⟨t, ht, hf⟩
    rw [sem_final_iff] at hf
    cases hs : step p t with
    | stuck => exact ⟨t, ht, hs⟩
    | _ => rw [hs] at hf; simp [outcomeOf] at hf
  · rintro ⟨t, ht, hf⟩
    exact ⟨t, ht, by rw [sem_final_iff, hf]; rfl⟩

theorem beh_diverges_iff {p : Prog R} {s : State R} :
    (sem p).Beh s .diverges ↔ Diverges p s := Iff.rfl

/-- RTL has no faults and no resource exhaustion. -/
theorem not_beh_faulted {p : Prog R} {s : State R} {f : Empty} :
    ¬ (sem p).Beh s (.faulted f) := f.elim

theorem not_beh_exhausted {p : Prog R} {s : State R} : ¬ (sem p).Beh s .exhausted := by
  rw [Semantics.beh_of_ne (by simp)]
  rintro ⟨t, -, hf⟩
  rw [sem_final_iff] at hf
  cases hs : step p t <;> rw [hs] at hf <;> simp [outcomeOf] at hf

/-- **`Safe` is "does not get stuck".** -/
theorem safe_iff_not_stuck {p : Prog R} {s : State R} :
    (sem p).Safe s ↔ ¬ Behaves p s .stuck := not_congr beh_undefined_iff

end Silmaril.Machine.RTL

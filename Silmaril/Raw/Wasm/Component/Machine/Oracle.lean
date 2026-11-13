module

public import Silmaril.Wasm.Component.Reference.Machine.Oracle.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Effects

/-!
# Oracles: answering the choice points of the specification

The specification programs `Canon.P E σ` of the Canonical ABI (`definitions.py` at
component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF") resolve every nondeterministic choice (C1-C7 and the host choices E1 of
`Canon.ChoiceKind`; Concurrency.md §"Nondeterminism") through an `Oracle`. The machine asks
the oracle, checks the answer against `Canon.Allowed o.prof k r`, and stops when the answer is
not admissible or the oracle reports `failed`.

* `Oracle E` has a profile, a private state, and `answer : State → CStore E → (k : ChoiceKind)
  → k.Resp × State`; the component store is passed so that store-dependent policies (for
  example wasmtime `a7b4f29`'s scheduling, `Machine/Wasmtime.lean`) are oracles too.
* `Oracle.first prof`: the "first alternative" oracle: `earlyReturn` false (always block),
  pick index 0, identity shuffle, `cancelNow` true, `errCtxKeep` false, the error-context
  message unchanged, canonical NaNs, host pick 0.
* `Oracle.replay prof log`: replays a recorded list of `ChoiceRecord`s (a kind and its
  response). On a kind mismatch or an exhausted log it marks its state failed and answers with
  `rejectAnswer?` (a response that is not `Allowed`) when the kind has one.
* `Oracle.lcg seed`: a pseudo-random oracle (linear congruential generator, `nondet` profile):
  random booleans and picks, a random permutation by random insertion, and NaNs shaped like
  REF `random_nan_bits` (L1509-1514): random sign, quiet bit and payload over the full width,
  all-ones exponent, and one random fraction bit below the quiet bit set.

## Theorems

* `first_allowed`: every answer of `Oracle.first p` is `Allowed p`, for every profile `p` and
  kind `k`. `first_allowed_of_not_nan`: for a kind other than `nan`, the answer is `Allowed` in
  every profile `q`, whatever `p`. `first_deterministic_allowed`: the answers of
  `Oracle.first .deterministic` are admissible in `nondet` and `deterministic`.
* `rejectAnswer?_not_allowed`: the mismatch answers of `replay` are not admissible.
  `replay_answer_match` / `replay_answer_mismatch` describe a replay step;
  `replay_answer_mismatch_stops` / `replay_answer_exhausted_stops` combine them: a mismatch (or
  an exhausted log) sets `failed` and answers inadmissibly whenever the kind admits a rejection.
* `lcg_allowed`: every answer of `Oracle.lcg` is `Allowed .nondet`
  (`randomPerm_perm`: the random shuffle is a permutation of `range n`); on concrete seeds the
  NaN answers are checked to satisfy `ABI.RandomNaNBits` (not proved for all seeds).

## Design notes

* `Oracle.first` takes the profile (default `.deterministic`). An answer admissible in every
  profile does not exist for C7: `deterministic` requires the canonical NaN `0x7fc00000`, while
  `refStrict` requires the image of REF `random_nan_bits` (L1509), which excludes it. So
  `first_allowed` is stated for `Oracle.first p` in profile `p`; under `refStrict`, a NaN
  lowers to `randomNaN t` (`0x7fc00001` / `0x7ff8000000000001`). For every other kind the answer
  does not depend on the profile and is admissible in every profile.
* The error-context message answer (C6b) is the input message when it is a consistent REF
  string (the only answers `Allowed` admits), else the empty UTF-8 string.
* `Oracle` has an extra field `failed : State → Bool` (default: never). A replay mismatch cannot
  always be signalled by an inadmissible response, because `tickPick`, `syncLoopPick` and `host`
  admit every response in every profile (and `earlyReturn`, `cancelNow`, `errCtxKeep` every
  response outside `deterministic`); the executable machine (`step?`) must also stop when `o.failed
  o.state` after `ask`.

Not modelled or claimed: any machine behaviour, fairness or statistical properties
of `lcg`, or agreement of `lcg` with Python's `random` module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

namespace Oracle

variable {E : CoreEngine}

end Oracle

/-! ## The first-alternative oracle -/

section FirstLemmas

end FirstLemmas

/-- Every answer of `Oracle.first p` is admissible in profile `p`. -/
theorem first_allowed {E : CoreEngine} (p : ProfileKind) (k : ChoiceKind) (st : Unit)
    (s : CStore E) : Allowed p k (((Oracle.first (E := E) p).answer st s k).1) := by
  cases k with
  | earlyReturn _ => exact fun _ => rfl
  | tickPick _ => trivial
  | syncLoopPick _ => trivial
  | shuffle n => exact List.Perm.refl _
  | cancelNow => exact fun _ => rfl
  | errCtxKeep => exact fun _ => rfl
  | errCtxMessage m => exact keepMessage_allowed _ m
  | nan t x => exact firstNan_allowed p t x
  | host _ => trivial

/-- For every kind other than `nan`, the answer of `Oracle.first p` is admissible in every
profile `q`. -/
theorem first_allowed_of_not_nan {E : CoreEngine} (p q : ProfileKind) (k : ChoiceKind)
    (hk : ∀ t x, k ≠ .nan t x) (st : Unit) (s : CStore E) :
    Allowed q k (((Oracle.first (E := E) p).answer st s k).1) := by
  cases k with
  | earlyReturn _ => exact fun _ => rfl
  | tickPick _ => trivial
  | syncLoopPick _ => trivial
  | shuffle n => exact List.Perm.refl _
  | cancelNow => exact fun _ => rfl
  | errCtxKeep => exact fun _ => rfl
  | errCtxMessage m => exact keepMessage_allowed _ m
  | nan t x => exact absurd rfl (hk t x)
  | host _ => trivial

/-- The deterministic first oracle is admissible in `nondet` and in `deterministic`. -/
theorem first_deterministic_allowed {E : CoreEngine} (q : ProfileKind) (hq : q ≠ .refStrict)
    (k : ChoiceKind) (st : Unit) (s : CStore E) :
    Allowed q k (((Oracle.first (E := E) .deterministic).answer st s k).1) := by
  cases q with
  | nondet => exact (first_allowed .deterministic k st s).to_nondet
  | refStrict => exact absurd rfl hq
  | deterministic => exact first_allowed .deterministic k st s

/-! ### Tests: `Oracle.first` answers -/

section FirstTests

variable {E : CoreEngine} (s : CStore E)

example : ((Oracle.first (E := E)).answer () s (.earlyReturn .yield_)).1 = false := rfl
example : ((Oracle.first (E := E)).answer () s (.tickPick 3)).1 = (0 : Fin 4) := rfl
example : ((Oracle.first (E := E)).answer () s (.syncLoopPick 2)).1 = (0 : Fin 3) := rfl
example : ((Oracle.first (E := E)).answer () s (.shuffle 3)).1 = [0, 1, 2] := rfl
example : ((Oracle.first (E := E)).answer () s .cancelNow).1 = true := rfl
example : ((Oracle.first (E := E)).answer () s .errCtxKeep).1 = false := rfl
example : ((Oracle.first (E := E)).answer () s (.host 5)).1 = (0 : Fin 6) := rfl
example : ((Oracle.first (E := E)).answer () s (.errCtxMessage emptyStrVal)).1 =
    emptyStrVal := rfl
example : ((Oracle.first (E := E)).answer () s (.nan .f32 negQuietNaN32)).1 =
    (0x7fc00000#32 : BitVec FloatType.f32.width) := rfl
example : ((Oracle.first (E := E) .refStrict).answer () s (.nan .f32 negQuietNaN32)).1 =
    (0x7fc00001#32 : BitVec FloatType.f32.width) := rfl
example : ((Oracle.first (E := E) .nondet).answer () s (.nan .f32 1#32)).1 =
    (1#32 : BitVec FloatType.f32.width) := rfl

end FirstTests

/-! ## Replay -/

theorem replay_answer_match (prof : ProfileKind) (k : ChoiceKind) (r : k.Resp)
    (rest : List ChoiceRecord) :
    replayAnswer prof ⟨⟨k, r⟩ :: rest, false⟩ k = (r, ⟨rest, false⟩) := by
  simp [replayAnswer]

theorem replay_answer_mismatch (prof : ProfileKind) (k k' : ChoiceKind) (r : k'.Resp)
    (rest : List ChoiceRecord) (h : k' ≠ k) :
    (replayAnswer prof ⟨⟨k', r⟩ :: rest, false⟩ k).2.failed = true := by
  simp [replayAnswer, h]

theorem replay_answer_exhausted (prof : ProfileKind) (k : ChoiceKind) :
    (replayAnswer prof ⟨[], false⟩ k).2.failed = true := rfl

/-- Once failed, a replay stays failed. -/
theorem replay_answer_failed (prof : ProfileKind) (k : ChoiceKind) (log : List ChoiceRecord) :
    (replayAnswer prof ⟨log, true⟩ k).2.failed = true := by
  cases log with
  | nil => rfl
  | cons _ _ => rfl

private theorem isNaN_zero (t : FloatType) : ABI.isNaN t 0 = false := by cases t <;> decide

private theorem isNaN_canonicalNaN (t : FloatType) : ABI.isNaN t (ABI.canonicalNaN t) = true := by
  cases t <;> decide

private theorem canonicalNaN_ne_zero (t : FloatType) : ABI.canonicalNaN t ≠ 0 := by
  cases t <;> decide

private theorem one_ne_zero' (t : FloatType) : (1 : BitVec t.width) ≠ 0 := by
  cases t <;> decide

theorem nanReject_ne (t : FloatType) (x : BitVec t.width) (hx : ABI.isNaN t x = false) :
    nanReject t x ≠ x := by
  unfold nanReject
  simp only [hx, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i h; subst h; exact one_ne_zero' t
  · rename_i h; exact fun e => h e.symm

theorem nanReject_not_allowed (prof : ProfileKind) (t : FloatType) (x : BitVec t.width) :
    ¬ NanLower prof t x (nanReject t x) := by
  intro h
  have hs := (nanLower_nondet_iff.mp h.to_nondet)
  rw [ABI.scrambleNaN_false_iff] at hs
  rcases hs with ⟨hx, he⟩ | ⟨hx, hy⟩
  · exact nanReject_ne t x hx he
  · simp only [nanReject, hx, ↓reduceIte, isNaN_zero] at hy
    exact Bool.false_ne_true hy

/-- The mismatch answers of `replay` are not admissible. -/
theorem rejectAnswer?_not_allowed (prof : ProfileKind) (k : ChoiceKind) (r : k.Resp)
    (h : rejectAnswer? prof k = some r) : ¬ Allowed prof k r := by
  cases k with
  | earlyReturn _ =>
    simp only [rejectAnswer?] at h; split at h
    · cases h; rename_i hp; exact fun ha => Bool.true_eq_false.mp (ha hp)
    · cases h
  | tickPick _ => cases h
  | syncLoopPick _ => cases h
  | shuffle n =>
    simp only [rejectAnswer?, Option.some.injEq] at h
    subst h
    intro hp
    have := hp.length_eq
    simp only [List.length_singleton, List.length_range] at this
    have hm : n ∈ List.range n := hp.subset (List.mem_singleton_self n)
    simp at hm
  | cancelNow =>
    simp only [rejectAnswer?] at h; split at h
    · cases h; rename_i hp; exact fun ha => Bool.false_ne_true (ha hp)
    · cases h
  | errCtxKeep =>
    simp only [rejectAnswer?] at h; split at h
    · cases h; rename_i hp; exact fun ha => Bool.true_eq_false.mp (ha hp)
    · cases h
  | errCtxMessage _ =>
    simp only [rejectAnswer?, Option.some.injEq] at h
    subst h
    intro ⟨hc, _⟩
    revert hc
    decide
  | nan t x =>
    simp only [rejectAnswer?, Option.some.injEq] at h
    subst h
    exact nanReject_not_allowed prof t x
  | host _ => cases h

/-- A replay mismatch stops the machine: the state is failed, and the answer is inadmissible
whenever `k` has an inadmissible response. -/
theorem replay_answer_mismatch_stops (prof : ProfileKind) (k k' : ChoiceKind) (r : k'.Resp)
    (rest : List ChoiceRecord) (h : k' ≠ k) :
    (replayAnswer prof ⟨⟨k', r⟩ :: rest, false⟩ k).2.failed = true ∧
      ∀ r₀, rejectAnswer? prof k = some r₀ →
        ¬ Allowed prof k (replayAnswer prof ⟨⟨k', r⟩ :: rest, false⟩ k).1 := by
  refine ⟨replay_answer_mismatch prof k k' r rest h, fun r₀ hr => ?_⟩
  have e : (replayAnswer prof ⟨⟨k', r⟩ :: rest, false⟩ k).1 = r₀ := by
    simp [replayAnswer, h, hr]
  rw [e]
  exact rejectAnswer?_not_allowed prof k r₀ hr

/-- An exhausted replay stops the machine (as `replay_answer_mismatch_stops`). -/
theorem replay_answer_exhausted_stops (prof : ProfileKind) (k : ChoiceKind) :
    (replayAnswer prof ⟨[], false⟩ k).2.failed = true ∧
      ∀ r₀, rejectAnswer? prof k = some r₀ →
        ¬ Allowed prof k (replayAnswer prof ⟨[], false⟩ k).1 := by
  refine ⟨rfl, fun r₀ hr => ?_⟩
  have e : (replayAnswer prof ⟨[], false⟩ k).1 = r₀ := by
    simp [replayAnswer, hr]
  rw [e]
  exact rejectAnswer?_not_allowed prof k r₀ hr

/-! ### Tests: replay -/

section ReplayTests

variable {E : CoreEngine} (s : CStore E)

example : ((Oracle.replay (E := E) sampleLog).answer ⟨sampleLog, false⟩ s
    (.earlyReturn .yield_)).1 = true := rfl

example : ((Oracle.replay (E := E) sampleLog).answer ⟨sampleLog.drop 1, false⟩ s
    (.tickPick 2)).1 = (2 : Fin 3) := rfl

example : ((Oracle.replay (E := E) sampleLog).answer ⟨sampleLog, false⟩ s
    .cancelNow).2.failed = true := rfl

example : ((Oracle.replay (E := E) sampleLog .deterministic).answer ⟨sampleLog, false⟩ s
    (.shuffle 2)).1 = [2] := rfl

end ReplayTests

/-! ## A pseudo-random oracle -/

theorem randomPerm_perm (n s : Nat) : (randomPerm n s).1.Perm (List.range n) := by
  induction n with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simp only [randomPerm]
    refine (List.perm_insertIdx n _ ?_).trans ?_
    · exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
    · rw [List.range_succ]
      exact (ih.cons n).trans (List.perm_append_singleton n _).symm

/-- Every answer of `lcg` is admissible in `nondet`. -/
theorem lcg_allowed {E : CoreEngine} (seed : Nat) (k : ChoiceKind) (st : Nat) (s : CStore E) :
    Allowed .nondet k (((Oracle.lcg (E := E) seed).answer st s k).1) := by
  cases k with
  | earlyReturn _ => exact fun h => nomatch h
  | tickPick _ => trivial
  | syncLoopPick _ => trivial
  | shuffle n => exact randomPerm_perm n st
  | cancelNow => exact fun h => nomatch h
  | errCtxKeep => exact fun h => nomatch h
  | errCtxMessage m => exact keepMessage_allowed _ m
  | nan t x =>
    show NanLower .nondet t x (lcgNan t x st).1
    simp only [NanLower, lcgNan]
    split
    · split
      · assumption
      · exact isNaN_canonicalNaN t
    · rfl
  | host _ => trivial

/-! ### Tests: lcg -/

example : (randomPerm 5 42).1.Perm (List.range 5) := by decide +kernel
example : ((randomPerm 4 7).1.length) = 4 := by decide +kernel

/-- The raw `lcgNaNBits` are REF `random_nan_bits` outputs on sample seeds, and cover a
negative signalling NaN (sign set, quiet bit clear). -/
example : ∀ s ∈ [0, 1, 7, 42, 1000, 123456789],
    ABI.isNaN .f32 (lcgNaNBits .f32 s).1 = true ∧
    ABI.isNaN .f64 (lcgNaNBits .f64 s).1 = true := by decide +kernel
example : ABI.RandomNaNBits .f64 (lcgNaNBits .f64 42).1 := by decide +kernel
example : ABI.RandomNaNBits .f32 (lcgNaNBits .f32 42).1 := by decide +kernel
example :
    (lcgNaNBits .f32 11).1.getLsbD 31 = true ∧ (lcgNaNBits .f32 11).1.getLsbD 22 = false := by
  decide +kernel
example :
    (lcgNaNBits .f64 7).1.getLsbD 63 = true ∧ (lcgNaNBits .f64 7).1.getLsbD 51 = false := by
  decide +kernel

end Silmaril.Wasm.Component.Machine

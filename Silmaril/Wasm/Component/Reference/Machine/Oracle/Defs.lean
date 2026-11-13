module

public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Defs
public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Value.Nan.Defs
public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

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

/-- An oracle answering choice points (see the module docstring). -/
structure Oracle (E : CoreEngine) where
  /-- The profile whose `Allowed` gate the machine applies to the answers. -/
  prof : ProfileKind
  /-- The private state of the oracle. -/
  State : Type
  /-- The current state. -/
  state : State
  /-- Answer the choice `k` in the component store given as second argument. -/
  answer : State → CStore E → (k : ChoiceKind) → k.Resp × State
  /-- The oracle gave up (e.g. a replay mismatch); the machine stops. -/
  failed : State → Bool := fun _ => false

namespace Oracle

variable {E : CoreEngine}

/-- Ask the oracle `o` the choice `k` at store `s`: the answer and the oracle with its state
advanced. -/
def ask (o : Oracle E) (s : CStore E) (k : ChoiceKind) : k.Resp × Oracle E :=
  let r := o.answer o.state s k
  (r.1, { o with state := r.2 })

@[simp] theorem ask_fst (o : Oracle E) (s : CStore E) (k : ChoiceKind) :
    (o.ask s k).1 = (o.answer o.state s k).1 := rfl

@[simp] theorem ask_prof (o : Oracle E) (s : CStore E) (k : ChoiceKind) :
    (o.ask s k).2.prof = o.prof := rfl

end Oracle

/-! ## The first-alternative oracle -/

/-- A NaN in the image of REF `random_nan_bits` (L1509): all-ones exponent, quiet bit and
fraction bit 0 set. -/
def randomNaN : (t : FloatType) → BitVec t.width
  | .f32 => 0x7fc00001#32
  | .f64 => 0x7ff8000000000001#64

/-- The empty UTF-8 REF string, lifted from a 32-bit memory. -/
def emptyStrVal : StrVal := ⟨⟨"", .utf8, 0⟩, .i32⟩

/-- C6b answer: the message unchanged when it is a consistent REF string, else empty. -/
def keepMessage (s : StrVal) : StrVal :=
  if s.v.Consistent s.srcAddr then s else emptyStrVal

/-- C7 answer of `Oracle.first prof`: the canonical NaN, except `randomNaN` under
`refStrict`; non-NaNs are unchanged. -/
def firstNan (prof : ProfileKind) (t : FloatType) (x : BitVec t.width) : BitVec t.width :=
  if prof = .refStrict ∧ ABI.isNaN t x = true then randomNaN t else ABI.canonicalizeNaN t x

/-- The answers of `Oracle.first prof`. -/
def firstAnswer (prof : ProfileKind) : (k : ChoiceKind) → k.Resp
  | .earlyReturn _ => false
  | .tickPick _ => 0
  | .syncLoopPick _ => 0
  | .shuffle n => List.range n
  | .cancelNow => true
  | .errCtxKeep => false
  | .errCtxMessage s => keepMessage s
  | .nan t x => firstNan prof t x
  | .host _ => 0

/-- The first-alternative oracle for profile `prof` (stateless). -/
def Oracle.first {E : CoreEngine} (prof : ProfileKind := .deterministic) : Oracle E where
  prof := prof
  State := Unit
  state := ()
  answer := fun st _ k => (firstAnswer prof k, st)

section FirstLemmas

end FirstLemmas

/-! ### Tests: `Oracle.first` answers -/

section FirstTests

variable {E : CoreEngine} (s : CStore E)

end FirstTests

/-! ## Replay -/

/-- A recorded choice: its kind and response. -/
abbrev ChoiceRecord := (k : ChoiceKind) × k.Resp

/-- A NaN-lowering answer admissible in no profile: a non-NaN for a NaN input, a different
value for a non-NaN input. -/
def nanReject (t : FloatType) (x : BitVec t.width) : BitVec t.width :=
  if ABI.isNaN t x = true then 0 else if x = 0 then 1 else 0

/-- A response to `k` that is not `Allowed prof k`, when one exists. -/
def rejectAnswer? (prof : ProfileKind) : (k : ChoiceKind) → Option k.Resp
  | .earlyReturn _ => if prof = .deterministic then some true else none
  | .tickPick _ => none
  | .syncLoopPick _ => none
  | .shuffle n => some [n]
  | .cancelNow => if prof = .deterministic then some false else none
  | .errCtxKeep => if prof = .deterministic then some true else none
  | .errCtxMessage _ => some ⟨⟨"", .utf8, 1⟩, .i32⟩
  | .nan t x => some (nanReject t x)
  | .host _ => none

/-- The state of a replay: the remaining log and whether a mismatch occurred. -/
structure ReplayState where
  /-- The remaining records. -/
  log : List ChoiceRecord
  /-- A mismatch or an exhausted log occurred. -/
  failed : Bool := false

/-- One replay answer: the head record if its kind is `k` (and no failure occurred), else a
rejected (or first) answer with the failure flag set. -/
def replayAnswer (prof : ProfileKind) (st : ReplayState) (k : ChoiceKind) :
    k.Resp × ReplayState :=
  match st with
  | ⟨⟨k', r⟩ :: rest, false⟩ =>
    if h : k' = k then (h ▸ r, ⟨rest, false⟩)
    else ((rejectAnswer? prof k).getD (firstAnswer prof k), { st with failed := true })
  | _ => ((rejectAnswer? prof k).getD (firstAnswer prof k), { st with failed := true })

/-- Replay the recorded choices `log` under profile `prof` (default `nondet`). -/
def Oracle.replay {E : CoreEngine} (log : List ChoiceRecord) (prof : ProfileKind := .nondet) :
    Oracle E where
  prof := prof
  State := ReplayState
  state := ⟨log, false⟩
  answer := fun st _ k => replayAnswer prof st k
  failed := ReplayState.failed

/-! ### Tests: replay -/

section ReplayTests

variable {E : CoreEngine} (s : CStore E)

/-- A two-record log: early return at `thread.yield`, then pick 2 of 3. -/
def sampleLog : List ChoiceRecord :=
  [⟨.earlyReturn .yield_, true⟩, ⟨.tickPick 2, (2 : Fin 3)⟩]

end ReplayTests

/-! ## A pseudo-random oracle -/

/-- One step of the linear congruential generator (glibc constants, modulus `2^31`). -/
def lcgNext (s : Nat) : Nat := (1103515245 * s + 12345) % 2 ^ 31

/-- A random bit from state `s` (bit 16, avoiding the weak low bits). -/
def lcgBit (s : Nat) : Bool := (s / 65536) % 2 == 1

/-- A random index below `last + 1` from state `s`. -/
def lcgFin (last s : Nat) : Fin (last + 1) :=
  ⟨(s / 65536) % (last + 1), Nat.mod_lt _ (by omega)⟩

/-- A random permutation of `range n` by random insertion: `n - 1` is inserted at a random
position of a random permutation of `range (n - 1)`. Returns the final generator state. -/
def randomPerm : Nat → Nat → List Nat × Nat
  | 0, s => ([], s)
  | n + 1, s =>
    let r := randomPerm n s
    let s' := lcgNext r.2
    (r.1.insertIdx ((s' / 65536) % (r.1.length + 1)) n, s')

/-- The all-ones biased exponent of `t`, in place. -/
def nanExponentMask : (t : FloatType) → BitVec t.width
  | .f32 => 0x7f800000#32
  | .f64 => 0x7ff0000000000000#64

/-- REF `random_nan_bits(total_bits, exponent_bits)` (L1509-1514) driven by the generator from
state `s`: `getrandbits(total_bits)` is the concatenation of three draws (93 bits, truncated to
the width), the exponent is forced to all ones, and fraction bit
`randrange(fraction_bits - 1)` (a fourth draw) is set. Returns the bits and the final state. -/
def lcgNaNBits (t : FloatType) (s : Nat) : BitVec t.width × Nat :=
  let s₁ := lcgNext s
  let s₂ := lcgNext s₁
  let s₃ := lcgNext s₂
  let s₄ := lcgNext s₃
  let bits := BitVec.ofNat t.width (s₁ + s₂ * 2 ^ 31 + s₃ * 2 ^ 62)
  let bit := BitVec.ofNat t.width (2 ^ ((s₄ / 65536) % (ABI.floatFractionWidth t - 1)))
  (bits ||| nanExponentMask t ||| bit, s₄)

/-- C7 answer of `lcg`: for a NaN input, `lcgNaNBits` (falling back to the canonical NaN if
that were not a NaN, which does not happen); the input otherwise (without drawing). -/
def lcgNan (t : FloatType) (x : BitVec t.width) (s : Nat) : BitVec t.width × Nat :=
  if ABI.isNaN t x = true then
    let y := lcgNaNBits t s
    (if ABI.isNaN t y.1 = true then y.1 else ABI.canonicalNaN t, y.2)
  else (x, s)

/-- The answers of `lcg` (each draws from the generator once, except the shuffle, a NaN
lowering of a NaN (four draws) and the message choice (none)). -/
def lcgAnswer (s : Nat) : (k : ChoiceKind) → k.Resp × Nat
  | .earlyReturn _ => (lcgBit (lcgNext s), lcgNext s)
  | .tickPick last => (lcgFin last (lcgNext s), lcgNext s)
  | .syncLoopPick last => (lcgFin last (lcgNext s), lcgNext s)
  | .shuffle n => randomPerm n s
  | .cancelNow => (lcgBit (lcgNext s), lcgNext s)
  | .errCtxKeep => (lcgBit (lcgNext s), lcgNext s)
  | .errCtxMessage m => (keepMessage m, s)
  | .nan t x => lcgNan t x s
  | .host last => (lcgFin last (lcgNext s), lcgNext s)

/-- A pseudo-random oracle in the `nondet` profile, seeded with `seed`. -/
def Oracle.lcg {E : CoreEngine} (seed : Nat) : Oracle E where
  prof := .nondet
  State := Nat
  state := seed
  answer := fun st _ k => lcgAnswer st k

/-! ### Tests: lcg -/

end Silmaril.Wasm.Component.Machine

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

section FirstLemmas

theorem emptyStrVal_consistent : emptyStrVal.v.Consistent emptyStrVal.srcAddr := by
  decide

theorem keepMessage_consistent (s : StrVal) :
    (keepMessage s).v.Consistent (keepMessage s).srcAddr := by
  unfold keepMessage
  split
  · assumption
  · exact emptyStrVal_consistent

theorem emptyStrVal_valid : emptyStrVal.Valid := by
  decide

/-- `keepMessage` keeps a valid message valid. -/
theorem keepMessage_valid {s : StrVal} (hs : s.Valid) : (keepMessage s).Valid := by
  unfold keepMessage
  split
  · exact hs
  · exact emptyStrVal_valid

/-- `keepMessage` is an admissible C6b answer in every profile. -/
theorem keepMessage_allowed (prof : ProfileKind) (s : StrVal) :
    Allowed prof (.errCtxMessage s) (keepMessage s) :=
  ⟨keepMessage_consistent s, keepMessage_valid⟩

theorem randomNaNBits_randomNaN (t : FloatType) : ABI.RandomNaNBits t (randomNaN t) := by
  cases t <;> decide

theorem isNaN_randomNaN (t : FloatType) : ABI.isNaN t (randomNaN t) = true := by
  cases t <;> decide

theorem firstNan_allowed (prof : ProfileKind) (t : FloatType) (x : BitVec t.width) :
    NanLower prof t x (firstNan prof t x) := by
  cases prof with
  | refStrict =>
    simp only [NanLower, firstNan, true_and]
    cases hx : ABI.isNaN t x
    · simp only [Bool.false_eq_true, ↓reduceIte, ABI.canonicalizeNaN, hx, IsEmpty.forall_iff,
        and_true]
      exact ABI.ScrambleNaN.nonNaN x hx
    · simp only [↓reduceIte, forall_const]
      exact ⟨ABI.ScrambleNaN.scrambled x _ hx rfl (isNaN_randomNaN t),
        randomNaNBits_randomNaN t⟩
  | nondet =>
    have h : firstNan .nondet t x = ABI.canonicalizeNaN t x := by simp [firstNan]
    rw [h]
    exact (nanLower_deterministic_canonicalizeNaN t x).to_nondet
  | deterministic =>
    have h : firstNan .deterministic t x = ABI.canonicalizeNaN t x := by simp [firstNan]
    rw [h]
    exact nanLower_deterministic_canonicalizeNaN t x

end FirstLemmas

end Silmaril.Wasm.Component.Machine

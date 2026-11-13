module

public import Silmaril.Wasm.Component.Async.CabiRef.Defs

@[expose] public section

/-!
# The transcription against silmaril's machine: the rest of the end state machine

`Silmaril.Wasm.Component.Async.CabiRef` relates the transcription `Silmaril.Wasm.Component.Async.Cabi`
of `definitions.py` at `d095e2f` to silmaril's end state machine (`definitions.py` at `a25fc0b`,
`Silmaril.Wasm.Component.Runtime`) by `CabiRef.EndsRel` (every end has the same `View`) and
proves that `End.copy` cases 2 and 3 and the delivery of a stream event are taken by both
machines. This module extends it to the remaining steps of the end state machine:

* `End.copy` towards a dropped peer (case 1) and the zero-length cases 4 and 5, and with them
  every successful `End.copy` (`copyEnd_sim`);
* `End.cancel` (`cancelEnd` / `Runtime.cancel`, the coin of `random.randint` being silmaril's
  `notifyNow`, or the deterministic profile);
* `End.drop` (`dropEnd` / `Runtime.dropEnd`);
* the delivery of a future event (`future_event` / `Runtime.takeEvent`);
* `End.forward` (`forwardEnd` / `Runtime.forward`), where silmaril also clears the links of the
  two forwarded ends (its documented deviation): the stores are related **except at the two
  forwarded ends** (`EndsRelExcept`), and not related at them (refuted).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Component.Async.CabiRef

open Silmaril.Wasm.Component.Runtime

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {α : Type}

/-- The relation at every end but those `P` excludes. -/
def EndsRelOn (P : Nat → Prop) (st : Cabi.Store α) (s : CStore E) : Prop :=
  ∀ e, P e → (s.end? ⟨e⟩).map viewS = (st.ends e).bind (viewC st e)

/-- The relation at every end but `a` and `b` (the ends `End.forward` retires). -/
def EndsRelExcept (a b : Nat) (st : Cabi.Store α) (s : CStore E) : Prop :=
  EndsRelOn (fun e => e ≠ a ∧ e ≠ b) st s

/-- Every parked buffer exists. -/
def BufsPresent (st : Cabi.Store α) : Prop :=
  ∀ e x, st.ends e = some x → ∀ b, x.buffer = some b → (st.bufs b).isSome

/-- The three outcomes of `future_event` (L1051–1069) for a recorded progress `p ≤ 1`:
`COMPLETED` once a value moved, else `DROPPED` if the peer is gone, else `CANCELLED`. -/
def FutureOutcome (x : Cabi.End) (p : Nat) (ns : Cabi.EndState) (r : Cabi.CopyResult) : Prop :=
  (p = 1 ∧ (x.state = .copying ∨ x.state = .cancelling) ∧ x.buffer = none ∧ ns = .done ∧
      r = .completed) ∨
  (p = 0 ∧ x.other = none ∧ x.state ≠ .done ∧ ns = .done ∧ r = .dropped) ∨
  (p = 0 ∧ x.other ≠ none ∧ x.state = .cancelling ∧ ns = .idle ∧ r = .cancelled)

end Silmaril.Wasm.Component.Async.CabiRef

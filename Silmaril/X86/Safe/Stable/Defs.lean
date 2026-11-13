module

public import Silmaril.X86.Safe.Defs
public import Silmaril.X86.Sep.Extra.Defs

/-!
# Stable triples: the frame survives every intermediate state

A triple of `Sep/Spec` (`Sep.Triple`) or `Safe` (`STriple`) only promises that the frame
`F` holds again at the *final* state: a function may overwrite a location of the frame and
restore it before it returns (`push rbp; mov rbp, rsp; …; pop rbp` does this to the
callee-saved `rbp`). That is invisible to a sequential caller, but not to a second thread,
a signal handler, or an interrupted run that is inspected half way. A **stable** triple
promises that, at every intermediate state, the frame still holds of *part* of the state:
`(strue ∗ F) (toFrag mk)`.

This file has no relational
safety (`SafeR`) and no `graph` of a step function: `RelIsa` (with an explicit
`Res.stop`) is the only nondeterministic machine notion, so this file has **stable triples only**.
`strue` is `Sep.strue` (`Sep/Extra`).

* `Unchanged h m mk`: every location outside the domain of the fragment `h` holds the same
  value in `mk` as in `m`. It is the locality side condition of `Sep.Triple.of_local`, and
  the per-state condition from which a run gives a stable triple (`TripleS.of_local`).
* `TripleS step P Q`: the stable total triple. There is a run of `n` steps to a state where
  `Q ∗ F` holds, and `strue ∗ F` holds at every state of the run before it.
* `SafeNS step S Q n m`: step-indexed partial correctness that also checks `S` at every
  state it passes before it reaches `Q`.
* `STripleS step n P Q`: the stable step-indexed triple, `SafeNS` with `S = strue ∗ F`.

**Why `SafeNS`.** A simpler `STripleS` would be `SafeN … ∧ ∀ k ≤ n, ∀ mk,
run step k m = some mk → (strue ∗ F) (toFrag mk)`. That asks for stability for `n` steps
whatever happens after `Q` is reached (after a function returns, the machine runs the
caller's code, about which a callee's triple knows nothing), so it is unprovable for a
function triple with a large index. `SafeNS` interleaves the stability check with the safety
recursion and stops checking once `Q` holds.

The theorems are in `Safe/Stable/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Safe

open Silmaril.X86 (MState)
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Sep

/-- Every location outside the domain of `h` holds the same value in `mk` as in `m`. -/
def Unchanged (h : Frag) (m mk : MState) : Prop :=
  ∀ l, h l = none → toFrag mk l = toFrag m l

/-- Every `step` step is a `step'` step. -/
def Refines (step step' : MState → Option MState) : Prop :=
  ∀ {m m' : MState}, step m = some m' → step' m = some m'

variable (step : MState → Option MState)

/-- **Stable total triple**: the frame survives every intermediate state, not only the
last. -/
def TripleS (P Q : SProp) : Prop :=
  ∀ (F : SProp) (m : MState), (P ∗ F) (toFrag m) →
    ∃ n m', run step n m = some m' ∧ (Q ∗ F) (toFrag m') ∧
      ∀ k < n, ∀ mk, run step k m = some mk → (strue ∗ F) (toFrag mk)

/-- **Step-indexed safety with a state invariant**: within `n` steps the machine reaches `Q`
without getting stuck, and every state it passes before that satisfies `S`. -/
def SafeNS (S Q : MState → Prop) : Nat → MState → Prop
  | 0, _ => True
  | n + 1, m => Q m ∨ (S m ∧ ∃ m', step m = some m' ∧ SafeNS S Q n m')

/-- **Stable step-indexed triple** (partial; the link-logic shape). -/
def STripleS (n : Nat) (P Q : SProp) : Prop :=
  ∀ (F : SProp) (m : MState), (P ∗ F) (toFrag m) →
    SafeNS step (fun mk => (strue ∗ F) (toFrag mk)) (fun m' => (Q ∗ F) (toFrag m')) n m

end Silmaril.X86.Safe

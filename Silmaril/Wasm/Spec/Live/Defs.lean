module

public import Silmaril.Wasm.Spec.Wasm.Thms
public import Silmaril.Wasm.Spec.Temporal.Thms

@[expose] public section

/-!
# Liveness grounded in Core 3.0 divergence: definitions

The divergence-observing semantics `wasmDivSem P` records, after a play where the pending export
call may run forever host-free, the event `ret f .diverges`. Its maximal behaviours (the reading
of `ltlMax`) are therefore the right models for liveness. This topic ties them to the Core
predicate `Diverges` of silmaril-lean, at every profile:

* `Live.isCall j`, `Live.isRetOk j ok`: atoms "export `j` is called", "export `j` returns a
  result satisfying `ok`".
* `Live.responds j ok`: the LTL response formula `□ (call j → ◇ ret-ok j)`, "every call of `j`
  is eventually answered by a result satisfying `ok`"; `Live.terminates j` is the Wasm instance
  with `ok := (· ≠ .diverges)`.
* `Live.DivWitness T j a bad`: a maximal behaviour of the trace set `T` in which `j` is called on
  `a` and never returns a result outside `bad`: either a maximal finite trace whose returns all
  satisfy `bad`, or an infinite limit with no return at all (infinite hidden chatter with the
  environment).
* `Live.Total K`: the environment answers every import call (it never diverges itself). Liveness
  of the program is only meaningful against such environments: an import call that is never
  answered is the environment's divergence, not the program's.

Theorems in `Silmaril.Wasm.Spec.Live.Thms`. A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec.Live

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {Ty A R : Type}

/-- The event is a call of export `j`. -/
def isCall {X : Iface Ty} (j : X.Exp) : PosPred A R X := fun _ e => ∃ a, e = Event.call j a

/-- The event is a return of export `j` with a result satisfying `ok`. -/
def isRetOk {X : Iface Ty} (j : X.Exp) (ok : R → Prop) : PosPred A R X :=
  fun _ e => ∃ r, ok r ∧ e = Event.ret j r

/-- **The response formula** `□ (call j → ◇ ret-ok j)`: every call of `j` is eventually answered
by a result satisfying `ok`. -/
def responds {X : Iface Ty} (j : X.Exp) (ok : R → Prop) : LTLFm A R X :=
  LTL.alw (LTL.imp (LTL.atom (isCall j)) (LTL.ev (LTL.atom (isRetOk j ok))))

/-- **Termination of export `j`** (Wasm): every call of `j` eventually returns a behaviour other
than `diverges`. -/
abbrev terminates {X : WIface} (j : X.Exp) : LTLFm (List Val) (Behaviour Val) X :=
  responds j (· ≠ .diverges)

/-- A maximal behaviour of `T` calling `j` on `a` whose returns all satisfy `bad`: a maximal
finite trace, or an infinite limit with no return. -/
def DivWitness {X : Iface Ty} (T : Set (List (Event A R X))) (j : X.Exp) (a : A)
    (bad : R → Prop) : Prop :=
  (∃ t, Maximal T t ∧ Event.call j a ∈ t ∧ ∀ j' r, Event.ret j' r ∈ t → bad r) ∨
    (∃ w ∈ limits T, (∃ k, w k = Event.call j a) ∧ ∀ k j' r, w k ≠ Event.ret j' r)

/-- The environment answers every question. -/
def Total {E : Sig.{0}} (K : Env E) : Prop := ∀ e, ∃ w, K.Answers e w

/-- The environment that answers every import call by trapping (total). -/
def trapEnv (ts : List FnType) : Env (ifaceSig ts) := fun _ => some .trap

end Silmaril.Wasm.Spec.Live

module

public import Silmaril.Wasm.Behaviour.Relations
public import Silmaril.Machine.Behaviour.Outcome

/-!
# Wasm behaviours as machine outcomes: definitions

silmaril-lean has two vocabularies for comparing runs. `Silmaril.Wasm.Behaviour.Relations`
defines four relations on Wasm behaviours by hand (`=`, `TrapRefines`, `TrapDiv`,
`TrapRefinesDiv`). `Silmaril.Machine.Behaviour.Outcome` defines one relation
`Outcome.Rel m ob` on machine outcomes, parametrised by a `Mode` (failure and exhaustion axes)
and an observation `Obs`. This topic maps the first into the second.

* `toOutcome`: a return is `returned`, a **trap is the resource outcome `exhausted`** (trap
  insertion is what `Mode.exhaustion = .allowed` permits: an `exhausted` target implements every
  source outcome), an escaping Core 3.0 exception is `trapped` with its address, divergence is
  `diverges`. It is injective.
* `toOutcomeDiv`: the coarsening that also sends divergence to `exhausted`, the quotient map
  by `TrapDiv`.

The theorems are in `Silmaril.Wasm.Outcome.Thms`. Ported from an earlier development
`Silmaril/Wasm/Behaviour/ToOutcome.lean` (see `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Outcome

open Silmaril.Wasm (Behaviour)
open Silmaril.Machine.Behaviour (Outcome)

universe u

variable {V : Type u}

/-- A Wasm behaviour as a machine outcome; a trap is `exhausted`. -/
def toOutcome : Behaviour V → Outcome (List V) Nat Empty
  | .returns vs => .returned vs
  | .traps => .exhausted
  | .throws a => .trapped a
  | .diverges => .diverges

/-- The coarse embedding: trap and divergence are both `exhausted`. -/
def toOutcomeDiv : Behaviour V → Outcome (List V) Nat Empty
  | .returns vs => .returned vs
  | .traps => .exhausted
  | .throws a => .trapped a
  | .diverges => .exhausted

@[simp] theorem toOutcome_returns (vs : List V) :
    toOutcome (.returns vs) = .returned vs := rfl

@[simp] theorem toOutcome_traps : toOutcome (.traps : Behaviour V) = .exhausted := rfl

@[simp] theorem toOutcome_throws (a : Nat) :
    toOutcome (.throws a : Behaviour V) = .trapped a := rfl

@[simp] theorem toOutcome_diverges : toOutcome (.diverges : Behaviour V) = .diverges := rfl

@[simp] theorem toOutcomeDiv_returns (vs : List V) :
    toOutcomeDiv (.returns vs) = .returned vs := rfl

@[simp] theorem toOutcomeDiv_traps : toOutcomeDiv (.traps : Behaviour V) = .exhausted := rfl

@[simp] theorem toOutcomeDiv_throws (a : Nat) :
    toOutcomeDiv (.throws a : Behaviour V) = .trapped a := rfl

@[simp] theorem toOutcomeDiv_diverges :
    toOutcomeDiv (.diverges : Behaviour V) = .exhausted := rfl

end Silmaril.Wasm.Outcome

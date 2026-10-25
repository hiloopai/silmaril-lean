module

public import Silmaril.Wasm.Behaviour.Semantics.V2.Defs
import Silmaril.Proofs.Wasm.Behaviour.Semantics.V2

/-!
# The behaviours of WebAssembly 2.0

The construction of `Silmaril/Wasm/Behaviour/Semantics/V1.lean`, over the 2.0
machine. Two differences with V1, both forced by the 2.0 development:

* the reduction relation is indexed by a **numerics profile** `P`, which fixes
  the NaN propagation sets and the nondeterministic failure of `memory.grow`, so
  `behavioursOf` takes `P` as well. Fixing a profile is part of fixing the
  semantics, not of choosing a configuration;
* a terminal configuration is recognised by `c'.code = r.toAdmin` rather than by
  a separate `result` function; `Result.toAdmin` is the 2.0 spelling of the same
  `$lift_result` inclusion.

Values are `V2.Execution.Val` (numbers, vectors and references). This is an
independent 2.0 reduction relation, not a restriction of the 3.0 relation.
Cross-version execution simulations are not part of this release; the
syntax/validation embeddings have their own contracts. See
`docs/projects/wasm-semantics.md`.

2.0 has no exception handling, so `Behaviour.throws` is never observed
(`throws_not_mem_behavioursOf`).
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- Divergence is observed exactly when the configuration has an infinite
trace. -/
@[simp] theorem diverges_mem_behavioursOf_iff {P : Profile} {host : HostSemantics H}
    {c : Config H} :
    (Behaviour.diverges : Behaviour Val) ∈ behavioursOf P host c ↔ Diverges P host c :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V2.diverges_mem_behavioursOf_iff

/-! ## Elimination -/

/-- Every terminating observed behaviour comes from a finite run to a terminal
configuration. -/
theorem exists_result_of_mem {P : Profile} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Val} (mem : b ∈ behavioursOf P host c) (ne : b ≠ .diverges) :
    ∃ (c' : Config H) (r : Result),
      Steps P host c c' ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V2.exists_result_of_mem mem ne

/-- The `Behaviour.Terminates` phrasing of `exists_result_of_mem`. -/
theorem terminates_of_mem {P : Profile} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Val} (mem : b ∈ behavioursOf P host c) (term : b.Terminates) :
    ∃ (c' : Config H) (r : Result),
      Steps P host c c' ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour :=
  exists_result_of_mem mem (by rintro rfl; exact absurd term (by simp))

/-! ## Monotonicity along a run -/

/-- Divergence is preserved backwards along a finite run. -/
theorem diverges_of_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps P host c c') (div : Diverges P host c') : Diverges P host c :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V2.diverges_of_steps steps div

/-- Behaviours accumulate backwards along a run. -/
theorem behavioursOf_mono_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps P host c c') : behavioursOf P host c' ⊆ behavioursOf P host c :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V2.behavioursOf_mono_steps steps

/-! ## Range -/

/-- Wasm 2.0 has no exception handling, so it never throws. -/
theorem throws_not_mem_behavioursOf {P : Profile} {host : HostSemantics H} {c : Config H}
    (a : Nat) : (Behaviour.throws a : Behaviour Val) ∉ behavioursOf P host c :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V2.throws_not_mem_behavioursOf a

/-- The same, at an entry point. -/
theorem throws_not_mem_behaviours {P : Profile} {host : HostSemantics H} {s : Store H}
    {a : FuncAddr} {vs : List Val} (e : Nat) :
    (Behaviour.throws e : Behaviour Val) ∉ behaviours P host s a vs :=
  throws_not_mem_behavioursOf e

/-- Every observed behaviour is a return, a trap or divergence. -/
theorem mem_behavioursOf_cases {P : Profile} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Val} (mem : b ∈ behavioursOf P host c) :
    (∃ vs, b = .returns vs) ∨ b = .traps ∨ b = .diverges :=
  Silmaril.Proofs.Wasm.Behaviour.Semantics.V2.mem_behavioursOf_cases mem

end Silmaril.Wasm.V2.Execution

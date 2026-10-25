module

public import Silmaril.Wasm.Behaviour.Adapters.Runtime
public import Silmaril.Wasm.V1.Execution.Instantiation

/-!
# The behaviours of WebAssembly 1.0

`behavioursOf host c` is the set of observable outcomes of the configuration
`c`: one `r.toBehaviour` for every finite run of `c` to a configuration whose
code is the result `r`, plus `diverges` exactly when `c` has an infinite
reduction trace. The semantics is nondeterministic — NaN payloads, the host
relation, `memory.grow` — so this is a *set*, and the union of a finite and an
infinite part mirrors the way V1 splits its outcome between `Result` and
`Diverges`.

## Why the configuration-indexed form is the primitive

`behaviours host s a vs = behavioursOf host (invoke s a vs)` is the entry-point
form, and it is *derived*. That order matters for the cross-semantics theorems.
Those are proved as simulations between configurations related by a `Sim`
relation, and the Core 3.0 configuration that invokes a function is **not** the
image of the V1 one: `Execution.Core.invoke` expands `call` into
`ref.func; call_ref`, so `(invoke s a vs).toCore ≠ Core.invoke s.toCore a vs'`.
Stating the behaviour theorems over arbitrary configurations restates the
existing simulation results with no new proof work; stating them only at
`invoke` would require re-proving the entry-point correspondence first.

## The range

V1 has no exception handling, so `Behaviour.throws` is never observed
(`throws_not_mem_behavioursOf`); this is exactly the range lemma
`Execution.Runtime.Result.toBehaviour_ne_throws` of the adapter, transported
through the definition.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- The observable behaviours of running the configuration `c`. -/
def behavioursOf {H : Type*} (host : HostSemantics H) (c : Config H) :
    Set (Behaviour Runtime.Value) :=
  {b | ∃ (c' : Config H) (r : Runtime.Result),
        Steps host c c' ∧ c'.code = result r ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ Diverges host c}

/-- The observable behaviours of invoking function address `a` on `vs` in `s`. -/
def behaviours {H : Type} (host : HostSemantics H) (s : Store H) (a : FuncAddr)
    (vs : List Runtime.Value) : Set (Behaviour Runtime.Value) :=
  behavioursOf host (invoke s a vs)

@[simp] theorem behaviours_eq {H : Type} (host : HostSemantics H) (s : Store H)
    (a : FuncAddr) (vs : List Runtime.Value) :
    behaviours host s a vs = behavioursOf host (invoke s a vs) := rfl

/-! ## Introduction -/

/-- A finite run to a configuration whose code is a result exhibits that
result's behaviour. -/
theorem mem_behavioursOf {H : Type*} {host : HostSemantics H} {c c' : Config H}
    {r : Runtime.Result} (steps : Steps host c c') (final : c'.code = result r) :
    r.toBehaviour ∈ behavioursOf host c :=
  Or.inl ⟨c', r, steps, final, rfl⟩

/-- A finite run to a configuration whose code is `vs` returns `vs`. -/
theorem returns_mem_behavioursOf {H : Type*} {host : HostSemantics H} {c c' : Config H}
    {vs : List Runtime.Value} (steps : Steps host c c') (final : c'.code = values vs) :
    Behaviour.returns vs ∈ behavioursOf host c :=
  mem_behavioursOf (r := .values vs) steps final

/-- A finite run to a trapped configuration traps. -/
theorem traps_mem_behavioursOf {H : Type*} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps host c c') (final : c'.code = [.trap]) :
    (Behaviour.traps : Behaviour Runtime.Value) ∈ behavioursOf host c :=
  mem_behavioursOf (r := .trap) steps final

/-- Divergence is observed exactly when the configuration has an infinite
trace. -/
@[simp] theorem diverges_mem_behavioursOf_iff {H : Type*} {host : HostSemantics H}
    {c : Config H} :
    (Behaviour.diverges : Behaviour Runtime.Value) ∈ behavioursOf host c ↔
      Diverges host c := by
  constructor
  · rintro (⟨_, r, _, _, h⟩ | ⟨_, h⟩)
    · exact absurd h.symm (Result.toBehaviour_ne_diverges r)
    · exact h
  · exact fun h => Or.inr ⟨rfl, h⟩

/-! ## Elimination -/

/-- Every terminating observed behaviour comes from a finite run to a
configuration whose code is a result. -/
theorem exists_result_of_mem {H : Type*} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Runtime.Value} (mem : b ∈ behavioursOf host c)
    (ne : b ≠ .diverges) :
    ∃ (c' : Config H) (r : Runtime.Result),
      Steps host c c' ∧ c'.code = result r ∧ b = r.toBehaviour := by
  rcases mem with h | ⟨h, _⟩
  · exact h
  · exact absurd h ne

/-- The `Behaviour.Terminates` phrasing of `exists_result_of_mem`. -/
theorem terminates_of_mem {H : Type*} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Runtime.Value} (mem : b ∈ behavioursOf host c)
    (term : b.Terminates) :
    ∃ (c' : Config H) (r : Runtime.Result),
      Steps host c c' ∧ c'.code = result r ∧ b = r.toBehaviour :=
  exists_result_of_mem mem (by rintro rfl; exact absurd term (by simp))

/-! ## Monotonicity along a run

Behaviours only accumulate backwards: a configuration exhibits every behaviour
of anything it can reach. Divergence is preserved backwards by folding the
infinite trace along the finite prefix (`InfiniteTrace.fold`), by induction on
the `Relation.ReflTransGen` witness. -/

/-- Divergence is preserved backwards along a finite run. -/
theorem diverges_of_steps {H : Type*} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps host c c') (div : Diverges host c') : Diverges host c := by
  induction steps with
  | refl => exact div
  | tail _ step ih => exact ih (InfiniteTrace.fold step div)

/-- Behaviours accumulate backwards along a run. -/
theorem behavioursOf_mono_steps {H : Type*} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps host c c') : behavioursOf host c' ⊆ behavioursOf host c := by
  rintro b (⟨c'', r, hsteps, hfinal, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨c'', r, steps.trans hsteps, hfinal, rfl⟩
  · exact Or.inr ⟨rfl, diverges_of_steps steps hdiv⟩

/-! ## Range -/

/-- WebAssembly 1.0 has no exception handling, so it never throws. -/
theorem throws_not_mem_behavioursOf {H : Type*} {host : HostSemantics H} {c : Config H}
    (a : Nat) : (Behaviour.throws a : Behaviour Runtime.Value) ∉ behavioursOf host c := by
  rintro (⟨_, r, _, _, h⟩ | ⟨h, _⟩)
  · exact Result.toBehaviour_ne_throws r a h.symm
  · cases h

/-- The same, at an entry point. -/
theorem throws_not_mem_behaviours {H : Type} {host : HostSemantics H} {s : Store H}
    {a : FuncAddr} {vs : List Runtime.Value} (e : Nat) :
    (Behaviour.throws e : Behaviour Runtime.Value) ∉ behaviours host s a vs :=
  throws_not_mem_behavioursOf e

/-- Every observed behaviour is a return, a trap or divergence. -/
theorem mem_behavioursOf_cases {H : Type*} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Runtime.Value} (mem : b ∈ behavioursOf host c) :
    (∃ vs, b = .returns vs) ∨ b = .traps ∨ b = .diverges := by
  rcases mem with ⟨_, r, _, _, rfl⟩ | ⟨rfl, _⟩
  · cases r with
    | values vs => exact Or.inl ⟨vs, rfl⟩
    | trap => exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

module

public import Silmaril.Wasm.Component.Reference.Embedding.Thms
public import Silmaril.Wasm.Component.Reference.Embedding.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Dispatch
public import Silmaril.Raw.Wasm.Component.Machine.Soundness
public import Silmaril.Raw.Wasm.Component.Instantiate.Root

/-!
# The embedding API: lifting, lowering, invoking, ticking, cancelling, instantiating

The REF Embedding API (`Store.invoke`, `Store.lift`, `Store.lower`, `Store.tick`, L524-563 of
`definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF"), plus root instantiation (`Instantiate/Root.lean`), on top of the component machine
(`Machine/Exec.lean`, `Machine/Step.lean`) with the dispatcher `Canon.dispatch`
(`Canon/Dispatch.lean`):

| Lean | REF / meaning |
| --- | --- |
| `storeLift core ft opts inst` | `Store.lift` (L539-543): a `CFuncInst.lifted` function value |
| `storeHostFunc ft fn` | a host function value (`CFuncInst.host`, run_tests `mk_host_func`) |
| `storeLower f opts inst` | `Store.lower` (L545-548): a core host function `CanonHost.lowered` |
| `invokeTop c f args` | `Store.invoke` (L524-536) as the host event `HostEvent.invoke` |
| `tickTop` | `Store.tick` (L555-563), `HostEvent.tick` |
| `cancelTop c` | the `on_cancel` returned by `Store.invoke` (L530-534), `HostEvent.cancel` |
| `instantiateTop c args` | root instantiation (`instantiateRootCall`), `HostEvent.run` |
| `componentMachine E X lim q hr host σ0` | an embedder and its initial machine configuration |
| `Calls`, `CallDiverges` | the relational outcome of a top-level call (over `Machine.Steps`) |
| `Instantiates`, `InstantiateTraps`, `InstantiateDiverges` | the same for instantiation |
| `Embedder.runTop`, `callTop`, `instantiateRun` | executable drivers, with soundness |

**Instantiation results.** A host frame discards its program's result (`Machine.runProg`), so
`instantiateProg` reports the root instance and its *function* exports (the part of the export
map the host can invoke) by one observation `instantiatedObs inst es`
(`HostObs.note instantiatedTag ...`, names as utf8 strings, ids as `u32`), decoded exactly by
`decodeInstantiated?` (`decodeInstantiated?_instantiatedObs`). `Instantiates` reads the first
such observation of the trace. Host functions running during instantiation (start
functions) must not emit notes with the tag `instantiatedTag` (not checked).

**Instantiation is a host entry.** `instantiateProg` brackets root instantiation with
`nesting_depth += 1` / `-= 1` like `Store.invoke`, so start functions (`Store.lift`'s
`func_inst`) and the host imports they call (`Store.lower`) run at `nesting_depth > 0`, the
precondition REF asserts (L540, L549; D-f).

## Proved

* `Embedder.runTop_sound`: the trace of `runTop` is a `Machine.Steps` trace
  (`Machine.runTop_sound`).
* `Embedder.callTop_sound`: an executable top-level call with a classified outcome
  (`callOutcome?`: resolved with its result, a trap other than an `internal` fault, or deadlock
  of the call) is a `Calls` fact
  (its trace issues only ticks after the invoke: `runTopCall_ticks`).
* `Embedder.instantiateRun_sound`: an executable instantiation that finished (host in control,
  not locked down) with a decoded result is an `Instantiates` fact (`Machine.run` issues no
  host event: `run_noHost`).
* `step?_not_host`, `runLoop_noHost`, `runTopLoop_ticks`, `hostStep?_label`: the label shapes
  of the executable drivers.
* `decodeInstantiated?_instantiatedObs` (the observation encoding round-trips).

## Tests (Mock engine, kernel-checked by `decide +kernel`)

* the empty component instantiates in a fresh root instance `0` with no exports
  (`empty_instantiates`, and the relational `empty_instantiates_rel`);
* a component whose core module exports `f() = 42` (no imports, no memory), lifted at
  `func() -> u32` and exported as `"f"`, instantiates with the export `("f", func 0)`
  (`const_instantiates`), and invoking the export resolves the top-level call with `[42]`
  (`const_call`); no choice is made and the nesting depth is restored (`const_call_shape`).
  `const_calls` states both relationally, end to end from `smokeMachine.config`
  (`Instantiates` to `m₁`, then `Calls` from `m₁`).

## Design notes and non-claims

* `componentMachine E X lim q hr host σ0` also takes the host readiness `hr` and the host
  record `host : Canon.HostImpl E σ` (instead of `hostFns`, see `Canon/Dispatch.lean`); it
  returns a `ComponentMachine` (the `Embedder` and the initial `Config`), since `Config` does not
  hold the dispatcher.
* Nested instantiation is a late-bound call (`Call.instantiate`, dispatched by
  `Canon.dispatch` to `Instantiate.instantiateClosure`), so the embedding API has no nesting
  bound: arbitrary nesting depth is bounded only by the machine's fuel (the `fuel` of the
  executable drivers). The embedder, the drivers and the relations that mention
  `Embedder.dispatch` take the instance `[∀ a b, Decidable (E.ExternSub a b)]`.
* `Calls` names the top-level call id `c` explicitly; after the invoke its trace may contain
  only the host events `tick` and `cancel c` (`CallHostEvent`), so no other host program can
  forge `HostObs.resolved c` or cause the outcome. Its outcome `resolved r` requires the
  host in control, no lockdown and `result? c = some r` (other top-level calls may be
  unresolved); `deadlock` is `Machine.Deadlocked` with `c` unresolved; `trap` is a machine
  trap (global, as in REF: it may come from another thread already present in `m`) whose trace
  has no `TrapReason.internal` label, so a model fault cannot satisfy a trap-expected fact.
  `Instantiates` / `InstantiateTraps` allow no host event after the instantiation event, and
  `InstantiateTraps` also excludes `internal` faults.
  Host functions (`HostImpl`) are trusted: one that emits `HostObs.resolved c` itself is not
  excluded. `CallDiverges` and
  `InstantiateDiverges` are guest divergence (`Machine.Diverges`, internal steps only) after the
  host event.
* `instantiateRun` drives internal steps only (`Machine.run`, no ticks): instantiation is
  synchronous (start functions run under `canon_lift`'s synchronous loop).
* Not claimed: completeness of the drivers, termination, fairness, typing of instantiation
  (not modelled; only the run-time import check `Instantiate.importTypeCheck` is performed),
  or anything about host behaviour beyond the given programs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
  _root_.Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ : Type}

/-! ## `Store.lift` / `Store.lower` -/

/-! ## Instantiation results as an observation -/

/-! ## Host events -/

section Instantiation

variable [∀ a b, Decidable (E.ExternSub a b)]

end Instantiation

/-! ## Embedders and the initial machine -/

/-! ## Relations -/

section Relations

variable (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))

variable [∀ a b, Decidable (E.ExternSub a b)]

end Relations

/-! ## Executable drivers and their soundness -/

namespace Embedder

variable [∀ a b, Decidable (E.ExternSub a b)] (emb : Embedder E σ) (o : Oracle E)

theorem runTop_sound (fuel : Nat) (m : Config E σ) :
    Steps o.prof emb.hr emb.dispatch m (emb.runTop o fuel m).labels
      (emb.runTop o fuel m).config :=
  Machine.runTop_sound emb.hr emb.dispatch emb.X o fuel m

end Embedder

/-- A trapping run without an `internal` fault is classified as `trap`. -/
theorem callOutcome?_of_trap {S : Type} {c : CallId} {r : RunResult E σ S}
    (h : r.outcome = .trap) (hi : r.labels.any Label.isInternalTrap = false) :
    callOutcome? c r = some .trap := by
  simp [callOutcome?, h, hi]

section Labels

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

end Labels

namespace Embedder

variable [∀ a b, Decidable (E.ExternSub a b)] (emb : Embedder E σ) (o : Oracle E)

end Embedder

/-! ## Smoke tests (Mock engine) -/

namespace EmbeddingTests

open Engine.Mock (mock mockExec)

/-- The empty component instantiates in the fresh root instance `0` with no exports. -/
theorem empty_instantiates :
    (emptyRun.map fun (r, inst, es) => (r.outcome, inst, es, r.config.store.insts.length)) =
      some (.resolved, ⟨0⟩, [], 1) := by decide +kernel

theorem empty_instantiates_rel :
    ∃ m', Instantiates first.prof noReady smokeEmb.dispatch smokeMachine.config [] [] m'
      ⟨0⟩ [] := by
  cases h : emptyRun with
  | none =>
    have hc := empty_instantiates
    rw [h] at hc
    simp at hc
  | some x =>
    obtain ⟨r, inst, es⟩ := x
    have hx : (inst, es) = (⟨0⟩, []) := by
      have := empty_instantiates
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact Prod.ext this.2.1 this.2.2.1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
    exact ⟨_, smokeEmb.instantiateRun_sound first h⟩

theorem const_instantiates :
    (constRun.map fun (r, inst, es) => (r.outcome, inst, es)) =
      some (.resolved, ⟨0⟩, [("f", ⟨0⟩)]) := by decide +kernel

/-- The top-level call resolves with `[42]`. -/
theorem const_call :
    (constCall.map fun r => (r.outcome, r.config.result? ⟨0⟩)) =
      some (.resolved, some (some [Val.u32 42])) := by decide +kernel

/-- No choice was made, the nesting depth is restored, and the implicit thread exited. -/
theorem const_call_shape :
    (constCall.map fun r => (r.choices.length, r.config.store.nestingDepth,
      r.config.store.threads.map (·.status), r.config.ctl.length)) =
      some (0, 0, [.exited], 0) := by decide +kernel

/-- The same facts on the relations, end to end: from the initial configuration, instantiating
`constComponent` reaches `m₁` with root instance `0` and the export `("f", func 0)`, and from
`m₁` top-level call `0` of that export (on no arguments) resolves with `[42]`. -/
theorem const_calls :
    ∃ m₁ m', Instantiates first.prof noReady smokeEmb.dispatch smokeMachine.config
        constComponent [] m₁ ⟨0⟩ [("f", ⟨0⟩)] ∧
      Calls first.prof noReady smokeEmb.dispatch m₁ ⟨0⟩ ⟨0⟩ [] m'
        (.resolved (some [Val.u32 42])) := by
  have hi := const_instantiates
  cases h₁ : constRun with
  | none => rw [h₁] at hi; simp at hi
  | some x =>
    obtain ⟨r₀, inst, es⟩ := x
    rw [h₁] at hi
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨_, rfl, rfl⟩ := hi
    have hI := smokeEmb.instantiateRun_sound first h₁
    have hc := const_call
    have hcall : constCall = smokeEmb.callTop first 400 ⟨0⟩ ⟨0⟩ [] r₀.config := by
      simp only [constCall, h₁]
      rfl
    rw [hcall] at hc
    cases h : smokeEmb.callTop first 400 ⟨0⟩ ⟨0⟩ [] r₀.config with
    | none => rw [h] at hc; cases hc
    | some r =>
      rw [h] at hc
      have hc' : r.outcome = .resolved ∧ r.config.result? ⟨0⟩ = some (some [Val.u32 42]) :=
        Prod.mk.inj (Option.some.inj hc)
      refine ⟨_, _, hI, smokeEmb.callTop_sound first h ?_⟩
      simp [callOutcome?, hc'.1, hc'.2]

end EmbeddingTests

end Silmaril.Wasm.Component

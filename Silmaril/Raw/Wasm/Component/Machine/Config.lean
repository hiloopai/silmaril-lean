module

public import Silmaril.Wasm.Component.Reference.Machine.Config.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Config.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Effects

/-!
# Machine configurations, host events, labels and outcomes

The specification programs `Canon.P E σ` (the REF functions of `definitions.py` at
component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
are run by a machine that interprets the operations `Canon.Op E σ`. This file fixes the
machine's configuration; the executable step is `Machine/Exec.lean` and the relation
`Machine/Step.lean`.

## Configuration

* A running **activation** (`Activation`) is a `Focus` (the program or core thread executing
  now) and a stack of `Seg`ments (what to do with its result), plus the REF thread it runs on
  (`none` for host frames, e.g. a top-level host call before a thread exists).
  * `Focus.prog p`: the program `p` runs; its `Ret` result goes to the top segment.
  * `Focus.core t k`: the core activation `t` (of the engine, over canon host sites
    `CanonHost E`) runs; its returned values go to `k` (the continuation of `Op.callCore`).
  * `Seg.prog k`: a program waiting for the result of a late-bound call (`Op.call`).
  * `Seg.core t k`: a core activation `t` parked on a host callout (REF: core code calling a
    canon host function, `Store.lower`'s `core_func_inst`); the `Ret.flat` result of the callout
    program resumes `t` (`E.resume`), whose returned values then go to `k`.
  An activation with an empty segment stack whose focus returns has finished.
* **Blocked threads' continuations** live in `Config.conts`, indexed by `ThreadId`, and never
  in the component store `CStore E` (issue #477; the REF keeps them in `Thread.cont`, L279-390).
* **The control chain** `Config.ctl`: its head is the running activation. The activations below
  it are suspended *resumers*: an activation that issued `Op.resumeThread t` (REF
  `Thread.resume`, resume sites R1-R4) keeps its continuation `Focus.prog (k ())` below the
  resumed thread's activation, and runs again when that thread blocks or finishes (REF: `resume`
  returns when the resumed thread suspends). An empty chain means the host is in control.
* `Config.pending` records top-level calls issued by the host (`HostEvent.invoke`) and
  `Config.results` their resolutions (REF `on_resolve`: `none` means cancelled).
* `Config.cancels` records, per top-level call, the `CancelRef` that REF `Store.invoke`
  (L524-536) wraps into the returned `on_cancel`: when the host activation of
  `HostEvent.invoke c f args` (running `call (.funcInst f caller)`) returns `Ret.cancel r`, the
  machine records `(c, r)` with `setCancel`; `HostEvent.cancel c` then looks it up with
  `cancel?` and runs `call (.onCancel r)` bracketed by `nesting_depth += 1 / -= 1` (REF
  L530-534).
* REF `Store.nesting_depth` (reentrant host invocations) lives in `CStore.nestingDepth`, not here.

## Host events, labels, outcomes

`HostEvent` are the embedder's actions (REF `Store.invoke`, `Store.tick`, cancelling a
top-level call via its `on_cancel`, and running an instantiation program supplied by the embedding,
`Embedding.lean`). `Label` labels machine transitions; `Label.obs` reuses `Canon.HostObs`. `Outcome`
summarises a bounded run.

## Design notes

* The configuration structure is `Machine.Config E σ`, not `Machine E σ`: a structure
  `Machine` inside namespace `Machine` fails the `dupNamespace` linter.

* `Seg.resumer` is not a segment: resumers are the non-head activations of `ctl` (above).
* `Focus.core` carries the continuation `k` of the returned values, so `Seg.core` is only used
  for a core activation parked on a callout.
* `HostEvent.run p` is the instantiation event; `HostEvent.instantiate` is an alias.

Not modelled or claimed here: any transition, invariants of configurations,
or the choice of the oracle (`Machine/Oracle.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable (E : CoreEngine) (σ : Type)

theorem Label.isInternalTrap_trap_internal {E : CoreEngine} {σ : Type} (msg : String) :
    (Label.trap (.internal msg) : Label E σ).isInternalTrap = true := rfl

variable {E σ}

namespace Activation

end Activation

namespace Config

theorem cancel?_setCancel_ne (m : Config E σ) (c d : CallId) (r : CancelRef) (h : d ≠ c) :
    (m.setCancel c r).cancel? d = m.cancel? d := by
  simp only [cancel?, setCancel, List.find?_cons]
  have hne : (c == d) = false := by simpa using fun e => h e.symm
  simp only [hne]
  congr 1
  rw [List.find?_filter]
  congr 1
  funext x
  by_cases hx : x.1 = d
  · simp [hx, bne_iff_ne, h]
  · simp [hx]

theorem result?_resolve_self (m : Config E σ) (c : CallId) (r : Option (List Val))
    (h : m.result? c = none) : (m.resolve c r).result? c = some r := by
  simp only [result?, Option.map_eq_none_iff] at h
  simp [result?, resolve, List.find?_append, h]

end Config

/-! ## Examples -/

section Examples

example (s : CStore E) (h : σ) (t : ThreadId) (p : P E σ (Ret E)) :
    ((Config.init s h).setCont t (some (.ofProg (some t) p))).cont? t =
      some (.ofProg (some t) p) := by simp

example (s : CStore E) (h : σ) :
    ((Config.init s h).resolve ⟨0⟩ (some [])).result? ⟨0⟩ = some (some []) := rfl

example (s : CStore E) (h : σ) :
    (((Config.init s h).setCancel ⟨0⟩ (.task ⟨3⟩)).setCancel ⟨1⟩ .none).cancel? ⟨0⟩ =
      some (.task ⟨3⟩) := by
  rw [Config.cancel?_setCancel_ne _ _ _ _ (by decide), Config.cancel?_setCancel_self]

example : Config.setSlot ([] : List (Option Nat)) 2 (some 7) = [none, none, some 7] := rfl

end Examples

end Silmaril.Wasm.Component.Machine

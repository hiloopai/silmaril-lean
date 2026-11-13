module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.HostMap

/-!
# Core activations of the reference machine as Core 3.0 runs

The component machine runs a core activation of `core3P P` by `E.Internal` steps, which are
`Silmaril.Wasm.Game.InternalP P` steps of single-threaded threads over the engine's store, and reads
its end through `E.status = flatStatus ∘ statusP P`. This module turns such runs into Core 3.0
runs, at any host type:

* `internalP_steps`, `internalP_diverges`: host-free thread runs and divergence are Core runs
  and Core divergence (`noHost`) of the threads' configurations;
* `status_values`, `status_trap`: a `returned` status of `core3P P` is a Core result in the
  thread's code (values with their flat view; a trap or an uncaught exception);
* `coreRun_values`, `coreRun_trap`, `coreRun_diverges`: a run of an invocation in a store `s`,
  ending with that status (or diverging), is a run of the invocation in the store
  `Store.mapH g s` of any other host type in the shape `coreOut`/`coreDiverges` use.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

variable {H H' : Type} {P : Profile}

/-- One host-free thread step is one Core step of the threads' configurations. -/
theorem internalP_step {x y : Store H × Thread} (h : Silmaril.Wasm.Game.InternalP P x y) :
    Step P (noHostH H) (x.2.config x.1) (y.2.config y.1) := by
  obtain ⟨f', code', hy, hs⟩ := h
  obtain ⟨s', t'⟩ := y
  have ht : t' = .active f' code' := hy
  subst ht
  exact hs

/-- Host-free thread runs are Core runs. -/
theorem internalP_steps {x y : Store H × Thread}
    (h : Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) x y) :
    Steps P (noHostH H) (x.2.config x.1) (y.2.config y.1) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (internalP_step hs)

/-- Host-free thread divergence is Core divergence. -/
theorem internalP_diverges {x : Store H × Thread}
    (h : Silmaril.InfiniteTrace (Silmaril.Wasm.Game.InternalP P) x) :
    Diverges P (noHostH H) (x.2.config x.1) :=
  Silmaril.InfiniteTrace.map (f := fun y : Store H × Thread => y.2.config y.1)
    (fun _ _ hs => internalP_step hs) h

/-! ## Reading the status -/

/-- `statusP` returned values: the code is those values. -/
theorem statusP_values {s : Store H} {t : Thread} {vs : List Execution.Core.Val}
    (h : Silmaril.Wasm.Game.statusP P s t = .returned (.values vs)) :
    (t.config s).code = vals vs := by
  unfold Silmaril.Wasm.Game.statusP at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  · have hvs : h1.choose = vs := by
      simpa only [Status.returned.injEq, CallResult.values.injEq] using h
    exact hvs ▸ h1.choose_spec
  all_goals first | cases h | (split at h <;> cases h)

/-- `statusP` returned a trap: the code is a trap or an uncaught exception. -/
theorem statusP_trap {s : Store H} {t : Thread}
    (h : Silmaril.Wasm.Game.statusP P s t = .returned .trap) :
    (t.config s).code = [.trap] ∨ ∃ a, (t.config s).code = throwing a := by
  unfold Silmaril.Wasm.Game.statusP at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  · cases h
  · exact .inl h2
  · exact .inr h3
  all_goals split at h <;> cases h

/-- A `returned` values status of `core3P P` is a Core value result with its flat view. -/
theorem status_values {s : Store H} {t : Thread} {fvs : List Silmaril.Wasm.Execution.Runtime.Value}
    (h : flatStatus (Silmaril.Wasm.Game.statusP P s t) = .returned (.values fvs)) :
    ∃ vs, (t.config s).code = vals vs ∧ vs.mapM toFlat? = some fvs := by
  unfold flatStatus at h
  split at h
  · cases h
  next vs heq =>
    split at h
    next fvs' hm =>
      have hf : fvs' = fvs := by
        simpa only [Silmaril.Wasm.Component.Engine.Status.returned.injEq,
          Silmaril.Wasm.Component.Engine.CallResult.values.injEq] using h
      exact ⟨vs, statusP_values heq, hf ▸ hm⟩
    next => cases h
  · cases h
  · split at h <;> cases h
  · cases h

/-- A `returned` trap status of `core3P P` is a Core trap or uncaught exception. -/
theorem status_trap {s : Store H} {t : Thread}
    (h : flatStatus (Silmaril.Wasm.Game.statusP P s t) = .returned .trap) :
    (t.config s).code = [.trap] ∨ ∃ a, (t.config s).code = throwing a := by
  unfold flatStatus at h
  split at h
  · cases h
  · split at h <;> cases h
  next heq => exact statusP_trap heq
  · split at h <;> cases h
  · cases h

/-! ## Runs of an invocation -/

/-- The configuration of a pending invocation. -/
theorem invokeFlat_config (s : Store H) (a : Nat)
    (xs : List Silmaril.Wasm.Execution.Runtime.Value) :
    (Thread.invokeFlat a xs).config s = invoke s a (xs.map ofFlat) :=
  rfl

/-- **A returned run of the reference engine is a `coreOut` run** of the renamed store. -/
theorem coreRun_values (g : H → H') {s : Store H} {a : Nat}
    {xs : List Silmaril.Wasm.Execution.Runtime.Value} {y : Store H × Thread}
    {fvs : List Silmaril.Wasm.Execution.Runtime.Value}
    (hr : Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) (s, Thread.invokeFlat a xs) y)
    (hs : flatStatus (Silmaril.Wasm.Game.statusP P y.1 y.2) = .returned (.values fvs)) :
    ∃ (c' : Config H') (res : Result),
      Steps P (noHostH H') (invoke (Store.mapH g s) a (xs.map ofFlat)) c' ∧ c'.code = res.toAdmin ∧
      (match res with
        | .values vs => vs.mapM toFlat?
        | _ => none) = some fvs := by
  obtain ⟨vs, hc, hm⟩ := status_values hs
  have hrun : Steps P (noHostH H) (invoke s a (xs.map ofFlat)) (y.2.config y.1) :=
    internalP_steps hr
  exact ⟨Config.mapH g (y.2.config y.1), .values vs, invoke_steps_mapH g hrun, hc, hm⟩

/-- **A trapping run of the reference engine is a `coreOut` run with no result.** -/
theorem coreRun_trap (g : H → H') {s : Store H} {a : Nat}
    {xs : List Silmaril.Wasm.Execution.Runtime.Value} {y : Store H × Thread}
    (hr : Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) (s, Thread.invokeFlat a xs) y)
    (hs : flatStatus (Silmaril.Wasm.Game.statusP P y.1 y.2) = .returned .trap) :
    ∃ (c' : Config H') (res : Result),
      Steps P (noHostH H') (invoke (Store.mapH g s) a (xs.map ofFlat)) c' ∧ c'.code = res.toAdmin ∧
      (match res with
        | .values vs => vs.mapM toFlat?
        | _ => none) = none := by
  have hrun : Steps P (noHostH H) (invoke s a (xs.map ofFlat)) (y.2.config y.1) :=
    internalP_steps hr
  rcases status_trap hs with hc | ⟨e, hc⟩
  · exact ⟨_, .trap, invoke_steps_mapH g hrun, hc, rfl⟩
  · exact ⟨_, .throw e, invoke_steps_mapH g hrun, hc, rfl⟩

/-- **A divergent run of the reference engine is a `coreDiverges` run.** -/
theorem coreRun_diverges (g : H → H') {s : Store H} {a : Nat}
    {xs : List Silmaril.Wasm.Execution.Runtime.Value}
    (hd : Silmaril.InfiniteTrace (Silmaril.Wasm.Game.InternalP P) (s, Thread.invokeFlat a xs)) :
    Diverges P (noHostH H') (invoke (Store.mapH g s) a (xs.map ofFlat)) :=
  invoke_diverges_mapH g (internalP_diverges hd)

end Silmaril.Proofs.Wasm.Component.Reference

module

public import Silmaril.Proofs.Wasm.Component.FXEngine.HostMap
public import Silmaril.Proofs.Wasm.Component.Reference.CallTyping
public import Silmaril.Proofs.Wasm.Component.Reference.CoreRun
public import Silmaril.Wasm.Component.EngineRef.Defs

/-!
# Export activations of the WasmFX engine in a store without host or FX functions

The reference machine runs the core activation of an export over `fxE P` in its own store
`cs : Store (FXCode H)` (host type `H = CanonHost (fxE P)`), from the Core thread
`.core (invokeFlat a xs)`. When `cs` renames (`Store.mapH`, every host code to `0`) to the store
of the module's `IsInst` instance `I`, the export is `a = I.addrs.getD k 0` and the arguments
are typed, this module shows that the run is a Core 3.0 run of the instance:

* `internalP_mapH`, `reach_mapH`, `statusP_mapH_returned`: host-free thread steps, runs and
  returned statuses survive renaming the host code (for every `g : H → H'`);
* `no_statusP_callout`: no thread reached by Core steps from the activation is at a host call,
  of a component host function or of an FX function (`run_no_callout` on the renamed run);
* `step_fx`, `reach_fx`: hence every FX engine step from a reached Core thread is a Core
  step (an FX function is never entered), and FX engine runs are Core thread runs;
* `runFacts_fx`: **the run facts** (`EngineRef.RunFacts`) of the activation, with the outcomes
  and divergence of the `core3P P` engine instance `J` whose store is `I.store`: no callout,
  returned values typed (`run_results_typed`) and in `engineOut (core3P P) J`, traps in it,
  divergence a divergence of `J`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXRefE

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.EngineRef
open Silmaril.Proofs.Wasm.Component.FXEngine (config_mapH' decompose?_of_statusP_callout liftR_eq
  liftR_eq_callout)
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH Config.mapH Step.mapH internalP_steps
  invoke_steps_mapH status_values run_results_typed run_no_callout decompose?_mapH)
open Silmaril.Wasm.Game (statusP InternalP)
open Silmaril.Wasm.Execution.Core (Store Config)
open Silmaril.Wasm.SingleThreaded (Thread)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps Diverges)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {H H' : Type}

/-! ## Renaming the host code of thread runs -/

/-- A host-free thread step survives renaming the host code. -/
theorem internalP_mapH (g : H → H') {s s' : Store H} {t t' : Thread}
    (h : InternalP P (s, t) (s', t')) :
    InternalP P (Store.mapH g s, t) (Store.mapH g s', t') := by
  obtain ⟨f', code', ht, hstep⟩ := h
  have hm : Silmaril.Wasm.Execution.Core.Step P (fun _ _ _ _ => False)
      (Config.mapH g (t.config s)) (Config.mapH g ⟨s', f', code'⟩) := Step.mapH g hstep
  refine ⟨f', code', ht, ?_⟩
  rw [config_mapH']
  exact hm

/-- Host-free thread runs survive renaming the host code. -/
theorem reach_mapH (g : H → H') {x y : Store H × Thread}
    (h : Relation.ReflTransGen (InternalP P) x y) :
    Relation.ReflTransGen (InternalP P) (Store.mapH g x.1, x.2) (Store.mapH g y.1, y.2) :=
  Relation.ReflTransGen.lift (fun z : Store H × Thread => (Store.mapH g z.1, z.2))
    (fun a b hab => internalP_mapH (s := a.1) (t := a.2) (s' := b.1) (t' := b.2) g hab) x y h

/-- A returned status survives renaming the host code (it is read off the code). -/
theorem statusP_mapH_returned (g : H → H') {s : Store H} {t : Thread}
    {r : Silmaril.Wasm.SingleThreaded.CallResult} (h : statusP P s t = .returned r) :
    statusP P (Store.mapH g s) t = .returned r := by
  have hc : (t.config (Store.mapH g s)).code = (t.config s).code := by
    rw [config_mapH']
    rfl
  unfold statusP at h ⊢
  dsimp only at h ⊢
  rw [hc]
  split_ifs at h ⊢
  all_goals first
    | (injection h with h; subst h; rfl)
    | (split at h <;> cases h)

/-- A flat returned status is a returned status. -/
theorem flatStatus_returned {st : Silmaril.Wasm.SingleThreaded.Status H}
    {R : Silmaril.Wasm.Component.Engine.CallResult} (h : flatStatus st = .returned R) :
    ∃ r, st = .returned r := by
  rcases st with _ | r | ⟨_, _⟩ | _
  · cases h
  · exact ⟨r, rfl⟩
  · simp only [flatStatus] at h
    split at h <;> cases h
  · cases h

/-- A renamed status that is returned was returned. -/
theorem mapHostS_returned {st : Silmaril.Wasm.Component.Engine.Status (FXCode H)}
    {R : Silmaril.Wasm.Component.Engine.CallResult} (e : mapHostS st = .returned R) :
    st = .returned R := by
  rcases st with _ | r | ⟨c, _⟩ | _
  · cases e
  · simp only [mapHostS, Silmaril.Wasm.Component.Engine.Status.returned.injEq] at e
    rw [e]
  · cases c <;> cases e
  · cases e

/-- The `core3P P` status of a renamed store, when the status is returned. -/
theorem core3P_status_mapH (g : H → H') {s : Store H} {t : Thread}
    {R : Silmaril.Wasm.Component.Engine.CallResult}
    (h : flatStatus (statusP P s t) = .returned R) :
    (core3P P).status (Store.mapH g s) t = .returned R := by
  obtain ⟨r, hr⟩ := flatStatus_returned h
  show flatStatus (statusP P (Store.mapH g s) t) = _
  rw [statusP_mapH_returned g hr]
  rw [hr] at h
  rcases r with vs | _
  · cases hm : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
    | none => simp [flatStatus, hm] at h
    | some fvs => simpa [flatStatus, hm] using h
  · simpa [flatStatus] using h

/-! ## The activation of an export -/

/-- The context of an export activation: the module's `IsInst` instance `I`, a store `cs` that
renames to `I.store`, the export `x` of the module, and typed flat arguments `xs`. -/
structure CallCtx (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) (cs : Store (FXCode H))
    (x : SimpleExport) (xs : List Flat) : Prop where
  inst : c.mod.IsInst I
  store : Store.mapH (fun _ => (0 : Nat)) cs = I.store
  core : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)
  typed : xs.map (·.type) = ValTy.flatList x.ty.params

variable {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} {cs : Store (FXCode H)}
  {x : SimpleExport} {xs : List Flat}

/-- The Core run of a thread run from the activation, in the store of the instance. -/
theorem coreRun (hC : CallCtx c I cs x xs) {s' : Store (FXCode H)} {t' : Thread}
    (hr : Relation.ReflTransGen (InternalP P) (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs)
      (s', t')) :
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke I.store (I.addrs.getD x.core 0)
        (xs.map Silmaril.Wasm.SingleThreaded.ofFlat))
      (Config.mapH (fun _ => (0 : Nat)) (t'.config s')) := by
  have run := invoke_steps_mapH (fun _ : FXCode H => (0 : Nat)) (internalP_steps hr)
  rw [hC.store] at run
  exact run

/-- **No reached thread is at a host call.** -/
theorem no_statusP_callout (hC : CallCtx c I cs x xs) {s' : Store (FXCode H)} {t' : Thread}
    (hr : Relation.ReflTransGen (InternalP P) (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs)
      (s', t')) {hc : FXCode H} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hs : statusP P s' t' = .callout hc args) : False := by
  obtain ⟨nm, hcore⟩ := hC.core
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨E, a', hd⟩ := decompose?_of_statusP_callout hs
  obtain ⟨E', hd'⟩ := decompose?_mapH (fun _ => (0 : Nat)) hd
  have hxs' : xs.map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact hC.typed
  have hn := run_no_callout hC.inst hk hxs' (coreRun hC hr)
  have hstore : (Config.mapH (fun _ => (0 : Nat)) (t'.config s')).store =
      Store.mapH (fun _ => 0) s' :=
    congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  rw [hstore] at hn
  exact absurd (hd'.symm.trans hn) (by simp)

/-- **An FX engine step from a reached Core thread is a Core step.** -/
theorem step_fx (hC : CallCtx c I cs x xs) {s₁ : Store (FXCode H)} {t₁ : Thread}
    (hr : Relation.ReflTransGen (InternalP P) (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs)
      (s₁, t₁)) {y : Store (FXCode H) × ThreadFX H}
    (h : (fxE P).Internal (s₁, ThreadFX.core t₁) y) :
    ∃ s₂ t₂, y = (s₂, ThreadFX.core t₂) ∧ InternalP P (s₁, t₁) (s₂, t₂) := by
  rcases (h : InternalFX P (s₁, ThreadFX.core t₁) y) with ⟨t₂, ht, h'⟩ | ⟨⟨F, args, e⟩, -⟩
  · exact ⟨y.1, t₂, Prod.ext rfl ht, h'⟩
  · exact (no_statusP_callout hC hr e).elim

/-- **FX engine runs of the activation are Core thread runs.** -/
theorem reach_fx (hC : CallCtx c I cs x xs) {y : Store (FXCode H) × ThreadFX H}
    (h : Steps (fxE P) (cs, ThreadFX.core (Thread.invokeFlat (I.addrs.getD x.core 0) xs)) y) :
    ∃ s' t', y = (s', ThreadFX.core t') ∧
      Relation.ReflTransGen (InternalP P) (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs)
        (s', t') := by
  induction h with
  | refl => exact ⟨_, _, rfl, .refl⟩
  | tail _ hstep ih =>
    obtain ⟨s₁, t₁, rfl, h₁⟩ := ih
    obtain ⟨s₂, t₂, rfl, h₂⟩ := step_fx hC h₁ hstep
    exact ⟨s₂, t₂, rfl, h₁.tail h₂⟩

/-- The FX status of a reached Core thread is its flat Core status. -/
theorem statusFX_reached (hC : CallCtx c I cs x xs) {s' : Store (FXCode H)} {t' : Thread}
    (hr : Relation.ReflTransGen (InternalP P) (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs)
      (s', t')) {R : Silmaril.Wasm.Component.Engine.CallResult}
    (hst : (fxE P).status s' (ThreadFX.core t') = .returned R) :
    flatStatus (statusP P s' t') = .returned R := by
  have e : liftR (statusP P s' t') = .returned R := hst
  rw [liftR_eq fun F args h => no_statusP_callout hC hr h] at e
  exact mapHostS_returned e

/-- A thread run from the activation, renamed, is a run of the `core3P P` instance `J`. -/
theorem core3P_run (hC : CallCtx c I cs x xs) {J : EInstance (core3P P)}
    (hJs : J.store = I.store) {s' : Store (FXCode H)} {t' : Thread}
    (hr : Relation.ReflTransGen (InternalP P) (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs)
      (s', t')) :
    Steps (core3P P) (J.store, (core3P P).invoke (I.addrs.getD x.core 0) xs)
      (Store.mapH (fun _ => (0 : Nat)) s', t') := by
  have e := reach_mapH (fun _ : FXCode H => (0 : Nat)) hr
  rw [hC.store, ← hJs] at e
  exact e

/-- No FX engine run of the activation reaches a callout. -/
theorem no_callout_fx (hC : CallCtx c I cs x xs) {s' : Store (FXCode H)} {t' : ThreadFX H}
    (h : H) (args : List Flat)
    (run : Steps (fxE P) (cs, (fxE P).invoke (I.addrs.getD x.core 0) xs) (s', t')) :
    (fxE P).status s' t' ≠ .callout h args := by
  intro hst
  obtain ⟨s₂, t₂, e, hr⟩ := reach_fx hC run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨args', hst'⟩ := liftR_eq_callout (show liftR (statusP P _ _) = _ from hst)
  exact no_statusP_callout hC hr hst'

/-- Values returned by a reached thread have the export's flat result types. -/
theorem typed_fx (hC : CallCtx c I cs x xs) {s' : Store (FXCode H)} {t' : Thread}
    (hr : Relation.ReflTransGen (InternalP P) (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs)
      (s', t')) {ys : List Flat}
    (hflat : flatStatus (statusP P s' t') = .returned (.values ys)) :
    ys.map (·.type) = ValTy.flatList x.ty.results := by
  obtain ⟨nm, hcore⟩ := hC.core
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  have hxs' : xs.map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact hC.typed
  obtain ⟨vs, hc, hm⟩ := status_values hflat
  have ht := run_results_typed hC.inst hk hxs' (coreRun hC hr) hc hm
  rw [hget] at ht
  exact ht

/-- Returned values of an FX engine run of the activation: typed, and an outcome of `J`. -/
theorem values_fx (hC : CallCtx c I cs x xs) {J : EInstance (core3P P)}
    (hJs : J.store = I.store) (hJa : J.addrs[x.core]? = some (I.addrs.getD x.core 0))
    {s' : Store (FXCode H)} {t' : ThreadFX H} (ys : List Flat)
    (run : Steps (fxE P) (cs, (fxE P).invoke (I.addrs.getD x.core 0) xs) (s', t'))
    (hst : (fxE P).status s' t' = .returned (.values ys)) :
    some ys ∈ engineOut (core3P P) J x.core xs ∧ ys.map (·.type) = ValTy.flatList x.ty.results := by
  obtain ⟨s₂, t₂, e, hr⟩ := reach_fx hC run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hflat := statusFX_reached hC hr hst
  exact ⟨⟨_, _, _, hJa, core3P_run hC hJs hr, Or.inl ⟨ys, core3P_status_mapH _ hflat, rfl⟩⟩,
    typed_fx hC hr hflat⟩

/-- A trap of an FX engine run of the activation is an outcome of `J`. -/
theorem trap_fx (hC : CallCtx c I cs x xs) {J : EInstance (core3P P)}
    (hJs : J.store = I.store) (hJa : J.addrs[x.core]? = some (I.addrs.getD x.core 0))
    {s' : Store (FXCode H)} {t' : ThreadFX H}
    (run : Steps (fxE P) (cs, (fxE P).invoke (I.addrs.getD x.core 0) xs) (s', t'))
    (hst : (fxE P).status s' t' = .returned .trap) :
    none ∈ engineOut (core3P P) J x.core xs := by
  obtain ⟨s₂, t₂, e, hr⟩ := reach_fx hC run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  exact ⟨_, _, _, hJa, core3P_run hC hJs hr,
    Or.inr ⟨core3P_status_mapH _ (statusFX_reached hC hr hst), rfl⟩⟩

/-- A divergence of the activation on the FX engine is a divergence of its Core threads. -/
theorem diverges_core (hC : CallCtx c I cs x xs)
    (hd : Diverges (fxE P) (cs, (fxE P).invoke (I.addrs.getD x.core 0) xs)) :
    Silmaril.InfiniteTrace (InternalP P) (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs) :=
  Silmaril.InfiniteTrace.of_map (fun z : Store (FXCode H) × Thread => (z.1, ThreadFX.core z.2))
    (fun z => Relation.ReflTransGen (InternalP P)
      (cs, Thread.invokeFlat (I.addrs.getD x.core 0) xs) z)
    (fun ⟨_, _⟩ y hz hy => by
      obtain ⟨s₂, t₂, rfl, h₂⟩ := step_fx hC hz hy
      exact ⟨(s₂, t₂), h₂, hz.tail h₂, rfl⟩) .refl hd

/-- A divergence of the activation on the FX engine is a divergence of `J`. -/
theorem diverges_fx (hC : CallCtx c I cs x xs) {J : EInstance (core3P P)}
    (hJs : J.store = I.store) (hJa : J.addrs[x.core]? = some (I.addrs.getD x.core 0))
    (hd : Diverges (fxE P) (cs, (fxE P).invoke (I.addrs.getD x.core 0) xs)) :
    engineDiverges (core3P P) J x.core xs := by
  have hN := Silmaril.InfiniteTrace.map (fun z : Store (FXCode H) × Thread =>
    (Store.mapH (fun _ => (0 : Nat)) z.1, z.2))
    (fun a b hab => internalP_mapH (s := a.1) (t := a.2) (s' := b.1) (t' := b.2) _ hab)
    (diverges_core hC hd)
  refine ⟨_, hJa, ?_⟩
  show Silmaril.InfiniteTrace (InternalP P) _
  rw [hJs, ← hC.store]
  exact hN

/-- **The run facts of the activation**, with the outcomes of a `core3P P` instance `J` whose
store is `I.store` and whose export `x.core` is at `I.addrs.getD x.core 0`. -/
theorem runFacts_fx (hC : CallCtx c I cs x xs) {J : EInstance (core3P P)}
    (hJs : J.store = I.store) (hJa : J.addrs[x.core]? = some (I.addrs.getD x.core 0)) :
    RunFacts (fxE P) cs (I.addrs.getD x.core 0) xs (ValTy.flatList x.ty.results)
      (engineOut (core3P P) J x.core xs) (engineDiverges (core3P P) J x.core xs) :=
  ⟨fun h args run => no_callout_fx hC h args run, fun ys run hst => values_fx hC hJs hJa ys run hst,
    fun run hst => trap_fx hC hJs hJa run hst, fun hd => diverges_fx hC hJs hJa hd⟩

end Silmaril.Proofs.Wasm.Component.FXRefE

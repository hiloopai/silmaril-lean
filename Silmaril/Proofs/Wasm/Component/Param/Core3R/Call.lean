module

public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.CallRun

/-!
# The call phase over `core3R P V IR`

`Silmaril.Proofs.Wasm.Component.Reference.CallPath` and the `core3P`-specific sections of
`Silmaril.Proofs.Wasm.Component.Reference.CallRun` (`Core`, `Outcomes`, `Call`, `Main` and
`callPhase`), with `core3P P` replaced by `core3R P V IR` (provenance: copies of these sections).
The only proof changes: a core step of the machine is an `IR` step, which is read as an
`InternalP P` step through `Sub P IR` (`coreSteps_internal`, `diverges_core`); the call context
`CallCtx` carries `Sub P IR` and the lemmas of the core activation take it. The tactic `mstep`
of `Reference.CallPath` is reused.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

/-! ## The call path (`Reference.CallPath`) -/

section Path

variable {P : Profile} {σ : Type}

/-- The engine. -/
abbrev E3 (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) : CoreEngine := core3R P V IR

/-- The dispatcher of the reference host. -/
abbrev D (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) : Call (E3 P V IR) → Canon.P (E3 P V IR) Unit (Ret (E3 P V IR)) :=
  (refHostR P V IR).dispatch

/-- The host caller record of top-level call `0`. -/
def hostCaller (args : List Silmaril.Wasm.Component.Reference.Val) : Caller (E3 P V IR) := .host ⟨0⟩ args 0

theorem runs_allocObj {d : Call (E3 P V IR) → Canon.P (E3 P V IR) σ (Ret (E3 P V IR))} {α Id : Type}
    {th : Option ThreadId} (F : ArenaField (E3 P V IR) Id α) (x : α)
    (m : Machine.Config (E3 P V IR) σ)
    (hl : (ArenaOps.allocSt F x m.store).lockdown = m.store.lockdown) :
    RunsQ d th (allocObj F x) m [.tau, .tau] (F.mkId (F.size m.store))
      { m with store := ArenaOps.allocSt F x m.store } :=
  .get (.modify hl (.pure _ _))


theorem runs_getObj {d : Call (E3 P V IR) → Canon.P (E3 P V IR) σ (Ret (E3 P V IR))} {α Id : Type}
    {th : Option ThreadId} (F : ArenaField (E3 P V IR) Id α) (i : Id)
    (m : Machine.Config (E3 P V IR) σ) {x : α} (h : F.get? m.store i = some x) :
    RunsQ d th (getObj F i) m [.tau] x m := by
  refine .get ?_
  show RunsQ _ _ (match F.get? m.store i with | some x => pure x | none => internal _) _ _ _ _
  rw [h]
  exact .pure _ _

theorem paramTypes_liftedFt (x : SimpleExport) :
    paramTypes (liftedFt x) = toClosedList x.ty.params := labels_map_snd _ _

theorem runs_lower {th : Option ThreadId} (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (cx : LiftLowerContext (E3 P V IR))
    (hf : floatFreeList x.ty.params = true) (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16) (m : Machine.Config (E3 P V IR) Unit) :
    RunsQ (D P V IR) th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams (vs.map toRefVal)
      (paramTypes (liftedFt x)) none) m [.tau]
      (Silmaril.Wasm.Component.lowerArgs x.ty.params vs) m := by
  rw [paramTypes_liftedFt, lowerFlatValues_toClosed (max := ABI.maxFlatParams) _ _ _ hf hck hmax]
  exact .get (.pure _ _)

theorem resultTypes_liftedFt (x : SimpleExport)
    (h : x.ty.results.length ≤ 1) : resultTypes (liftedFt x) = toClosedList x.ty.results := by
  rcases hr : x.ty.results with _ | ⟨t, _ | ⟨u, us⟩⟩
  · simp only [resultTypes, liftedFt, hr, toClosedList]; rfl
  · simp only [resultTypes, liftedFt, hr, toClosedList]; rfl
  · rw [hr] at h; simp at h

theorem runs_lift_some {th : Option ThreadId} (x : SimpleExport)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hff : floatFreeList x.ty.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList x.ty.results)
    {ws : List Silmaril.Wasm.Component.Val} (hws : liftArgs x.ty.results ys = some ws)
    (cx : LiftLowerContext (E3 P V IR)) (m : Machine.Config (E3 P V IR) Unit) :
    ∃ c, RunsQ (D P V IR) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x))) m [.tau] (ws.map toRefVal, c) m := by
  have h := liftFlatTypes_liftArgs (σ := Unit) (E := E3 P V IR) Limits.spec Quirks.none cx
    (ptrTypeIn m.store cx) hff hys
  rw [hws] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [resultTypes_liftedFt x hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
    liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  refine .get ?_
  show RunsQ _ _ (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn m.store cx)
    (toClosedList x.ty.results) ⟨ys, 0⟩) _ _ _ _
  rw [hc]
  exact .pure _ _

theorem lrun_lift_trap {α : Type} {th : Option ThreadId} (prof : ProfileKind) (x : SimpleExport)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hff : floatFreeList x.ty.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList x.ty.results)
    (hnone : liftArgs x.ty.results ys = none)
    {cx : LiftLowerContext (E3 P V IR)} {f : List Silmaril.Wasm.Component.Reference.Val × FlatCursor → Canon.P (E3 P V IR) Unit α}
    {g : α → Canon.P (E3 P V IR) Unit (Ret (E3 P V IR))} {M : Machine.Config (E3 P V IR) Unit}
    {segs : List (Seg (E3 P V IR) Unit)} {rest : List (Activation (E3 P V IR) Unit)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (liftedFt x)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) :
    ∃ mT r, LRun prof (refHostR P V IR).hr (D P V IR) M [.tau] mT ∧ Live mT ∧
      UniqueStep prof (refHostR P V IR).hr (D P V IR) mT (.trap r) (trapCfg mT) := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x)) =
        (ptrType cx >>= fun p => liftFlatTypes Limits.spec Quirks.none cx p
        (toClosedList x.ty.results) ⟨ys, 0⟩ : Canon.P (E3 P V IR) Unit _) := by
    rw [resultTypes_liftedFt x hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := liftFlatTypes_liftArgs (σ := Unit) (E := E3 P V IR) Limits.spec Quirks.none cx
    (ptrTypeIn M.store cx) hff hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P V IR) Unit) .get fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (refHostR P V IR).hr (D P V IR) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn M.store cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.get hc'
  rw [hk] at s₁
  refine ⟨_, r, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl)⟩


/-- The configuration after the host invoked function `j` on `args` from `afterInst`. -/
def invokedCfgH (P : Profile) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (fs : List (CFuncInst (core3R P V IR))) (h : σ) (j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) :
    Machine.Config (E3 P V IR) σ :=
  { afterInstH P V IR cs fs h with
    pending := [] ++ [(⟨0⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨0⟩ ⟨j⟩ args)] }

/-- The configuration after the host invoked function `j` on `args` from `afterInst`. -/
abbrev invokedCfg (P : Profile) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (fs : List (CFuncInst (core3R P V IR))) (j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) : Machine.Config (E3 P V IR) Unit :=
  invokedCfgH P cs fs () j args

/-- From `mS`, the call resolves with `rs`: a live run to a configuration with the host in
control, results `rs`, from which a tick returns to itself. -/
def Resolves (prof : ProfileKind) (P : Profile) (mS : Machine.Config (E3 P V IR) Unit)
    (rs : List Silmaril.Wasm.Component.Reference.Val) : Prop :=
  ∃ tr mE, LRun prof (refHostR P V IR).hr (D P V IR) mS tr mE ∧ mE.ctl = [] ∧
    mE.store.lockdown = false ∧ mE.result? ⟨0⟩ = some (some rs) ∧
    ∀ m₁, Step prof (refHostR P V IR).hr (D P V IR) mE (.host .tick) m₁ →
      ∃ trT, LRun prof (refHostR P V IR).hr (D P V IR) m₁ trT mE

/-- From `mS`, the call traps after one live step. -/
def TrapsNext (prof : ProfileKind) (P : Profile) (mS : Machine.Config (E3 P V IR) Unit) : Prop :=
  ∃ mT r, LRun prof (refHostR P V IR).hr (D P V IR) mS [.tau] mT ∧ Live mT ∧
    UniqueStep prof (refHostR P V IR).hr (D P V IR) mT (.trap r) (trapCfg mT)

/-- The configuration `M₀` runs the core activation of export `x` (address `a`) on the
lowered values of `vs`; when it returns flat values of the result types, the call resolves
or traps as the IR lift prescribes. -/
structure CallAt (prof : ProfileKind) (P : Profile) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P V IR) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P V IR) Unit (Ret (E3 P V IR))) (segs : List (Seg (E3 P V IR) Unit))
    (rest : List (Activation (E3 P V IR) Unit)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ (y : CoreSt (E3 P V IR)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    Resolves prof P (retCfg M₀ th K segs rest y ys) (ws.map toRefVal)
  trap : ∀ (y : CoreSt (E3 P V IR)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNext prof P (retCfg M₀ th K segs rest y ys)

/-- The function value `j` of `fs` is the lift of export `x` at core address `a`. -/
theorem funcs_get? {fs : List (CFuncInst (core3R P V IR))} {j a : Nat} {x : SimpleExport}
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) (s : CStore (E3 P V IR)) (e : s.funcs = fs) :
    ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) := by
  simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
  exact hf

/-- **The deterministic parts of an export call.** -/
theorem call_at (prof : ProfileKind) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (fs : List (CFuncInst (core3R P V IR))) (j a : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (refHostR P V IR).hr (D P V IR)
      (invokedCfg P cs fs j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAt prof P cs x a vs M₀ th K segs rest := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (refHostR P V IR).hr (D P V IR) (invokedCfg P cs fs j (vs.map toRefVal)) _ _
    unfold invokedCfg
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (hostCaller (vs.map toRefVal)) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P V IR), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) :=
      funcs_get? hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk rfl (RunsQ.get (.pure _ _)) rfl
    iterate 14 mstep
    have hlow : ∀ (cx : LiftLowerContext (E3 P V IR)) (m : Machine.Config (E3 P V IR) Unit),
        RunsQ (D P V IR) (some ⟨0⟩) (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
          (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau] (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lower x vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    mstep
    exact .refl _
  apply CallAt.mk
  · rfl
  · rfl
  · rfl
  · show ∀ (y : CoreSt (E3 P V IR)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
      Resolves prof P (retCfg _ _ _ _ _ y ys) (ws.map toRefVal)
    intro y ys ws hys hws
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · unfold retCfg
      apply RunsQ.chunk2 rfl (runs_lift_some x hres hmaxr hffr hys hws _ _).choose_spec rfl
      repeat mstep
      exact .refl _
    refine ⟨rfl, rfl, rfl, ?_⟩
    · intro m₁ hs
      cases hs
      apply Exists.intro
      repeat mstep
      exact .refl _
  · intro y ys hys hn
    exact lrun_lift_trap prof x hres hmaxr hffr hys hn rfl rfl

end Path

/-! ## The core activation of the call -/

section Core

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

/-- A flat callout status is a callout. -/
theorem flatStatus_callout {H : Type} {st : Silmaril.Wasm.SingleThreaded.Status H} {h : H}
    {args : List FlatValue} (hs : flatStatus st = .callout h args) :
    ∃ h' args', st = .callout h' args' := by
  cases st with
  | callout h' args' => exact ⟨h', args', rfl⟩
  | returned r =>
    cases r with
    | values vs =>
      simp only [flatStatus] at hs
      split at hs <;> cases hs
    | trap => cases hs
  | running => cases hs
  | stuck => cases hs

open Silmaril.Wasm.SingleThreaded in
/-- A callout status of `statusP` is a host-call redex. -/
theorem statusP_callout {P : Profile} {H : Type} {s : Silmaril.Wasm.Execution.Core.Store H}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {h : H} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hs : Silmaril.Wasm.Game.statusP P s t = .callout h args) :
    ∃ E a, decompose? s (t.config s).code = some (E, a, h, args) := by
  unfold Silmaril.Wasm.Game.statusP at hs
  dsimp only at hs
  split_ifs at hs
  all_goals
    split at hs
    next E a h₁ args₁ hd =>
      cases hs
      exact ⟨E, a, hd⟩
    next => cases hs

/-- A callout status of `core3R P V IR` is a host-call redex. -/
theorem status_callout {P : Profile} {s : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P V IR))}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {h : CanonHost (E3 P V IR)} {args : List FlatValue}
    (hs : (E3 P V IR).status s t = .callout h args) :
    ∃ E a h' args', Silmaril.Wasm.SingleThreaded.decompose? s (t.config s).code =
      some (E, a, h', args') := by
  obtain ⟨h', args', hst⟩ := flatStatus_callout (H := CanonHost (E3 P V IR)) hs
  obtain ⟨E, a, hd⟩ := statusP_callout hst
  exact ⟨E, a, h', args', hd⟩

variable {P : Profile} {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {a : Nat}
  {xs : List Flat}

/-- Runs of the core activation are runs of the reference engine's threads. -/
theorem coreSteps_internal (hIR : Sub P IR) {y : CoreSt (E3 P V IR)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P V IR))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y) :
    Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P)
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y :=
  Relation.ReflTransGen.mono (fun _ _ h => hIR h.2) _ _ hy

/-- Runs of the core activation are Core runs of the renamed store. -/
theorem coreSteps_run (hIR : Sub P IR) {y : CoreSt (E3 P V IR)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P V IR))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y) :
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke (Store.mapH (fun _ => 0) cs) a
        (xs.map Silmaril.Wasm.SingleThreaded.ofFlat))
      (Config.mapH (fun _ => 0) (y.2.config y.1)) :=
  invoke_steps_mapH _ (internalP_steps (coreSteps_internal hIR hy))

variable {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} {x : SimpleExport} {nm : String}

/-- The core activation never calls out. -/
theorem no_callout (hIR : Sub P IR) (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (ha : a = I.addrs.getD x.core 0)
    (hcore : c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (hxs : xs.map (·.type) = ValTy.flatList x.ty.params) {y : CoreSt (E3 P V IR)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P V IR))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y)
    {h : CanonHost (E3 P V IR)} {args : List FlatValue} (hs : (E3 P V IR).status y.1 y.2 = .callout h args) :
    False := by
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨E, a', h', args', hd⟩ := status_callout hs
  obtain ⟨E', hd'⟩ := decompose?_mapH (fun _ => 0) hd
  have run := coreSteps_run hIR hy
  rw [hcs, ha] at run
  have hxs' : xs.map (·.type) = c.mod.exports[x.core].2.params := by rw [hget]; exact hxs
  have hn := run_no_callout hI hk hxs' run
  have hstore : (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).store =
      Store.mapH (fun _ => 0) y.1 := by
    exact congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  rw [hstore] at hn
  exact absurd (hd'.symm.trans hn) (by simp)

/-- A returned core activation gives an outcome of `coreOut`, with values of the flat
result types. -/
theorem values_coreOut (hIR : Sub P IR) (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (ha : a = I.addrs.getD x.core 0)
    (hcore : c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (hxs : xs.map (·.type) = ValTy.flatList x.ty.params) {y : CoreSt (E3 P V IR)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P V IR))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y)
    {vs : List FlatValue} (hs : (E3 P V IR).status y.1 y.2 = .returned (.values vs)) :
    some vs ∈ coreOut P c.mod x.core xs ∧ vs.map (·.type) = ValTy.flatList x.ty.results := by
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨cvs, hc, hm⟩ := status_values hs
  have run := coreSteps_run hIR hy
  rw [hcs, ha] at run
  have hxs' : xs.map (·.type) = c.mod.exports[x.core].2.params := by rw [hget]; exact hxs
  have ht := run_results_typed hI hk hxs' run hc hm
  rw [hget] at ht
  exact ⟨⟨I, hI, _, .values cvs, run, hc, hm.symm⟩, ht⟩

/-- A trapped core activation gives the outcome `none` of `coreOut`. -/
theorem trap_coreOut (hIR : Sub P IR) (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (ha : a = I.addrs.getD x.core 0) {y : CoreSt (E3 P V IR)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P V IR))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) y)
    (hs : (E3 P V IR).status y.1 y.2 = .returned .trap) : none ∈ coreOut P c.mod x.core xs := by
  obtain ⟨c', res, run, hc, hr⟩ := coreRun_trap (fun _ => (0 : Nat)) (coreSteps_internal hIR hy) hs
  rw [hcs, ha] at run
  exact ⟨I, hI, c', res, run, hc, hr.symm⟩

/-- A divergent core activation diverges in `coreDiverges`. -/
theorem diverges_core (hIR : Sub P IR) (hI : c.mod.IsInst I) (hcs : Store.mapH (fun _ => 0) cs = I.store)
    (ha : a = I.addrs.getD x.core 0)
    (hd : Silmaril.InfiniteTrace (CoreStep (E3 P V IR))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)) :
    coreDiverges P c.mod x.core xs := by
  have hd' := coreRun_diverges (P := P) (fun _ => (0 : Nat))
    (Silmaril.InfiniteTrace.map id (fun _ _ h => hIR h.2) hd)
  rw [hcs, ha] at hd'
  exact ⟨I, hI, hd'⟩

end Core

/-! ## Outcomes -/

section Outcomes

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

variable {P : Profile} {prof : ProfileKind}

/-- A trapped configuration has only the trap outcome. -/
theorem holds_trapCfg {m : Machine.Config (E3 P V IR) Unit} {out : CallOutcome}
    (ho : out.Holds (refHostR P V IR).hr ⟨0⟩ (trapCfg m)) : out = .trap := by
  cases out with
  | resolved r => exact absurd ho.2.1 (by simp)
  | trap => rfl
  | deadlock => exact absurd ho.1.2.1 (by simp)

/-- After a resolving suffix, the only outcome is the resolution. -/
theorem out_of_resolves {m₁ m' : Machine.Config (E3 P V IR) Unit} {rs : List Silmaril.Wasm.Component.Reference.Val}
    {tr : List (Label (E3 P V IR) Unit)} {out : CallOutcome} (hR : Resolves prof P m₁ rs)
    (hs : Steps prof (refHostR P V IR).hr (D P V IR) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (refHostR P V IR).hr ⟨0⟩ m') : out = .resolved (some rs) := by
  obtain ⟨tr₃, mE, hlr, hctl, hlock, hres, htick⟩ := hR
  rcases hlr.inv hs with hl | ⟨tr₄, e, r⟩
  · exact absurd ho (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₄ → CallHostEvent ⟨0⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  have hq := quiet hctl (by rw [hres]; simp) htick _ tr₄ m' le_rfl r hev'
  rcases hq with rfl | hl
  · cases out with
    | resolved r => exact congrArg _ (Option.some.inj (ho.2.2.symm.trans hres))
    | trap => exact absurd (ho.symm.trans hlock) (by decide)
    | deadlock => exact absurd (ho.2.symm.trans hres) (by simp)
  · exact absurd ho (hl.not_holds _ _)

/-- After a trapping suffix, the only outcome is the trap. -/
theorem out_of_trapsNext {m₁ m' : Machine.Config (E3 P V IR) Unit}
    {tr : List (Label (E3 P V IR) Unit)} {out : CallOutcome} (hT : TrapsNext prof P m₁)
    (hs : Steps prof (refHostR P V IR).hr (D P V IR) m₁ tr m')
    (ho : out.Holds (refHostR P V IR).hr ⟨0⟩ m') : out = .trap := by
  obtain ⟨mT, r, hlr, hlive, hu⟩ := hT
  rcases hlr.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  cases r' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    rw [steps_of_locked rfl rfl r''] at ho
    exact holds_trapCfg ho

/-- A resolving suffix does not diverge. -/
theorem resolves_not_diverges {m₁ : Machine.Config (E3 P V IR) Unit} {rs : List Silmaril.Wasm.Component.Reference.Val}
    (hR : Resolves prof P m₁ rs) : ¬ Diverges prof (refHostR P V IR).hr (D P V IR) m₁ := by
  obtain ⟨tr₃, mE, hlr, hctl, -⟩ := hR
  exact fun hd => not_diverges_of_ctl_nil hctl (hlr.diverges hd)

/-- A trapping suffix does not diverge. -/
theorem trapsNext_not_diverges {m₁ : Machine.Config (E3 P V IR) Unit} (hT : TrapsNext prof P m₁) :
    ¬ Diverges prof (refHostR P V IR).hr (D P V IR) m₁ := by
  obtain ⟨mT, r, hlr, -, hu⟩ := hT
  intro hd
  obtain ⟨m', ⟨l, -, s⟩, hd'⟩ := (hlr.diverges hd).unfold
  obtain ⟨-, rfl⟩ := hu.2 _ _ s
  exact not_diverges_trapCfg _ hd'

end Outcomes

/-! ## The call phase -/

section Call

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val}

/-- The static facts of a call of export `x` of `c` on `vs`. -/
structure CallCtx (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) : Prop where
  inst : c.mod.IsInst I
  store : Store.mapH (fun _ => 0) cs = I.store
  core : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)
  typed : ValTy.checkList x.ty.params vs = true
  sub : Sub P IR

/-- The lowered arguments have the flat parameter types. -/
theorem CallCtx.lowered (C : CallCtx P c I cs x vs) :
    (lowerArgs x.ty.params vs).map (·.type) = ValTy.flatList x.ty.params :=
  lowerList_types _ _ C.typed

/-- The specification of a call with typed arguments. -/
theorem CallCtx.spec (C : CallCtx P c I cs x vs) {b : Silmaril.Wasm.Component.Reference.Outcome}
    (h : ∃ r ∈ coreOut P c.mod x.core (lowerArgs x.ty.params vs), b = liftOutcome x.ty r) :
    b ∈ exportSpec P c x vs := by
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd C.typed h)]
  unfold exportSpec
  rw [hl]
  exact .inl h

/-- **Calls after the core activation left it.** -/
theorem exit_spec (C : CallCtx P c I cs x vs) {M₀ : Machine.Config (E3 P V IR) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P V IR) Unit (Ret (E3 P V IR))}
    {segs : List (Seg (E3 P V IR) Unit)} {rest : List (Activation (E3 P V IR) Unit)}
    (hat : CallAt prof P cs x (I.addrs.getD x.core 0) vs M₀ th K segs rest) {y : CoreSt (E3 P V IR)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P V IR))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) y)
    {l : Label (E3 P V IR) Unit} {m₁ m' : Machine.Config (E3 P V IR) Unit} {tr : List (Label (E3 P V IR) Unit)}
    {out : CallOutcome} (hx : CoreExit M₀ th K segs rest y l m₁)
    (hs : Steps prof (refHostR P V IR).hr (D P V IR) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (refHostR P V IR).hr ⟨0⟩ m') : Outcome.ofCall out ∈ exportSpec P c x vs := by
  obtain ⟨nm, hcore⟩ := C.core
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨hout, hty⟩ := values_coreOut C.sub C.inst C.store rfl hcore C.lowered hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      rw [out_of_resolves (hat.ret y ys ws hty hl) hs hev ho]
      exact C.spec ⟨_, hout, by simp only [Outcome.ofCall, liftOutcome, hl]⟩
    | none =>
      rw [out_of_trapsNext (hat.trap y ys hty hl) hs ho]
      exact C.spec ⟨_, hout, by simp only [Outcome.ofCall, liftOutcome, hl]⟩
  · rw [steps_of_locked rfl rfl hs] at ho
    rw [holds_trapCfg ho]
    exact C.spec ⟨_, trap_coreOut C.sub C.inst C.store rfl hy hst, rfl⟩
  · exact (no_callout C.sub C.inst C.store rfl hcore C.lowered hy hst).elim

/-- **Divergence after the core activation left it** is impossible. -/
theorem exit_not_diverges (C : CallCtx P c I cs x vs) {M₀ : Machine.Config (E3 P V IR) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P V IR) Unit (Ret (E3 P V IR))}
    {segs : List (Seg (E3 P V IR) Unit)} {rest : List (Activation (E3 P V IR) Unit)}
    (hat : CallAt prof P cs x (I.addrs.getD x.core 0) vs M₀ th K segs rest) {y : CoreSt (E3 P V IR)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P V IR))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) y)
    {l : Label (E3 P V IR) Unit} {m₁ : Machine.Config (E3 P V IR) Unit}
    (hx : CoreExit M₀ th K segs rest y l m₁) : ¬ Diverges prof (refHostR P V IR).hr (D P V IR) m₁ := by
  obtain ⟨nm, hcore⟩ := C.core
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨-, hty⟩ := values_coreOut C.sub C.inst C.store rfl hcore C.lowered hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws => exact resolves_not_diverges (hat.ret y ys ws hty hl)
    | none => exact trapsNext_not_diverges (hat.trap y ys hty hl)
  · exact not_diverges_trapCfg _
  · exact (no_callout C.sub C.inst C.store rfl hcore C.lowered hy hst).elim

/-- The host invocation from `afterInst`. -/
theorem invoke_inv {fs : List (CFuncInst (core3R P V IR))} {j : Nat} {args : List Silmaril.Wasm.Component.Reference.Val}
    {m : Machine.Config (E3 P V IR) Unit}
    (h : Step prof (refHostR P V IR).hr (D P V IR) (afterInst P V IR cs fs) (.host (.invoke ⟨0⟩ ⟨j⟩ args)) m) :
    m = invokedCfg P cs fs j args := by
  cases h
  rfl

end Call

section Main

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val} {fs : List (CFuncInst (core3R P V IR))} {j : Nat}
  {M₀ : Machine.Config (E3 P V IR) Unit} {th : Option ThreadId}
  {K : List FlatValue → Canon.P (E3 P V IR) Unit (Ret (E3 P V IR))} {segs : List (Seg (E3 P V IR) Unit)}
  {rest : List (Activation (E3 P V IR) Unit)} {tr₁ : List (Label (E3 P V IR) Unit)}

/-- The specification of a divergent call with typed arguments. -/
theorem CallCtx.spec_diverges (C : CallCtx P c I cs x vs)
    (h : coreDiverges P c.mod x.core (lowerArgs x.ty.params vs)) :
    .diverges ∈ exportSpec P c x vs := by
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd C.typed h)]
  unfold exportSpec
  rw [hl]
  exact .inr ⟨rfl, h⟩

/-- **Terminating calls** follow the specification. -/
theorem calls_spec (C : CallCtx P c I cs x vs)
    (hpre : LRun prof (refHostR P V IR).hr (D P V IR) (invokedCfg P cs fs j (vs.map toRefVal)) tr₁ M₀)
    (hat : CallAt prof P cs x (I.addrs.getD x.core 0) vs M₀ th K segs rest)
    {m' : Machine.Config (E3 P V IR) Unit} {out : CallOutcome}
    (hcalls : Calls prof (refHostR P V IR).hr (D P V IR) (afterInst P V IR cs fs) ⟨0⟩ ⟨j⟩ (vs.map toRefVal) m'
      out) : Outcome.ofCall out ∈ exportSpec P c x vs := by
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, s, r⟩ := Steps.cons_iff.mp hs
  rw [invoke_inv s] at r
  rcases hpre.inv r with hl | ⟨tr'', e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  rw [eq_coreCfg hat.ctl, hat.core] at r'
  rcases coreCfg_steps_inv r' with ⟨y, -, rfl, -⟩ | ⟨y, pre, l, m₁, tr₂, hy, -, e', hx, r''⟩
  · have hl : Live (coreCfg M₀ th K segs rest y) := ⟨List.cons_ne_nil _ _, hat.lock⟩
    exact absurd ho (hl.not_holds _ _)
  · have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev := fun ev hm =>
      hev ev (by rw [e, e']; exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_cons_of_mem _ hm)))
    exact exit_spec C hat hy hx r'' hev' ho

/-- **Divergent calls** follow the specification. -/
theorem diverges_spec (C : CallCtx P c I cs x vs)
    (hpre : LRun prof (refHostR P V IR).hr (D P V IR) (invokedCfg P cs fs j (vs.map toRefVal)) tr₁ M₀)
    (hat : CallAt prof P cs x (I.addrs.getD x.core 0) vs M₀ th K segs rest)
    (hd : CallDiverges prof (refHostR P V IR).hr (D P V IR) (afterInst P V IR cs fs) ⟨0⟩ ⟨j⟩ (vs.map toRefVal)) :
    coreDiverges P c.mod x.core (lowerArgs x.ty.params vs) := by
  obtain ⟨m₂, s, hd⟩ := hd
  rw [invoke_inv s] at hd
  have hd₀ := hpre.diverges hd
  rw [eq_coreCfg hat.ctl, hat.core] at hd₀
  rcases coreCfg_diverges_inv hd₀ with hi | ⟨y, l, m₁, hy, hx, hd'⟩
  · exact diverges_core C.sub C.inst C.store rfl hi
  · exact (exit_not_diverges C hat hy hx hd').elim

/-- The `j`-th lifted function. -/
theorem liftedFuncs_get? (c : Simple) (addr : Nat → Nat) {j : Nat}
    (hj : j < c.exports.length) :
    (liftedFuncs P V IR addr c)[j]? =
      some (.lifted (addr c.exports[j].core) (liftedFt c.exports[j]) {} ⟨0⟩) := by
  simp only [liftedFuncs, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]

end Main

/-- **The call phase of `RefToSpecAll`.** -/
theorem callPhase : CallPhase := by
  intro P V IR hIR prof c hc hf ha I cs hI hcs j hj vs hvs b hb
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem hj
  have C : CallCtx P c I cs c.exports[j] vs := ⟨hI, hcs, hc.core _ hx, hvs, hIR⟩
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_at prof cs _ j _ c.exports[j] vs hff hvs
    hmax hres hmaxr hffr (liftedFuncs_get? c (fun k => I.addrs.getD k 0) hj)
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, hd⟩
  · exact calls_spec C hpre hat hcalls
  · exact C.spec_diverges (diverges_spec C hpre hat hd)

end Silmaril.Proofs.Wasm.Component.Param.Core3R

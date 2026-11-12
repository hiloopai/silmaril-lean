module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallPhaseI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallPhaseKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.FloatPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLink
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkNames
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstNest
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCallout
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkExp
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkPlay
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSeg
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSegs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Seq
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Sound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.SoundSeqI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.LinkCall` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.LinkCall` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P V IR) σ}

/-- From `mS`, the call resolves with `rs` under `DI P impl`. -/
def ResolvesD (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P V IR) σ)
    (mS : Machine.Config (E3 P V IR) σ) (rs : List Val) : Prop :=
  ∃ tr mE, LRun prof (fun _ _ => false) (DI P impl) mS tr mE ∧ mE.ctl = [] ∧
    mE.store.lockdown = false ∧ mE.result? ⟨0⟩ = some (some rs) ∧
    ∀ m₁, Step prof (fun _ _ => false) (DI P impl) mE (.host .tick) m₁ →
      ∃ trT, LRun prof (fun _ _ => false) (DI P impl) m₁ trT mE

/-- The configuration with three component instances, the host in control. -/
def after3 (P : Profile) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (fs : List (CFuncInst (core3R P V IR))) (h : σ) : Machine.Config (E3 P V IR) σ :=
  Config.init { core := cs, insts := [{}, {}, {}], funcs := fs } h

/-- The configuration after the host invoked function `j` on `args` from `after3`. -/
def invoked3 (P : Profile) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (fs : List (CFuncInst (core3R P V IR))) (h : σ) (j : Nat) (args : List Val) :
    Machine.Config (E3 P V IR) σ :=
  { after3 P cs fs h with
    pending := [] ++ [(⟨0⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨0⟩ ⟨j⟩ args)] }

theorem invoke_inv3 {cs : (core3R P V IR).Store (CanonHost (core3R P V IR))} {fs : List (CFuncInst (core3R P V IR))}
    {h₀ : σ} {j : Nat} {args : List Val} {m : Machine.Config (E3 P V IR) σ}
    (h : Step prof (fun _ _ => false) (DI P impl) (after3 P cs fs h₀)
      (.host (.invoke ⟨0⟩ ⟨j⟩ args)) m) :
    m = invoked3 P cs fs h₀ j args := by
  cases h
  rfl

/-- The configuration `M₀` runs the importer's core activation of export `x` (address `a`) on
the lowered values of `vs`, in a frame for `lsegs_inv`; from every extension of it by nested
calls, a return of flat values of the result types resolves the call or traps, as the IR lift
prescribes. -/
structure CallAtL (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P V IR) σ)
    (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (fs : List (CFuncInst (core3R P V IR)))
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P V IR) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P V IR) σ (Ret (E3 P V IR))) (segs : List (Seg (E3 P V IR) σ))
    (rest : List (Activation (E3 P V IR) σ)) : Prop where
  start : M₀ = coreCfg (extN M₀ {} [] M₀.conts) th K segs rest
    (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs x.ty.params vs))
  funcs : M₀.store.funcs = fs
  frame : LFrame M₀ th
  ret : ∀ (ιe : InstState) (N : List (NRec P V IR)) (C : List (Option (Activation (E3 P V IR) σ)))
    (y : CoreSt (E3 P V IR)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesD prof P impl (retCfg (extN M₀ ιe N C) th K segs rest y ys) (ws.map toRefVal)
  trap : ∀ (ιe : InstState) (N : List (NRec P V IR)) (C : List (Option (Activation (E3 P V IR) σ)))
    (y : CoreSt (E3 P V IR)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextD prof P impl (retCfg (extN M₀ ιe N C) th K segs rest y ys)

/-! ## The importer's records first in their arenas -/

theorem tasks_get_head {s : CStore (E3 P V IR)} {y : Runtime.Task (E3 P V IR)} {R : List (Runtime.Task (E3 P V IR))}
    (h : s.tasks = y :: R) : ArenaField.tasks.get? s (⟨0⟩ : TaskId) = some y := by
  show (s.tasks)[0]? = some y
  rw [h]
  rfl

theorem threads_get_head {s : CStore (E3 P V IR)} {z : Runtime.Thread} {R : List Runtime.Thread}
    (h : s.threads = z :: R) : ArenaField.threads.get? s (⟨0⟩ : ThreadId) = some z := by
  show (s.threads)[0]? = some z
  rw [h]
  rfl

/-- `Task.return_` of the first task, whose caller is the first, a host caller record. -/
theorem runs_returnH {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {y : Runtime.Task (E3 P V IR)} {R : List (Runtime.Task (E3 P V IR))} {CL : List (Caller (E3 P V IR))}
    {c : CallId} {args : List Val} (vs : List Val) (ht : m.store.tasks = y :: R)
    (hy : y.caller = ⟨0⟩) (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = .host c args 0 :: CL) :
    RunsQ (DI P impl) th (Task.return_ ⟨0⟩ vs) m
      [.tau, .tau, .tau, .obs (.resolved c (some vs)), .tau, .tau] ()
      { m.resolve c (some vs) with
        store := CStore.setTaskState ⟨0⟩ .resolved m.store } := by
  have hc' : m.store.callers = ([] : List (Caller (E3 P V IR))) ++ [.host c args 0] ++ CL := hc
  unfold Task.return_
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_head ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; rfl) _ _)
  apply RunsQ.bind (runs_trapIf (by rw [hb]; rfl) _ _)
  rw [hy]
  unfold callUnit callRet perform Prog.lift
  apply RunsQ.bind (RunsQ.call (runs_onResolveSC (Gc := []) (some vs) hc') (.pure _ _))
  exact runs_modifyStore _ _ rfl
  rfl

theorem runs_unregisterH {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {y : Runtime.Task (E3 P V IR)} {R : List (Runtime.Task (E3 P V IR))} {z : Runtime.Thread}
    {R' : List Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = y :: R) (hst : y.state = .resolved)
    (hthr : m.store.threads = z :: R') (hidx : z.index = some i)
    (hi : ArenaField.insts.get? m.store y.inst = some ι) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.unregisterThread ⟨0⟩ ⟨0⟩) m [.tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨0⟩ ⟨0⟩ i m.store } := by
  unfold Task.unregisterThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_head ht))
  apply RunsQ.bind (runs_trapIf (by rw [hst]; simp) _ _)
  apply RunsQ.bind (runs_getObj ArenaField.threads _ _ (threads_get_head hthr))
  rw [hidx]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind (runs_getObj ArenaField.insts _ _ hi)
  rw [hrem]
  exact runs_modifyStore _ _ (CStore.unregisterThreadSt_frame (E := E3 P V IR) _ _ _ _).2.2.2.2.2.2.2.1
  rfl

theorem runs_exitH {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {y : Runtime.Task (E3 P V IR)} {R : List (Runtime.Task (E3 P V IR))} {z : Runtime.Thread}
    {R' : List Runtime.Thread} {ι ι' : InstState} {i : Nat} {t' : ThreadId}
    (ht : m.store.tasks = y :: R) (himp : y.implicitThread = some ⟨0⟩)
    (hst : y.state = .resolved) (hasync : y.ft.async_ = false)
    (hthr : m.store.threads = z :: R') (hidx : z.index = some i)
    (hi : ArenaField.insts.get? m.store y.inst = some ι) (hrem : ι.removeThread? i = some (t', ι')) :
    RunsQ (DI P impl) th (Task.exitImplicitThread ⟨0⟩) m [.tau, .tau, .tau, .tau, .tau] ()
      { m with store := CStore.unregisterThreadSt ⟨0⟩ ⟨0⟩ i m.store } := by
  have hu := runs_unregisterH (impl := impl) (th := th) ht hst hthr hidx hi hrem
  unfold Task.exitImplicitThread
  apply RunsQ.of_tr
  apply RunsQ.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_head ht))
  rw [himp]
  apply RunsQ.bind (.pure _ _)
  apply RunsQ.bind hu
  exact runs_ite_false (by rw [hasync]; rfl) _ _
  rfl

theorem runs_callUnit_loopH {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ}
    {y : Runtime.Task (E3 P V IR)} {R : List (Runtime.Task (E3 P V IR))}
    (ht : m.store.tasks = y :: R) (hst : y.state = .resolved) :
    RunsQ (DI P impl) th (callUnit (.loop (.syncLiftLoop ⟨0⟩))) m [.tau, .tau, .tau] () m := by
  have hl : RunsQ (DI P impl) th (DI P impl (.loop (.syncLiftLoop ⟨0⟩))) m [.tau] .unit m := by
    show RunsQ _ _ (syncLiftLoopBody (fun _ _ => false) ⟨0⟩) _ _ _ _
    unfold syncLiftLoopBody
    apply RunsQ.bind (tr₂ := []) (runs_getObj ArenaField.tasks _ _ (tasks_get_head ht))
    rw [hst]
    exact .pure _ _
  unfold callUnit callRet perform Prog.lift
  exact RunsQ.call hl (.pure _ _)

/-- The importer's task of the call, its implicit thread `0` registered. -/
def taskL (x : SimpleExport) : Runtime.Task (E3 P V IR) :=
  ({ ft := liftedFt x, opts := {}, inst := ⟨2⟩, caller := ⟨0⟩, implicitThread := some ⟨0⟩ } :
    Runtime.Task (E3 P V IR)).addThreadR ⟨0⟩

/-- The importer's task once the call returned and its thread exited. -/
def taskRetL (x : SimpleExport) : Runtime.Task (E3 P V IR) :=
  { (((taskL (P := P) (V := V) (IR := IR) x).withState .started).withState .resolved) with
    threads := (((taskL (P := P) (V := V) (IR := IR) x).withState .started).withState .resolved).threads.erase ⟨0⟩ }

/-- The store of the call with the nested calls' records `N`: the exporter's instance state `ιe`,
the importer's `ιi`, the importer's task `tk` and thread `thr` first. -/
def storeLN (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3R P V IR))) (tk : Runtime.Task (E3 P V IR)) (thr : Runtime.Thread)
    (args : List Val) (N : List (NRec P V IR)) : CStore (E3 P V IR) :=
  { core := cs, insts := [{}, ιe, ιi], funcs := fs, tasks := tk :: N.map (·.task),
    threads := thr :: N.map (·.thread), callers := .host ⟨0⟩ args 0 :: N.map (·.caller),
    subtasks := N.map (·.sub), nestingDepth := 1 }

/-- **The deterministic parts of the importer's top-level call** from `after3`. -/
theorem call_atL (prof : ProfileKind) (cs : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (fs : List (CFuncInst (core3R P V IR))) (h₀ : σ) (j a : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨2⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (fun _ _ => false) (DI P impl)
      (invoked3 P cs fs h₀ j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtL prof P impl cs fs x a vs M₀ th K segs rest := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (fun _ _ => false) (DI P impl) (invoked3 P cs fs h₀ j (vs.map toRefVal)) _ _
    unfold invoked3
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (hostCaller (vs.map toRefVal)) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P V IR), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨2⟩) := by
      intro s e
      simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
      exact hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk rfl (RunsQ.get (.pure _ _)) rfl
    iterate 14 mstep
    have hlow : ∀ (cx : LiftLowerContext (E3 P V IR)) (m : Machine.Config (E3 P V IR) σ),
        RunsQ (DI P impl) (some ⟨0⟩) (lowerFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatParams (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau]
          (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lowerP x.ty vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    mstep
    apply LRun.store_congr (S' := storeLN cs {} (enterInst {} ⟨0⟩) fs
      ((taskL x).withState .started) threadL (vs.map toRefVal) []) rfl
    exact .refl _
  apply CallAtL.mk
  · rfl
  · rfl
  · exact ⟨fun _ _ _ _ _ => rfl, ⟨_, rfl, rfl⟩⟩
  · show ∀ (ιe : InstState) (N : List (NRec P V IR)) (C : List (Option (Activation (E3 P V IR) σ)))
      (y : CoreSt (E3 P V IR)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
      ResolvesD prof P impl (retCfg (extN _ ιe N C) _ _ _ _ y ys) (ws.map toRefVal)
    intro ιe N C y ys ws hys hws
    have hlift : ∀ (cx : LiftLowerContext (E3 P V IR)) (m : Machine.Config (E3 P V IR) σ), ∃ c,
        RunsQ (DI P impl) (some ⟨0⟩) (liftFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatResults (.ofList ys) (resultTypes (witFt x.ty))) m [.tau]
          (ws.map toRefVal, c) m :=
      runs_lift_someP x.ty hres hmaxr hffr hys hws
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · show LRun prof (fun _ _ => false) (DI P impl) (retCfg _ _ _ _ _ y ys) _ _
      apply LRun.store_congr (S' := storeLN y.1 ιe (enterInst {} ⟨0⟩) fs
        ((taskL x).withState .started) threadL (vs.map toRefVal) N) rfl
      unfold retCfg
      apply RunsQ.chunk2 rfl (hlift _ _).choose_spec rfl
      apply RunsQ.chunk2 rfl (runs_returnH (CL := N.map (·.caller)) _ rfl rfl rfl rfl rfl) rfl
      apply LRun.store_congr (S' := storeLN y.1 ιe (enterInst {} ⟨0⟩) fs
        (((taskL x).withState .started).withState .resolved) threadL (vs.map toRefVal) N) rfl
      have hrem : (enterInst ({} : InstState) ⟨0⟩).removeThread? 1 =
          some (⟨0⟩, InstState.removeThread 1 (enterInst {} ⟨0⟩)) := removeThread?_enter {} ⟨0⟩
      apply RunsQ.chunk rfl (runs_exitH rfl rfl rfl rfl rfl rfl rfl hrem) rfl
      apply LRun.store_congr (S' := storeLN y.1 ιe (InstState.removeThread 1 (enterInst {} ⟨0⟩)) fs
        (taskRetL x) threadL (vs.map toRefVal) N) rfl
      mstep
      apply LRun.store_congr (S' := storeLN y.1 ιe (InstState.removeThread 1 (enterInst {} ⟨0⟩)) fs
        (taskRetL x) { threadL with status := .exited } (vs.map toRefVal) N) rfl
      have hloop : ∀ (th : Option ThreadId) (m : Machine.Config (E3 P V IR) σ),
          m.store.tasks = taskRetL x :: N.map (·.task) →
          RunsQ (DI P impl) th (callUnit (.loop (.syncLiftLoop ⟨0⟩))) m [.tau, .tau, .tau] () m :=
        fun _ _ h => runs_callUnit_loopH h rfl
      apply RunsQ.chunk rfl (hloop _ _ rfl) rfl
      iterate 3 mstep
      exact .refl _
    refine ⟨rfl, rfl, rfl, ?_⟩
    show ∀ m₁, Step prof (fun _ _ => false) (DI P impl) _ (.host .tick) m₁ →
      ∃ trT, LRun prof (fun _ _ => false) (DI P impl) m₁ trT _
    intro m₁ hs
    cases hs
    apply Exists.intro
    repeat mstep
    exact .refl _
  · intro ιe N C y ys hys hn
    exact lrun_lift_trapP x.ty hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Param.Core3R

module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkPlay
public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkCore
public import Silmaril.Proofs.Wasm.Component.Reference.CallPhaseI
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The top-level call of a linked component

From the configuration after instantiating `Linked2.toRef` (`afterLink`: three component
instances, the exporter's lifted functions then the importer's), the host's invocation of the
importer's lifted export `j` runs, over the dispatcher `DI P impl` (no ready host waitables),
deterministically to the importer's core activation (`call_atL`) in instance `2`. Its frame
`M₀` is an `LFrame` whose exporter instance state has a reusable thread table, so `lsegs_inv`
applies from it. From any extension `extN M₀ ιe N C` of the frame by nested calls, a return of
flat values of the result types resolves the call with the lifted results, or traps where the
lift fails (`CallAtL.ret`, `CallAtL.trap`): the importer's task, thread and caller record are
the first of their arenas, the nested calls' records come after them.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- From `mS`, the call resolves with `rs` under `DI P impl`. -/
def ResolvesD (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (mS : Machine.Config (E3 P) σ) (rs : List Silmaril.Wasm.Component.Reference.Val) : Prop :=
  ∃ tr mE, LRun prof (fun _ _ => false) (DI P impl) mS tr mE ∧ mE.ctl = [] ∧
    mE.store.lockdown = false ∧ mE.result? ⟨0⟩ = some (some rs) ∧
    ∀ m₁, Step prof (fun _ _ => false) (DI P impl) mE (.host .tick) m₁ →
      ∃ trT, LRun prof (fun _ _ => false) (DI P impl) m₁ trT mE

/-- The configuration with three component instances, the host in control. -/
def after3 (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h : σ) : Machine.Config (E3 P) σ :=
  Config.init { core := cs, insts := [{}, {}, {}], funcs := fs } h

/-- The configuration after the host invoked function `j` on `args` from `after3`. -/
def invoked3 (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h : σ) (j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) :
    Machine.Config (E3 P) σ :=
  { after3 P cs fs h with
    pending := [] ++ [(⟨0⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨0⟩ ⟨j⟩ args)] }

theorem afterLink_eq (cs : (core3P P).Store (CanonHost (core3P P))) (addrE addrI : Nat → Nat)
    (l : Linked2) (h : σ) :
    afterLink P cs addrE addrI l h = after3 P cs
      (liftedList addrE ⟨1⟩ l.exp.exports ++ liftedList addrI ⟨2⟩ l.imp.exports) h := rfl

theorem invoke_inv3 {cs : (core3P P).Store (CanonHost (core3P P))} {fs : List (CFuncInst (core3P P))}
    {h₀ : σ} {j : Nat} {args : List Silmaril.Wasm.Component.Reference.Val} {m : Machine.Config (E3 P) σ}
    (h : Step prof (fun _ _ => false) (DI P impl) (after3 P cs fs h₀)
      (.host (.invoke ⟨0⟩ ⟨j⟩ args)) m) :
    m = invoked3 P cs fs h₀ j args := by
  cases h
  rfl

/-- The configuration `M₀` runs the importer's core activation of export `x` (address `a`) on
the lowered values of `vs`, in a frame for `lsegs_inv`; from every extension of it by nested
calls, a return of flat values of the result types resolves the call or traps, as the IR lift
prescribes. -/
structure CallAtL (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (cs : (core3P P).Store (CanonHost (core3P P))) (fs : List (CFuncInst (core3P P)))
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop where
  start : M₀ = coreCfg (extN M₀ {} [] M₀.conts) th K segs rest
    (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs x.ty.params vs))
  funcs : M₀.store.funcs = fs
  frame : LFrame M₀ th
  ret : ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesD prof P impl (retCfg (extN M₀ ιe N C) th K segs rest y ys) (ws.map toRefVal)
  trap : ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextD prof P impl (retCfg (extN M₀ ιe N C) th K segs rest y ys)

theorem threadsOk_empty : ThreadsOk ({} : InstState) := .inl rfl

/-! ## The importer's records first in their arenas -/

theorem tasks_get_head {s : CStore (E3 P)} {y : Runtime.Task (E3 P)} {R : List (Runtime.Task (E3 P))}
    (h : s.tasks = y :: R) : ArenaField.tasks.get? s (⟨0⟩ : TaskId) = some y := by
  show (s.tasks)[0]? = some y
  rw [h]
  rfl

theorem threads_get_head {s : CStore (E3 P)} {z : Runtime.Thread} {R : List Runtime.Thread}
    (h : s.threads = z :: R) : ArenaField.threads.get? s (⟨0⟩ : ThreadId) = some z := by
  show (s.threads)[0]? = some z
  rw [h]
  rfl

/-- `Task.return_` of the first task, whose caller is the first, a host caller record. -/
theorem runs_returnH {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {y : Runtime.Task (E3 P)} {R : List (Runtime.Task (E3 P))} {CL : List (Caller (E3 P))}
    {c : CallId} {args : List Silmaril.Wasm.Component.Reference.Val} (vs : List Silmaril.Wasm.Component.Reference.Val) (ht : m.store.tasks = y :: R)
    (hy : y.caller = ⟨0⟩) (hst : y.state = .started) (hb : y.numBorrows = 0)
    (hc : m.store.callers = .host c args 0 :: CL) :
    RunsQ (DI P impl) th (Task.return_ ⟨0⟩ vs) m
      [.tau, .tau, .tau, .obs (.resolved c (some vs)), .tau, .tau] ()
      { m.resolve c (some vs) with
        store := CStore.setTaskState ⟨0⟩ .resolved m.store } := by
  have hc' : m.store.callers = ([] : List (Caller (E3 P))) ++ [.host c args 0] ++ CL := hc
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

theorem runs_unregisterH {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {y : Runtime.Task (E3 P)} {R : List (Runtime.Task (E3 P))} {z : Runtime.Thread}
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
  exact runs_modifyStore _ _ (CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.2.1
  rfl

theorem runs_exitH {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {y : Runtime.Task (E3 P)} {R : List (Runtime.Task (E3 P))} {z : Runtime.Thread}
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

theorem runs_callUnit_loopH {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {y : Runtime.Task (E3 P)} {R : List (Runtime.Task (E3 P))}
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
def taskL (x : SimpleExport) : Runtime.Task (E3 P) :=
  ({ ft := liftedFt x, opts := {}, inst := ⟨2⟩, caller := ⟨0⟩, implicitThread := some ⟨0⟩ } :
    Runtime.Task (E3 P)).addThread ⟨0⟩

/-- The importer's task once the call returned and its thread exited. -/
def taskRetL (x : SimpleExport) : Runtime.Task (E3 P) :=
  { (((taskL (P := P) x).withState .started).withState .resolved) with
    threads := (((taskL (P := P) x).withState .started).withState .resolved).threads.erase ⟨0⟩ }

/-- The importer's thread of the call. -/
def threadL : Runtime.Thread := { status := .running, task := ⟨0⟩, index := some 1 }

/-- The store of the call with the nested calls' records `N`: the exporter's instance state `ιe`,
the importer's `ιi`, the importer's task `tk` and thread `thr` first. -/
def storeLN (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState)
    (fs : List (CFuncInst (core3P P))) (tk : Runtime.Task (E3 P)) (thr : Runtime.Thread)
    (args : List Silmaril.Wasm.Component.Reference.Val) (N : List (NRec P)) : CStore (E3 P) :=
  { core := cs, insts := [{}, ιe, ιi], funcs := fs, tasks := tk :: N.map (·.task),
    threads := thr :: N.map (·.thread), callers := .host ⟨0⟩ args 0 :: N.map (·.caller),
    subtasks := N.map (·.sub), nestingDepth := 1 }

/-- **The deterministic parts of the importer's top-level call** from `after3`. -/
theorem call_atL (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h₀ : σ) (j a : Nat) (x : SimpleExport)
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
    have hget : ∀ s : CStore (E3 P), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨2⟩) := by
      intro s e
      simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
      exact hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk rfl (RunsQ.get (.pure _ _)) rfl
    iterate 14 mstep
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ),
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
  · show ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
      (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
      ResolvesD prof P impl (retCfg (extN _ ιe N C) _ _ _ _ y ys) (ws.map toRefVal)
    intro ιe N C y ys ws hys hws
    have hlift : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ), ∃ c,
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
      have hloop : ∀ (th : Option ThreadId) (m : Machine.Config (E3 P) σ),
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

end Silmaril.Proofs.Wasm.Component.Reference

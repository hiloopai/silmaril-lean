module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Nested

/-!
# Forward runs of a linked call: specification traps

`Calls` (`Embedding.Defs`) accepts a trap outcome only from a trace without `internal` faults.
The backward lemmas of a linked call (`TrapStore`) record the traps of failing lifts as
`TrapsAt`, a live run to some trap, without its reason. The forward direction needs the reason:
the traps of the reference lift of IR types are `invalidChar` and `invalidDiscriminant`
(`Adequacy.liftFlatTypes_liftArgsS`, `Adequacy.IsSpecTrap`). Here the trapping runs of
`TrapStore` are restated with specification traps, the proofs those of `TrapStore` and
`LinkCallout` with `IsSpecTrap` in place of `IsTrap`:

* `TrapsQS`: `TrapsQ` (big-step runs to a trap) whose trap is a specification trap;
  `TrapsQS.lrun`: a live run to a configuration whose only step is that trap;
* `TrapsAtS M c`: `TrapsAt` with a specification trap;
* `traps_lowerOnStartS`, `traps_startLTS`, `lift_body_trapTS`, `nest_trap_argsTS`: a callout of
  the importer whose arguments do not lift;
* `lrun_lift_trapAtS`, `lift_body_atTS`, `nest_atTS`: results of the exporter that do not lift;
* `CallAtLKTS`, `call_atLKTS`: results of the importer that do not lift.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

/-! ## Big-step runs to a specification trap -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

variable (dispatch) in
/-- `TrapsQ` whose trap is a specification trap (`Adequacy.IsSpecTrap`). -/
inductive TrapsQS : {α : Type} → Option ThreadId → Canon.P E σ α → Config E σ →
    List (Label E σ) → Config E σ → Prop where
  | trap {α : Type} {th : Option ThreadId} {p : Canon.P E σ α} (m : Config E σ) :
      Adequacy.IsSpecTrap p → TrapsQS th p m [] m
  | bind {α β : Type} {th : Option ThreadId} {p : Canon.P E σ α} {f : α → Canon.P E σ β}
      {m m₁ mT : Config E σ} {tr₁ tr₂ : List (Label E σ)} {a : α} :
      RunsQ dispatch th p m tr₁ a m₁ → TrapsQS th (f a) m₁ tr₂ mT →
      TrapsQS th (p >>= f) m (tr₁ ++ tr₂) mT
  | left {α β : Type} {th : Option ThreadId} {p : Canon.P E σ α} {f : α → Canon.P E σ β}
      {m mT : Config E σ} {tr : List (Label E σ)} :
      TrapsQS th p m tr mT → TrapsQS th (p >>= f) m tr mT
  | callIn {α : Type} {th : Option ThreadId} {c : Call E} {k : Ret E → Canon.P E σ α}
      {m mT : Config E σ} {tr : List (Label E σ)} :
      TrapsQS th (dispatch c) m tr mT → TrapsQS th (callRet c >>= k) m (.tau :: tr) mT

namespace TrapsQS

theorem lock {α : Type} {th : Option ThreadId} {p : Canon.P E σ α} {m mT : Config E σ}
    {tr : List (Label E σ)} (h : TrapsQS dispatch th p m tr mT) :
    mT.store.lockdown = m.store.lockdown := by
  induction h with
  | trap => rfl
  | bind h₁ _ ih => exact ih.trans h₁.lock
  | left _ ih => exact ih
  | callIn _ ih => exact ih

/-- `TrapsQ.lrun`, the trap a specification trap. -/
theorem lrun {α : Type} {th : Option ThreadId} {p : Canon.P E σ α} {m mT : Config E σ}
    {tr : List (Label E σ)} (h : TrapsQS dispatch th p m tr mT) :
    m.store.lockdown = false →
    ∀ (f : α → Canon.P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
      ∃ (q : Canon.P E σ (Ret E)) (segs' : List (Seg E σ)) (r : TrapReason),
        (∀ msg, r ≠ .internal msg) ∧
        LRun prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
          { mT with ctl := ⟨th, .prog q, segs'⟩ :: rest } ∧
        Live ({ mT with ctl := ⟨th, .prog q, segs'⟩ :: rest } : Config E σ) ∧
        UniqueStep prof hr dispatch { mT with ctl := ⟨th, .prog q, segs'⟩ :: rest } (.trap r)
          (trapCfg { mT with ctl := ⟨th, .prog q, segs'⟩ :: rest }) := by
  induction h with
  | @trap _ th p m hp =>
    intro hl f segs rest
    obtain ⟨r, k, hr', rfl⟩ := hp
    exact ⟨_, segs, r, hr', .refl _, RunsQ.live_op hl,
      .of_prog rfl (fun _ _ e => by cases e) (.trap (k := fun e => k e >>= f) rfl)⟩
  | @bind _ _ th p f₀ m m₁ mT tr₁ tr₂ a h₁ _ ih =>
    intro hl f segs rest
    have hl₁ : m₁.store.lockdown = false := h₁.lock.trans hl
    obtain ⟨q, segs', r, hr', hrun, hlive, hu⟩ := ih hl₁ f segs rest
    have d₁ := h₁.lrun (prof := prof) (hr := hr) hl (fun a => f₀ a >>= f) segs rest
    have e : (p >>= f₀) >>= f = p >>= fun a => f₀ a >>= f := by
      rw [Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
      rfl
    rw [e]
    exact ⟨q, segs', r, hr', d₁.trans hrun, hlive, hu⟩
  | @left _ _ th p f₀ m mT tr _ ih =>
    intro hl f segs rest
    have e : (p >>= f₀) >>= f = p >>= fun a => f₀ a >>= f := by
      rw [Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
      rfl
    rw [e]
    exact ih hl (fun a => f₀ a >>= f) segs rest
  | @callIn _ th c k m mT tr _ ih =>
    intro hl f segs rest
    obtain ⟨q, segs', r, hr', hrun, hlive, hu⟩ := ih hl Prog.pure
      (.prog (fun r => k r >>= f) :: segs) rest
    have s₁ : UniqueStep prof hr dispatch
        { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.call c) fun r => k r >>= f), segs⟩ ::
          rest }
        .tau { m with ctl := ⟨th, .prog (dispatch c), .prog (fun r => k r >>= f) :: segs⟩ ::
          rest } :=
      .of_prog rfl (fun _ _ e => by cases e) (.call (k := fun r => k r >>= f) rfl)
    rw [Prog.bind_eq, Prog.bind_pure] at hrun
    exact ⟨q, segs', r, hr', .cons (RunsQ.live_op hl) s₁ hrun, hlive, hu⟩

end TrapsQS

end Generic

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- Big-step runs to a trap do not read or write the control chain. -/
theorem TrapsQS.withCtl {d : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))} {α : Type}
    {th : Option ThreadId} {p : Canon.P (E3 P) σ α} {m mT : Machine.Config (E3 P) σ}
    {tr : List (Label (E3 P) σ)} (h : TrapsQS d th p m tr mT) (c : List (Activation (E3 P) σ)) :
    TrapsQS d th p { m with ctl := c } tr { mT with ctl := c } := by
  induction h with
  | trap _ hp => exact .trap _ hp
  | bind h₁ _ ih => exact .bind (h₁.withCtl c) ih
  | left _ ih => exact .left ih
  | callIn _ ih => exact .callIn ih

/-! ## Specification traps at a core store -/

/-- `TrapsAt` with a specification trap: from `M`, a live run reaches a configuration holding
the core store `c` whose only step is a specification trap. -/
def TrapsAtS (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (M : Machine.Config (E3 P) σ) (c : (E3 P).Store (CanonHost (E3 P))) : Prop :=
  ∃ tr mT r, (∀ msg, r ≠ .internal msg) ∧ LRun prof (fun _ _ => false) (DI P impl) M tr mT ∧
    Live mT ∧ UniqueStep prof (fun _ _ => false) (DI P impl) mT (.trap r) (trapCfg mT) ∧
    mT.core = c

theorem TrapsAtS.lrun {M M' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    {c : (E3 P).Store (CanonHost (E3 P))}
    (h : LRun prof (fun _ _ => false) (DI P impl) M tr M') (h' : TrapsAtS prof P impl M' c) :
    TrapsAtS prof P impl M c := by
  obtain ⟨tr', mT, r, hr, h₁, hl, hu, hc⟩ := h'
  exact ⟨_, mT, r, hr, h.trans h₁, hl, hu, hc⟩

/-- A big-step run to a specification trap in focus, at the store it reaches. -/
theorem TrapsQS.trapsAtS {α : Type} {th : Option ThreadId} {p : Canon.P (E3 P) σ α}
    {f : α → Canon.P (E3 P) σ (Ret (E3 P))} {M mT : Machine.Config (E3 P) σ}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {tr : List (Label (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog (p >>= f), segs⟩ :: rest) (h : TrapsQS (DI P impl) th p M tr mT)
    (hl : M.store.lockdown = false) {c : (E3 P).Store (CanonHost (E3 P))}
    (hcore : mT.core = c) : TrapsAtS prof P impl M c := by
  have e : M = { M with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } := by
    cases M
    cases hc
    rfl
  obtain ⟨q, segs', r, hr, hrun, hlive, hu⟩ := h.lrun (prof := prof) (hr := fun _ _ => false) hl
    f segs rest
  rw [← e] at hrun
  exact ⟨_, _, r, hr, hrun, hlive, hu, hcore⟩

/-- `lrun_lift_trapAt` with a specification trap. -/
theorem lrun_lift_trapAtS {α : Type} {th : Option ThreadId} (p : Silmaril.Wasm.Component.FuncTy)
    (hres : p.results.length ≤ 1) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    (hff : floatFreeList p.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList p.results) (hnone : liftArgs p.results ys = none)
    {cx : LiftLowerContext (E3 P)}
    {f : List Silmaril.Wasm.Component.Reference.Val × FlatCursor → Canon.P (E3 P) σ α}
    {g : α → Canon.P (E3 P) σ (Ret (E3 P))} {M : Machine.Config (E3 P) σ}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (witFt p)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) : TrapsAtS prof P impl M M.core := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (witFt p)) =
        (ptrType cx >>= fun q => liftFlatTypes Limits.spec Quirks.none cx q
        (toClosedList p.results) ⟨ys, 0⟩ : Canon.P (E3 P) σ _) := by
    rw [resultTypes_witFt p hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := Adequacy.liftFlatTypes_liftArgsS (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn (CoreEngine.view _ M.core) cx) hff hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hr, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) σ) .readCore fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList p.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (fun _ _ => false) (DI P impl) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn (CoreEngine.view _ M.core) cx) (toClosedList p.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.readCore hc'
  rw [hk] at s₁
  exact ⟨_, _, r, hr, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl), rfl⟩

/-! ## Callouts whose arguments do not lift -/

/-- `traps_lowerOnStart` with a specification trap. -/
theorem traps_lowerOnStartS {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext (E3 P)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {xS : Subtask}
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    ∃ tr, TrapsQS (DI P impl) th (lowerOnStart Limits.spec Quirks.none c) m tr
      { m with store := LowerSt.startSt S m.store } := by
  have hT : Adequacy.IsSpecTrap (liftFlatTypes (σ := σ) Limits.spec Quirks.none cx
      (ptrTypeIn (CoreEngine.view _ m.core) cx) (toClosedList p.params) ⟨ys, 0⟩) := by
    have h := Adequacy.liftFlatTypes_liftArgsS (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
      (ptrTypeIn (CoreEngine.view _ m.core) cx) hff hys
    rwa [hws] at h
  have hmp : RunsQ (DI P impl) th (maybeOnProgress S) m [.tau] () m :=
    RunsQ.getObj_bind _ _ hS (by rw [hidx]; exact RunsQ.pure _ _)
  have hlift : TrapsQS (DI P impl) th (liftFlatValues Limits.spec Quirks.none cx 16 ⟨ys, 0⟩
      ((witFt p).params.map (·.2))) { m with store := LowerSt.startSt S m.store } [.tau]
      { m with store := LowerSt.startSt S m.store } := by
    rw [liftFlatValues_witFt hmax]
    exact TrapsQS.bind (RunsQ.readCore (RunsQ.pure _ _)) (TrapsQS.trap _ hT)
  exact ⟨_, TrapsQS.bind (RunsQ.getObj _ _ hc) (TrapsQS.bind hmp
    (TrapsQS.bind (RunsQ.modify rfl (RunsQ.pure _ _)) (TrapsQS.left hlift)))⟩

/-- `traps_startLT` with a specification trap. -/
theorem traps_startLTS {th : Option ThreadId} {m : Machine.Config (E3 P) σ}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)} {c : CallerId} {S : SubtaskId}
    {cx : LiftLowerContext (E3 P)} {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
    {xS : Subtask}
    (ht : m.store.tasks = Gt ++ [y]) (hy : y.caller = c)
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    ∃ tr mT, TrapsQS (DI P impl) th (Task.start ⟨Gt.length⟩) m tr mT ∧
      mT.core = m.core := by
  obtain ⟨tr, h⟩ := traps_lowerOnStartS (impl := impl) (th := th)
    (m := { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store }) (by exact hc)
    (by exact hS) hidx hff hys hmax hws
  have hon : TrapsQS (DI P impl) th (DI P impl (.onStart c))
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } (.tau :: tr)
      { m with store := LowerSt.startSt S (CStore.setTaskState ⟨Gt.length⟩ .started m.store) } :=
    TrapsQS.bind (RunsQ.getObj _ _ (by exact hc)) (TrapsQS.left h)
  have hs : TrapsQS (DI P impl) th (callVals (.onStart y.caller) :
      Canon.P (E3 P) σ (List Silmaril.Wasm.Component.Reference.Val))
      { m with store := CStore.setTaskState ⟨Gt.length⟩ .started m.store } (.tau :: .tau :: tr)
      { m with store := LowerSt.startSt S (CStore.setTaskState ⟨Gt.length⟩ .started m.store) } := by
    rw [hy]
    exact TrapsQS.callIn hon
  unfold Task.start
  exact ⟨_, _, TrapsQS.bind (runs_getObj ArenaField.tasks _ _ (tasks_get_last ht))
    (TrapsQS.bind (runs_modifyStore _ _ rfl) hs), rfl⟩

/-- `lift_body_trapT` with a specification trap. -/
theorem lift_body_trapTS (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) {ιe ιe' : InstState}
    (a : (E3 P).FuncAddr) (R : List (Activation (E3 P) σ))
    (hie : S.insts[1]? = some ιe) (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe'))
    (hl : S.lockdown = false)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapsAtS prof P impl
      { M₀ with
        store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
          (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R }
      M₀.core := by
  obtain ⟨trS, mT, hst, hcore⟩ := traps_startLTS (impl := impl) (th := some ⟨S.threads.length⟩)
    (m := { M₀ with
      store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₁ S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe') })
    (Gt := S.tasks) rfl rfl (callers_get_last rfl) (subtasks_get_last rfl) rfl hpf hys hmaxp hws
  have h₁ := RunsQ.lrun_at (prof := prof) (hr := fun _ _ => false)
    (runs_enterG (impl := impl) (Gt := S.tasks) (t := ⟨S.threads.length⟩)
      (m := { M₀ with
        store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
          (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R })
      rfl rfl (by exact hie) hadd) (by exact hl) _ rfl
  refine TrapsAtS.lrun h₁ ?_
  rw [nstore_enter S _ _ p hie hadd]
  refine TrapsAtS.lrun (RunsQ.lrun_at (runs_getObj ArenaField.tasks _ _ (tasks_get_last rfl))
    (by exact hl) _ rfl) ?_
  exact TrapsQS.trapsAtS rfl (hst.withCtl _) (by exact hl) hcore

/-- `nest_trap_argsT` with a specification trap: a callout of the importer whose arguments
do not lift traps at the core store of the callout. -/
theorem nest_trap_argsTS (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
    (C : List (Option (Activation (E3 P) σ))) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hentry : calloutEntry (extN B ιe N C).store th (.lowered f (witFt p) {} ⟨2⟩) = none)
    (hi : ArenaField.insts.get? (extN B ιe N C).store ⟨2⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hlen : 1 < B.store.insts.length)
    (hadd : ιe.addThread? ⟨(extN B ιe N C).store.threads.length⟩ = some (1, ιe'))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    TrapsAtS prof P impl (coreCfg (extN B ιe N C) th K segs rest x) x.1 := by
  obtain ⟨C₁, R, tr₁, h₁, -⟩ := nest_pre (prof := prof) (impl := impl) B ιe ιe' N C th K segs
    rest x f a p ys ιi hs hentry hi hleave hf
  have hie : ((extN B ιe N C).store : CStore (E3 P)).insts[1]? = some ιe :=
    List.getElem?_set_self hlen
  exact TrapsAtS.lrun h₁ (lift_body_trapTS (prof := prof) (impl := impl)
    { coreCfg (extN B ιe N C) th K segs rest x with conts := C₁ }
    (extN B ιe N C).store ys p a R hie hadd rfl hpf hys hmaxp hws)

/-- `lift_body_atT` (same proof), the trap of a failing lift a specification trap. -/
theorem lift_body_atTS (M₀ : Machine.Config (E3 P) σ) (S : CStore (E3 P)) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (ws : List Silmaril.Wasm.Component.Val) {ιe ιe' : InstState}
    (a : (E3 P).FuncAddr) (R : List (Activation (E3 P) σ))
    (hie : S.insts[1]? = some ιe) (hadd : ιe.addThread? ⟨S.threads.length⟩ = some (1, ιe'))
    (hrem : ιe'.removeThread? 1 = some (⟨S.threads.length⟩, InstState.removeThread 1 ιe'))
    (hl : S.lockdown = false)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ pos K' segs' tr, LRun prof (fun _ _ => false) (DI P impl)
      { M₀ with
        store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₀ S p)
          (thread₁ S.tasks) S.insts
        ctl := ⟨some ⟨S.threads.length⟩,
          .prog (DI P impl (.threadBody (.liftImplicit ⟨S.tasks.length⟩ a))), []⟩ :: R } tr
      { M₀ with
        store := nstoreCore S ys p ιe' pos
        ctl := ⟨some ⟨S.threads.length⟩,
          .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) K',
          segs'⟩ :: R } ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl)
          (retCfg { M₀ with store := nstoreCore S ys p ιe' pos } (some ⟨S.threads.length⟩) K'
            segs' R y zs) tr'
          { M₀ with store := nstoreRet S y.1 ys p ιe' pos us, core := y.1, ctl := R }) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsAtS prof P impl
          (retCfg { M₀ with store := nstoreCore S ys p ιe' pos } (some ⟨S.threads.length⟩) K'
            segs' R y zs) y.1) := by
  obtain ⟨pos, trS, hst⟩ := runs_startL (impl := impl) (th := some ⟨S.threads.length⟩)
    (m := { M₀ with
      store := nstore S { inst := ⟨2⟩ } (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p 0) (ntask₁ S p)
        ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe') })
    (Gt := S.tasks) rfl rfl (callers_get_last rfl) (subtasks_get_last rfl) rfl hpf hys hmaxp hws
  have hlen : 1 < S.insts.length := (List.getElem?_eq_some_iff.mp hie).1
  have hie' : (S.insts.set 1 ιe')[1]? = some ιe' := List.getElem?_set_self hlen
  refine ⟨pos, ?_⟩
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · apply RunsQ.chunk rfl (runs_enterG (impl := impl) (Gt := S.tasks) rfl rfl (by exact hie) hadd)
      (by exact hl)
    apply LRun.store_congr (nstore_enter S _ _ p hie hadd)
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last rfl)) (by exact hl)
    apply RunsQ.chunk rfl (hst.withCtl _) (by exact hl)
    apply RunsQ.chunk rfl (runs_lowerP p ws _ hpf (Silmaril.Wasm.Component.checkList_of_liftArgs hws)
      hmaxp _) (by exact hl)
    lstep hl
    exact .refl _
  · intro y zs us hzs hus
    apply Exists.intro
    unfold retCfg
    apply LRun.store_congr (S' := nstore S { inst := ⟨2⟩, state := .started }
      (lowerRec ⟨S.subtasks.length⟩ ⟨2⟩ ys p pos) ((ntask₁ S p).withState .started)
      ((thread₁ S.tasks).withIndex 1) (S.insts.set 1 ιe')) (by rw [nstoreCore_eq])
    apply RunsQ.chunk2 rfl (runs_lift_someP (impl := impl) p hres hmaxr hrf hzs hus _ _).choose_spec
      (by exact hl)
    apply RunsQ.chunk2 rfl (by exact (runs_returnL (impl := impl) (Gt := S.tasks) rfl rfl rfl rfl
        (callers_get_last rfl) (subtasks_get_last rfl) rfl hres hrf
        (Silmaril.Wasm.Component.checkList_of_liftArgs hus) hmaxr).choose_spec) (by exact hl)
    apply LRun.store_congr (nstore_return S y.1 ys p ιe' pos _)
    apply RunsQ.chunk rfl (runs_exitG (impl := impl) (Gt := S.tasks) (Gth := S.threads) rfl rfl rfl
      rfl rfl rfl (by exact hie') hrem) (by exact hl)
    lstep ((CStore.unregisterThreadSt_frame (E := E3 P) _ _ _ _).2.2.2.2.2.2.1.trans hl)
    exact lrun_refl_store (nstore_exit S y.1 _ _ p ιe')
  · intro y zs hzs hn
    exact lrun_lift_trapAtS p hres hmaxr hrf hzs hn rfl (by exact hl)

/-- `nest_atT` (same proof), the trap of a failing lift of the exporter's results a
specification trap at the core store the exporter returned with. -/
theorem nest_atTS (B : Machine.Config (E3 P) σ) (ιe ιe' : InstState) (N : List (NRec P))
    (C : List (Option (Activation (E3 P) σ))) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P)) (f : FuncId) (a : (E3 P).FuncAddr)
    (p : Silmaril.Wasm.Component.FuncTy) (ys : List Flat) (ιi : InstState)
    (ws : List Silmaril.Wasm.Component.Val)
    (hs : (E3 P).status x.1 x.2 = .callout (.lowered f (witFt p) {} ⟨2⟩) ys)
    (hentry : calloutEntry (extN B ιe N C).store th (.lowered f (witFt p) {} ⟨2⟩) = none)
    (hi : ArenaField.insts.get? (extN B ιe N C).store ⟨2⟩ = some ιi) (hleave : ιi.mayLeave = true)
    (hf : ArenaField.funcs.get? B.store f = some (.lifted a (witFt p) {} ⟨1⟩))
    (hlen : 1 < B.store.insts.length)
    (hadd : ιe.addThread? ⟨(extN B ιe N C).store.threads.length⟩ = some (1, ιe'))
    (hrem : ιe'.removeThread? 1 =
      some (⟨(extN B ιe N C).store.threads.length⟩, InstState.removeThread 1 ιe'))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ (pos : Nat) (C₁ : List (Option (Activation (E3 P) σ))) (M₁ : Machine.Config (E3 P) σ)
      (th' : Option ThreadId) (K' : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
      (segs' : List (Seg (E3 P) σ)) (rest' : List (Activation (E3 P) σ)) (tr : List (Label (E3 P) σ)),
      LRun prof (fun _ _ => false) (DI P impl) (coreCfg (extN B ιe N C) th K segs rest x) tr M₁ ∧
      M₁.ctl = ⟨th', .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws))
        K', segs'⟩ :: rest' ∧
      M₁.core = x.1 ∧ M₁.store.lockdown = false ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat) (us : List Silmaril.Wasm.Component.Val),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = some us →
        ∃ tr', LRun prof (fun _ _ => false) (DI P impl) (retCfg M₁ th' K' segs' rest' y zs) tr'
          (coreCfg (extN B (InstState.removeThread 1 ιe')
            (N ++ [nrec (extN B ιe N C).store ys p pos (lowerArgs p.results us)])
            C₁) th K segs rest (y.1, (E3 P).resume y.1 x.2 (.values (lowerArgs p.results us))))) ∧
      (∀ (y : CoreSt (E3 P)) (zs : List Flat),
        zs.map (·.type) = ValTy.flatList p.results → liftArgs p.results zs = none →
        TrapsAtS prof P impl (retCfg M₁ th' K' segs' rest' y zs) y.1) := by
  obtain ⟨C₁, R, tr₁, h₁, hback⟩ := nest_pre (prof := prof) (impl := impl) B ιe ιe' N C th K segs
    rest x f a p ys ιi hs hentry hi hleave hf
  have hie : ((extN B ιe N C).store : CStore (E3 P)).insts[1]? = some ιe :=
    List.getElem?_set_self hlen
  obtain ⟨pos, K', segs', tr₂, h₂, hret, htrap⟩ := lift_body_atTS (prof := prof) (impl := impl)
    { coreCfg (extN B ιe N C) th K segs rest x with conts := C₁ }
    (extN B ιe N C).store ys p ws a R hie hadd hrem rfl hpf hys hmaxp hws
    hres hrf hmaxr
  refine ⟨pos, C₁, _, _, K', segs', _, _, h₁.trans h₂, rfl, rfl, rfl, ?_, htrap⟩
  intro y zs us hzs hus
  obtain ⟨tr₃, h₃⟩ := hret y zs us hzs hus
  obtain ⟨tr₄, h₄⟩ := hback y.1 pos us
  exact ⟨_, h₃.trans h₄⟩

/-- `CallAtLKT`, the trap of a failing lift of the importer's results a specification
trap. -/
structure CallAtLKTS (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi' : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h₀ : σ) (k j : Nat)
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop where
  start : M₀ = coreCfg (extN M₀ ιe [] M₀.conts) th K segs rest
    (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs x.ty.params vs))
  funcs : M₀.store.funcs = fs
  frame : LFrame M₀ th
  ret : ∀ (ιe' : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ∃ C', ResolvesAtL prof P impl (retCfg (extN M₀ ιe' N C) th K segs rest y ys)
      (readyCfgL y.1 ιe' (InstState.removeThread 1 ιi') fs
        (nextGarbL G x k j (vs.map toRefVal) (ws.map toRefVal) N C') (ST ++ N.map (·.sub)) h₀)
  trap : ∀ (ιe' : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsAtS prof P impl (retCfg (extN M₀ ιe' N C) th K segs rest y ys) y.1

/-- `call_atLK` (same proof), with `CallAtLKTS`. -/
theorem call_atLKTS (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ιe ιi : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask)
    (h₀ : σ) (k j a : Nat) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true) (hth : ThreadsOk ιi) (hleave : ιi.mayLeave = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨2⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (fun _ _ => false) (DI P impl)
      (invokedAtL cs ιe ιi fs G ST h₀ k j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtLKTS prof P impl cs ιe (enterInst ιi ⟨G.threads.length⟩) fs G ST h₀ k j x a vs M₀ th
        K segs rest := by
  have hadd : ιi.addThread? ⟨G.threads.length⟩ = some (1, enterInst ιi ⟨G.threads.length⟩) :=
    addThread?_ok hth _
  have hrem : (enterInst ιi ⟨G.threads.length⟩).removeThread? 1 = some (⟨G.threads.length⟩,
      InstState.removeThread 1 (enterInst ιi ⟨G.threads.length⟩)) :=
    removeThread?_enter ιi _
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (fun _ _ => false) (DI P impl)
      (invokedAtL cs ιe ιi fs G ST h₀ k j (vs.map toRefVal)) _ _
    unfold invokedAtL
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (.host ⟨k⟩ (vs.map toRefVal) 0) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨2⟩) := by
      intro s e
      simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
      exact hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    show LRun prof (fun _ _ => false) (DI P impl) _ _ _
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S : CStore (E3 P), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
        threadStatusSt ⟨G.threads.length⟩ .running S =
          { S with threads := G.threads ++ [thread₁ G.tasks] } :=
      fun S h => threadStatus_last h _
    apply LRun.store_congr (S' := storeK₁ cs ιe ιi fs G ST x k (vs.map toRefVal))
      ((e₁ _ rfl).trans rfl)
    have hS₁ : (storeK₁ cs ιe ιi fs G ST x k (vs.map toRefVal)).insts = [{}, ιe, ιi] := rfl
    apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
      (runs_enter3 (Gt := G.tasks) (y := taskK₀ x G.callers) rfl rfl rfl hS₁ hadd) rfl
    have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
          (storeK₁ cs ιe ιi fs G ST x k (vs.map toRefVal))) =
        storeK₂ cs ιe ιi (enterInst ιi ⟨G.threads.length⟩) fs G ST x k (vs.map toRefVal) :=
      enter_eq3 rfl rfl rfl hadd rfl
    apply LRun.store_congr (by exact e₂)
    have hS₂ : (storeK₂ cs ιe ιi (enterInst ιi ⟨G.threads.length⟩) fs G ST x k
        (vs.map toRefVal)).tasks = G.tasks ++ [taskK₁ x G.callers ⟨G.threads.length⟩] := rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last hS₂)) rfl
    apply RunsQ.chunk rfl (runs_start (Gt := G.tasks) (Gc := G.callers) hS₂ rfl rfl) rfl
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ),
        RunsQ (DI P impl) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatParams (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau]
          (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lowerP x.ty vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    apply LRun.store_congr
      (S' := storeK₃ cs ιe ιi (enterInst ιi ⟨G.threads.length⟩) fs G ST x k (vs.map toRefVal))
      (setTaskState_last (Gt := G.tasks) rfl _)
    mstep
    exact .refl _
  apply CallAtLKTS.mk
  · exact start_of rfl rfl rfl rfl
  · rfl
  · refine ⟨fun f ft ιe' N C => ?_, ⟨_, rfl, hleave⟩⟩
    exact calloutEntry_mid (Gt := G.tasks) (Gth := G.threads) rfl rfl rfl rfl f ft {}
  · show ∀ (ιe' : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
      (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
      ∃ C', ResolvesAtL prof P impl (retCfg (extN _ ιe' N C) _ _ _ _ y ys) _
    intro ιe' N C y ys ws hys hws
    have hlift : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ), ∃ c,
        RunsQ (DI P impl) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatResults (.ofList ys) (resultTypes (witFt x.ty))) m [.tau]
          (ws.map toRefVal, c) m :=
      runs_lift_someP x.ty hres hmaxr hffr hys hws
    apply Exists.intro; apply Exists.intro; apply Exists.intro
    apply And.intro
    · show LRun prof (fun _ _ => false) (DI P impl) (retCfg _ _ _ _ _ y ys) _ _
      unfold retCfg
      apply RunsQ.chunk2 rfl (hlift _ _).choose_spec rfl
      apply RunsQ.chunk2 rfl (runs_returnM (Gt := G.tasks) (R := N.map (·.task))
        (Gc := G.callers) (CL := N.map (·.caller)) _ rfl rfl rfl rfl rfl) rfl
      apply LRun.store_congr (setTaskState_mid (Gt := G.tasks) rfl _)
      apply RunsQ.chunk rfl (runs_exitM (Gt := G.tasks) (R := N.map (·.task))
        (Gth := G.threads) (R' := N.map (·.thread)) rfl rfl rfl rfl rfl rfl rfl hrem) rfl
      apply LRun.store_congr (unregisterThreadSt_mid _ _ rfl rfl rfl)
      show LRun prof (fun _ _ => false) (DI P impl) _ _ _
      mstep
      apply LRun.store_congr (threadStatus_mid (Gth := G.threads) rfl _)
      apply RunsQ.chunk rfl (runs_callUnit_loopM (Gt := G.tasks) (R := N.map (·.task)) rfl rfl)
        rfl
      mstep
      mstep
      mstep
      exact .refl _
    · rw [hostFinish_cancel _ G.pending ⟨k⟩ ⟨j⟩ (vs.map toRefVal) _ rfl]
      rfl
  · intro ιe' N C y ys hys hn
    exact lrun_lift_trapAtS x.ty hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd

module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiBase

/-!
# A `canon lower` callout answered by `answerImplS`

A core activation of the reference machine stopped at `.callout h args`, with `h` the
`canon lower` trampoline `.lowered f ft {} inst` of a host function `f` of the stateful host
`answerHostS P g` (host state of any type `σ`), runs the dispatched program `hostCalloutProg`:
the entry check, `canonLower` (a fresh subtask and `canon_lower` caller record), the host
function `answerImplS g` (`on_start`: `lowerOnStart` lifts the flat arguments; `g` answers in the
current host state and the next state is written; `on_resolve`: `lowerOnResolve` lowers the
answer and resolves the subtask), then the delivery of the resolution and the flat results.

* `runs_callout`: when the arguments lift to `ws` and `g` answers `us.map toRefVal` with
  well-typed `us` in the host state, moving to `s'`, the program runs deterministically to
  `.flat (lowerArgs results us)`, the host state becomes `s'`, and the store changes only by one
  more subtask and one more caller record (`ExtSC`);
* `traps_callout_lift`, `traps_callout_host`: when the lift fails, or `g` has no answer, the
  program traps (`TrapsQ`).

`TrapsQ` is the big-step form of a program that reaches a trap; `TrapsQ.lrun` places it in any
context as a live run to a configuration whose only step is the trap.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

/-! ## Generic big-step tools -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

namespace RunsQ

theorem getObj_bind {α β Id : Type} {th : Option ThreadId} (F : ArenaField E Id α) (i : Id)
    {k : α → P E σ β} {m m' : Config E σ} {x : α} {tr : List (Label E σ)} {b : β}
    (h : F.get? m.store i = some x) (hk : RunsQ dispatch th (k x) m tr b m') :
    RunsQ dispatch th (getObj F i >>= k) m (.tau :: tr) b m' := by
  refine .get ?_
  show RunsQ dispatch th ((match F.get? m.store i with
    | some x => Pure.pure x | none => internal "dangling arena id") >>= k) m tr b m'
  rw [h]
  exact hk

theorem getStore_bind {β : Type} {th : Option ThreadId} {k : CStore E → P E σ β}
    {m m' : Config E σ} {tr : List (Label E σ)} {b : β}
    (hk : RunsQ dispatch th (k m.store) m tr b m') :
    RunsQ dispatch th (Canon.getStore >>= k) m (.tau :: tr) b m' :=
  .get hk

theorem currentThread_bind {β : Type} {th : Option ThreadId} {k : Option ThreadId → P E σ β}
    {m m' : Config E σ} {tr : List (Label E σ)} {b : β}
    (hk : RunsQ dispatch th (k th) m tr b m') :
    RunsQ dispatch th (Canon.currentThread >>= k) m (.tau :: tr) b m' :=
  .currentThread hk

theorem modify_bind {β : Type} {th : Option ThreadId} (f : CStore E → CStore E)
    {k : Unit → P E σ β} {m m' : Config E σ} {s : CStore E} {tr : List (Label E σ)} {b : β}
    (hs : f m.store = s) (hl : s.lockdown = m.store.lockdown)
    (hk : RunsQ dispatch th (k ()) { m with store := s } tr b m') :
    RunsQ dispatch th (Canon.modifyStore f >>= k) m (.tau :: tr) b m' := by
  subst hs
  exact .modify hl hk

theorem getObj {α Id : Type} {th : Option ThreadId} (F : ArenaField E Id α) (i : Id)
    {m : Config E σ} {x : α} (h : F.get? m.store i = some x) :
    RunsQ dispatch th (Canon.getObj F i) m [.tau] x m := by
  refine .get ?_
  show RunsQ dispatch th (match F.get? m.store i with
    | some x => Pure.pure x | none => internal "dangling arena id") m [] x m
  rw [h]
  exact .pure _ _

theorem call_bind {β : Type} {th : Option ThreadId} {c : Call E} {k : Ret E → P E σ β}
    {m m₁ m' : Config E σ} {tr₁ tr₂ : List (Label E σ)} {r : Ret E} {b : β}
    (h₁ : RunsQ dispatch th (dispatch c) m tr₁ r m₁) (h₂ : RunsQ dispatch th (k r) m₁ tr₂ b m') :
    RunsQ dispatch th (callRet c >>= k) m (.tau :: (tr₁ ++ .tau :: tr₂)) b m' :=
  .call h₁ h₂

end RunsQ

variable (dispatch) in
/-- **Big-step runs to a trap**: the program `p` on thread `th` runs from `m` to a
configuration whose program in focus traps, possibly inside late-bound calls. -/
inductive TrapsQ : {α : Type} → Option ThreadId → P E σ α → Config E σ → List (Label E σ) →
    Config E σ → Prop where
  | trap {α : Type} {th : Option ThreadId} {p : P E σ α} (m : Config E σ) :
      IsTrap p → TrapsQ th p m [] m
  | bind {α β : Type} {th : Option ThreadId} {p : P E σ α} {f : α → P E σ β}
      {m m₁ mT : Config E σ} {tr₁ tr₂ : List (Label E σ)} {a : α} :
      RunsQ dispatch th p m tr₁ a m₁ → TrapsQ th (f a) m₁ tr₂ mT →
      TrapsQ th (p >>= f) m (tr₁ ++ tr₂) mT
  | left {α β : Type} {th : Option ThreadId} {p : P E σ α} {f : α → P E σ β}
      {m mT : Config E σ} {tr : List (Label E σ)} :
      TrapsQ th p m tr mT → TrapsQ th (p >>= f) m tr mT
  | callIn {α : Type} {th : Option ThreadId} {c : Call E} {k : Ret E → P E σ α}
      {m mT : Config E σ} {tr : List (Label E σ)} :
      TrapsQ th (dispatch c) m tr mT → TrapsQ th (callRet c >>= k) m (.tau :: tr) mT

namespace TrapsQ

theorem lock {α : Type} {th : Option ThreadId} {p : P E σ α} {m mT : Config E σ}
    {tr : List (Label E σ)} (h : TrapsQ dispatch th p m tr mT) :
    mT.store.lockdown = m.store.lockdown := by
  induction h with
  | trap => rfl
  | bind h₁ _ ih => exact ih.trans h₁.lock
  | left _ ih => exact ih
  | callIn _ ih => exact ih

/-- **A big-step run to a trap is a live run to a configuration whose only step is the
trap**, in any context. -/
theorem lrun {α : Type} {th : Option ThreadId} {p : P E σ α} {m mT : Config E σ}
    {tr : List (Label E σ)} (h : TrapsQ dispatch th p m tr mT) :
    m.store.lockdown = false →
    ∀ (f : α → P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
      ∃ (q : P E σ (Ret E)) (segs' : List (Seg E σ)) (r : TrapReason),
        LRun prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
          { mT with ctl := ⟨th, .prog q, segs'⟩ :: rest } ∧
        Live ({ mT with ctl := ⟨th, .prog q, segs'⟩ :: rest } : Config E σ) ∧
        UniqueStep prof hr dispatch { mT with ctl := ⟨th, .prog q, segs'⟩ :: rest } (.trap r)
          (trapCfg { mT with ctl := ⟨th, .prog q, segs'⟩ :: rest }) := by
  induction h with
  | @trap _ th p m hp =>
    intro hl f segs rest
    obtain ⟨r, k, rfl⟩ := hp
    exact ⟨_, segs, r, .refl _, RunsQ.live_op hl,
      .of_prog rfl (fun _ _ e => by cases e) (.trap (k := fun e => k e >>= f) rfl)⟩
  | @bind _ _ th p f₀ m m₁ mT tr₁ tr₂ a h₁ _ ih =>
    intro hl f segs rest
    have hl₁ : m₁.store.lockdown = false := h₁.lock.trans hl
    obtain ⟨q, segs', r, hrun, hlive, hu⟩ := ih hl₁ f segs rest
    have d₁ := h₁.lrun (prof := prof) (hr := hr) hl (fun a => f₀ a >>= f) segs rest
    have e : (p >>= f₀) >>= f = p >>= fun a => f₀ a >>= f := by
      rw [Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
      rfl
    rw [e]
    exact ⟨q, segs', r, d₁.trans hrun, hlive, hu⟩
  | @left _ _ th p f₀ m mT tr _ ih =>
    intro hl f segs rest
    have e : (p >>= f₀) >>= f = p >>= fun a => f₀ a >>= f := by
      rw [Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
      rfl
    rw [e]
    exact ih hl (fun a => f₀ a >>= f) segs rest
  | @callIn _ th c k m mT tr _ ih =>
    intro hl f segs rest
    obtain ⟨q, segs', r, hrun, hlive, hu⟩ := ih hl Prog.pure (.prog (fun r => k r >>= f) :: segs)
      rest
    have s₁ : UniqueStep prof hr dispatch
        { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.call c) fun r => k r >>= f), segs⟩ ::
          rest }
        .tau { m with ctl := ⟨th, .prog (dispatch c), .prog (fun r => k r >>= f) :: segs⟩ ::
          rest } :=
      .of_prog rfl (fun _ _ e => by cases e) (.call (k := fun r => k r >>= f) rfl)
    rw [Prog.bind_eq, Prog.bind_pure] at hrun
    exact ⟨q, segs', r, .cons (RunsQ.live_op hl) s₁ hrun, hlive, hu⟩

end TrapsQ

end Generic

/-! ## The callout program -/

section Callout

variable {P : Profile} {σ : Type} {d : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))}
  {g : σ → HostFuncId → List Val → Option (List Val × σ)}

@[simp] theorem callers_get?_subtasks_modify {E : CoreEngine} (s : CStore E) (i : SubtaskId)
    (f : Subtask → Subtask) (c : CallerId) :
    ArenaField.callers.get? (ArenaField.subtasks.modify s i f) c = ArenaField.callers.get? s c := rfl

@[simp] theorem subtasks_get?_callers_modify {E : CoreEngine} (s : CStore E) (c : CallerId)
    (f : Caller E → Caller E) (i : SubtaskId) :
    ArenaField.subtasks.get? (ArenaField.callers.modify s c f) i = ArenaField.subtasks.get? s i := rfl

theorem params_witFt (p : Silmaril.Wasm.Component.FuncTy) :
    (witFt p).params.map (·.2) = toClosedList p.params := labels_map_snd _ _

theorem result_witFt (p : Silmaril.Wasm.Component.FuncTy) (h : p.results.length ≤ 1) :
    (witFt p).result.toList = toClosedList p.results := by
  rcases hr : p.results with _ | ⟨t, _ | ⟨u, us⟩⟩
  · simp only [witFt, hr, toClosedList]; rfl
  · simp only [witFt, hr, toClosedList]; rfl
  · rw [hr] at h; simp at h

theorem runsQ_allocObj {α Id : Type} {th : Option ThreadId} (F : ArenaField (E3 P) Id α) (x : α)
    {m : Machine.Config (E3 P) σ}
    (hl : (ArenaOps.allocSt F x m.store).lockdown = m.store.lockdown) :
    RunsQ d th (allocObj F x) m [.tau, .tau] (F.mkId (F.size m.store))
      { m with store := ArenaOps.allocSt F x m.store } :=
  .get (.modify hl (.pure _ _))

/-- The flat arguments of a callout lifted at the parameter types: `liftFlatValues` is the
IR lift, or traps. -/
theorem liftFlatValues_witFt {cx : LiftLowerContext (E3 P)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} (hmax : (ValTy.flatList p.params).length ≤ 16) :
    liftFlatValues Limits.spec Quirks.none cx 16 ⟨ys, 0⟩ ((witFt p).params.map (·.2)) =
      (ptrType cx >>= fun p' => liftFlatTypes Limits.spec Quirks.none cx p'
        (toClosedList p.params) ⟨ys, 0⟩ : Canon.P (E3 P) σ _) := by
  rw [params_witFt]
  exact liftFlatValues_toClosed (max := 16) Limits.spec Quirks.none cx hmax

/-- `on_start` of a `canon_lower` caller record lifts the flat arguments. -/
theorem runs_lowerOnStart {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext (E3 P)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {xS : Subtask} {ws : List Silmaril.Wasm.Component.Val}
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws) :
    ∃ pos tr, RunsQ d th (lowerOnStart Limits.spec Quirks.none c) m tr (ws.map toRefVal)
      { m with store := LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store) } := by
  have hl : ∃ cur, liftFlatTypes (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) (toClosedList p.params) ⟨ys, 0⟩ =
        pure (ws.map toRefVal, cur) := by
    have h := liftFlatTypes_liftArgs (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) hff hys
    rwa [hws] at h
  obtain ⟨cur, hcur⟩ := hl
  have hmp : RunsQ d th (maybeOnProgress S) m [.tau] () m :=
    RunsQ.getObj_bind _ _ hS (by rw [hidx]; exact RunsQ.pure _ _)
  have hlf : RunsQ d th (liftFlatTypes Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) (toClosedList p.params) ⟨ys, 0⟩)
      { m with store := LowerSt.startSt S m.store } [] (ws.map toRefVal, cur)
      { m with store := LowerSt.startSt S m.store } := by
    rw [hcur]
    exact RunsQ.pure _ _
  refine ⟨cur.pos, ?_⟩
  apply Exists.intro
  apply RunsQ.getObj_bind _ _ hc
  apply RunsQ.bind hmp
  apply RunsQ.modify_bind _ rfl rfl
  show RunsQ _ _ (liftFlatValues Limits.spec Quirks.none cx 16 ⟨ys, 0⟩
    ((witFt p).params.map (·.2)) >>= _) _ _ _ _
  rw [liftFlatValues_witFt hmax]
  apply RunsQ.bind (RunsQ.bind (RunsQ.get (RunsQ.pure _ _)) hlf)
  exact RunsQ.modify_bind _ rfl rfl (RunsQ.pure _ _)

/-- `on_resolve` of a `canon_lower` caller record lowers the results and resolves the
subtask. -/
theorem runs_lowerOnResolve {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext (E3 P)} {ys : List Flat} {pos : Nat}
    {p : Silmaril.Wasm.Component.FuncTy} {xS : Subtask} {us : List Silmaril.Wasm.Component.Val}
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys pos (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hres : p.results.length ≤ 1) (hff : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmax : (ValTy.flatList p.results).length ≤ 1) :
    ∃ tr, RunsQ d th (lowerOnResolve Limits.spec Quirks.none c (some (us.map toRefVal))) m tr ()
      { m with store := CStore.subtaskResolveSt S .returned (lowerArgs p.results us) m.store } := by
  have hmp : RunsQ d th (maybeOnProgress S) m [.tau] () m :=
    RunsQ.getObj_bind _ _ hS (by rw [hidx]; exact RunsQ.pure _ _)
  have e : lowerFlatValues Limits.spec Quirks.none cx 1 (us.map toRefVal) (witFt p).result.toList
      (some ⟨ys, pos⟩) =
      (ptrType cx >>= fun _ => pure (lowerArgs p.results us) : Canon.P (E3 P) σ _) := by
    rw [result_witFt p hres]
    exact lowerFlatValues_toClosed Limits.spec Quirks.none cx hff hus hmax _
  apply Exists.intro
  apply RunsQ.getObj_bind _ _ hc
  apply RunsQ.bind hmp
  show RunsQ _ _ (lowerFlatValues Limits.spec Quirks.none cx 1 (us.map toRefVal)
    (witFt p).result.toList (some ⟨ys, pos⟩) >>= _) _ _ _ _
  rw [e]
  apply RunsQ.bind (RunsQ.bind (RunsQ.get (RunsQ.pure _ _)) (RunsQ.pure _ _))
  apply RunsQ.bind (RunsQ.pure _ _)
  exact RunsQ.modify rfl (RunsQ.pure _ _)

/-- The dispatcher of the stateful host answering by `g`. -/
abbrev DA (P : Profile) (g : σ → HostFuncId → List Val → Option (List Val × σ)) :
    Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P)) := (answerHostS P g).dispatch

/-- The `canon_lower` caller record of a callout with flat arguments `ys` to a function of type
`p`, for subtask `S` of instance `inst`. -/
def lowerRec (S : SubtaskId) (inst : InstId) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy)
    (pos : Nat) : Caller (E3 P) :=
  .lower S { opts := {}, inst := inst, scope := .subtask S } ys pos (witFt p) 16 1

/-- The subtask of a callout of instance `inst` resolved with `flat`, before delivery. -/
def resolvedSub (inst : InstId) (flat : List Flat) : Subtask :=
  { inst := inst, state := .returned, flatResults := flat, onCancel := CancelRef.none }

/-- The store after `canonLower` allocated the subtask and the caller record of a callout. -/
def allocSC (s : CStore (E3 P)) (inst : InstId) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy) :
    CStore (E3 P) :=
  ArenaOps.allocSt ArenaField.callers (lowerRec (P := P) ⟨s.subtasks.length⟩ inst ys p 0)
    (ArenaOps.allocSt ArenaField.subtasks ({ inst := inst } : Subtask) s)

/-- The store after a callout answered with the flat results `flat`. -/
def calloutSt (s : CStore (E3 P)) (inst : InstId) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy)
    (pos : Nat) (flat : List Flat) : CStore (E3 P) :=
  CStore.deliverResolveSt ⟨s.subtasks.length⟩ (LowerSt.setOnCancelSt ⟨s.subtasks.length⟩ .none
    (CStore.subtaskResolveSt ⟨s.subtasks.length⟩ .returned flat
      (LowerSt.setCallerPosSt ⟨s.callers.length⟩ pos (LowerSt.startSt ⟨s.subtasks.length⟩
        (allocSC s inst ys p)))))

theorem allocSC_callers (s : CStore (E3 P)) (inst : InstId) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) :
    ArenaField.callers.get? (allocSC s inst ys p) ⟨s.callers.length⟩ =
      some (lowerRec ⟨s.subtasks.length⟩ inst ys p 0) := by
  simp [allocSC, ArenaOps.allocSt, ArenaField.get?, ArenaField.alloc, Arena.alloc,
    ArenaField.callers, ArenaField.subtasks, Arena.get?_eq_getElem?]

theorem allocSC_subtasks (s : CStore (E3 P)) (inst : InstId) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) :
    ArenaField.subtasks.get? (allocSC s inst ys p) ⟨s.subtasks.length⟩ =
      some ({ inst := inst } : Subtask) := by
  simp [allocSC, ArenaOps.allocSt, ArenaField.get?, ArenaField.alloc, Arena.alloc,
    ArenaField.callers, ArenaField.subtasks, Arena.get?_eq_getElem?]

/-- `on_start` dispatched to a `canon_lower` caller record. -/
theorem runs_onStartLower {th : Option ThreadId} {m m' : Machine.Config (E3 P) σ} {c : CallerId}
    {x : Caller (E3 P)} {tr : List (Label (E3 P) σ)} {vs : List Val}
    (hc : ArenaField.callers.get? m.store c = some x)
    (hx : ∀ S cx ys pos ft mp mr, x = .lower S cx ys pos ft mp mr →
      RunsQ (DA P g) th (lowerOnStart Limits.spec Quirks.none c) m tr vs m')
    (hl : ∃ S cx ys pos ft mp mr, x = .lower S cx ys pos ft mp mr) :
    RunsQ (DA P g) th (DA P g (.onStart c)) m (.tau :: (tr ++ [])) (.vals vs) m' := by
  obtain ⟨S, cx, ys, pos, ft, mp, mr, rfl⟩ := hl
  exact RunsQ.getObj_bind _ _ hc (RunsQ.bind (hx _ _ _ _ _ _ _ rfl) (RunsQ.pure _ _))

/-- **The host function `fn` of `answerHostS P g`, called through a `canon_lower` caller
record**, lifts the arguments to `ws`, and resolves with `g`'s answer `us` in the current host
state, lowered, moving to the host state `s'`. -/
theorem runs_answer {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext (E3 P)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {xS : Subtask} {ws us : List Silmaril.Wasm.Component.Val}
    {s' : σ}
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hg : g m.host fn (ws.map toRefVal) = some (us.map toRefVal, s'))
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ pos tr, RunsQ (DA P g) th (DA P g (.funcInst f c)) m tr (.cancel .none)
      { m with host := s', store := (CStore.subtaskResolveSt S .returned (lowerArgs p.results us)
        (LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store))) } := by
  obtain ⟨pos, tr₁, h₁⟩ := runs_lowerOnStart (d := DA P g) (th := th) hc hS hidx hpf hys hmaxp hws
  have hc' : ArenaField.callers.get? (LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store)) c =
      some (.lower S cx ys pos (witFt p) 16 1) := by
    simp [LowerSt.setCallerPosSt, LowerSt.startSt, ArenaField.get?_modify, hc,
      LowerSt.Caller.withPos]
  have hS' : ArenaField.subtasks.get? (LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store)) S =
      some { xS with state := .started } := by
    simp [LowerSt.setCallerPosSt, LowerSt.startSt, ArenaField.get?_modify, hS]
  obtain ⟨tr₂, h₂⟩ := runs_lowerOnResolve (d := DA P g) (th := th)
    (m := { m with host := s', store := LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store) })
    hc' hS' hidx hres hrf hus hmaxr
  have h₃ : RunsQ (DA P g) th (DA P g (.onResolve c (some (us.map toRefVal))))
      { m with host := s', store := LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store) }
      (.tau :: (tr₂ ++ [])) .unit
      { m with host := s', store := (CStore.subtaskResolveSt S .returned (lowerArgs p.results us)
        (LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store))) } :=
    RunsQ.getObj_bind _ _ hc' (RunsQ.bind h₂ (RunsQ.pure _ _))
  refine ⟨pos, ?_⟩
  apply Exists.intro
  apply RunsQ.getObj_bind _ _ hf
  apply RunsQ.call_bind (runs_onStartLower hc (fun _ _ _ _ _ _ _ _ => h₁) ⟨_, _, _, _, _, _, _, rfl⟩)
  apply RunsQ.hostGet
  show RunsQ _ _ (match g m.host fn (ws.map toRefVal) with
    | some (rs, s') => _
    | none => trap (TrapReason.hostTrap "answerImpl: no answer")) _ _ _ _
  rw [hg]
  exact RunsQ.hostSet (RunsQ.bind (RunsQ.pure _ _)
    (RunsQ.bind (RunsQ.call_bind h₃ (RunsQ.pure _ _)) (RunsQ.pure _ _)))

/-- The end of a synchronous `canonLower` whose subtask has resolved: the resolution is
delivered and the flat results returned. -/
theorem runs_lowerTail {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {S : SubtaskId}
    {X : Subtask} (hS : ArenaField.subtasks.get? m.store S = some X) (hst : X.state = .returned)
    (hlen : X.lenders = some []) :
    RunsQ d th (do
        let resolved ← gets fun x => x.subtaskResolved S
        (if (!resolved) = true then Thread.waitUntilGuest WaitSite.syncLower (ReadyCond.subtaskResolved S)
          else pure () : Canon.P (E3 P) σ Unit)
        Subtask.deliverResolve S
        let y ← getObj ArenaField.subtasks S
        pure y.flatResults) m [.tau, .tau, .tau] X.flatResults
      { m with store := CStore.deliverResolveSt S m.store } := by
  have hr : m.store.subtaskResolved S = true := by
    simp only [CStore.subtaskResolved, CStore.subtask?, hS, hst]
    rfl
  have hd : CStore.deliverResolveSt S m.store =
      ArenaField.subtasks.modify m.store S fun y => { y with lenders := none } := by
    simp only [CStore.deliverResolveSt, CStore.subtask?, hS, hlen, Option.getD_some, List.foldl_nil]
  have hS' : ArenaField.subtasks.get? (CStore.deliverResolveSt S m.store) S =
      some { X with lenders := none } := by
    rw [hd, ArenaField.get?_modify_self, hS]
    rfl
  apply RunsQ.get
  show RunsQ _ _ ((if (!m.store.subtaskResolved S) = true then
    Thread.waitUntilGuest WaitSite.syncLower (ReadyCond.subtaskResolved S) else pure ()) >>= _) _ _ _ _
  rw [hr]
  apply RunsQ.bind (RunsQ.pure _ _)
  apply RunsQ.modify (by rw [hd]; rfl)
  exact RunsQ.getObj_bind _ _ hS' (RunsQ.pure _ _)

/-- The resolved subtask of a callout. -/
theorem subtasks_resolved (s : CStore (E3 P)) (inst : InstId) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (pos : Nat) (flat : List Flat) :
    ArenaField.subtasks.get? (LowerSt.setOnCancelSt ⟨s.subtasks.length⟩ CancelRef.none
      (CStore.subtaskResolveSt ⟨s.subtasks.length⟩ .returned flat
        (LowerSt.setCallerPosSt ⟨s.callers.length⟩ pos (LowerSt.startSt ⟨s.subtasks.length⟩
          (allocSC s inst ys p))))) ⟨s.subtasks.length⟩ =
      some (resolvedSub inst flat) := by
  simp [LowerSt.setOnCancelSt, CStore.subtaskResolveSt, LowerSt.setCallerPosSt, LowerSt.startSt,
    ArenaField.get?_modify, allocSC_subtasks, resolvedSub]

/-- **`canonLower` of a callout answered by `g`.** -/
theorem runs_canonLower {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {ws us : List Silmaril.Wasm.Component.Val}
    {s' : σ}
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hg : g m.host fn (ws.map toRefVal) = some (us.map toRefVal, s'))
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ pos tr, RunsQ (DA P g) th (canonLower Limits.spec Quirks.none f (witFt p) {} inst ys) m tr
      (lowerArgs p.results us)
      { m with host := s', store := calloutSt m.store inst ys p pos (lowerArgs p.results us) } := by
  obtain ⟨pos, tr₁, h₁⟩ := runs_answer (g := g) (th := th)
    (m := { m with store := allocSC m.store inst ys p }) hf (allocSC_callers _ _ _ _)
    (allocSC_subtasks _ _ _ _) rfl hpf hys hmaxp hws hg hres hrf hus hmaxr
  have ht := runs_lowerTail (d := DA P g) (th := th) (m := { m with host := s', store :=
    (LowerSt.setOnCancelSt ⟨m.store.subtasks.length⟩ CancelRef.none
      (CStore.subtaskResolveSt ⟨m.store.subtasks.length⟩ .returned (lowerArgs p.results us)
        (LowerSt.setCallerPosSt ⟨m.store.callers.length⟩ pos
          (LowerSt.startSt ⟨m.store.subtasks.length⟩ (allocSC m.store inst ys p))))) })
    (subtasks_resolved _ _ _ _ _ _) rfl rfl
  refine ⟨pos, ?_⟩
  apply Exists.intro
  apply RunsQ.getObj_bind _ _ hi
  rw [hleave]
  apply RunsQ.bind (RunsQ.pure _ _)
  apply RunsQ.bind (runsQ_allocObj _ _ rfl)
  apply RunsQ.bind (runsQ_allocObj _ _ rfl)
  apply RunsQ.call_bind h₁
  apply RunsQ.modify rfl
  exact ht

/-- The prefix of the callout program: the entry check passes. -/
theorem runs_hostCallout_of {th : Option ThreadId} {m m' : Machine.Config (E3 P) σ}
    {f : FuncId} {inst : InstId} {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
    {tr : List (Label (E3 P) σ)} {flat : List Flat}
    (hentry : calloutEntry m.store th (.lowered f (witFt p) {} inst) = none)
    (h : RunsQ (DA P g) th (canonLower Limits.spec Quirks.none f (witFt p) {} inst ys) m tr flat m') :
    RunsQ (DA P g) th (DA P g (.hostCallout (.lowered f (witFt p) {} inst) ys)) m
      (.tau :: .tau :: (tr ++ [])) (.flat flat) m' := by
  apply RunsQ.currentThread
  apply RunsQ.get
  show RunsQ _ _ (match calloutEntry m.store th (.lowered f (witFt p) {} inst) with
    | some r => trap r | none => _) _ _ _ _
  rw [hentry]
  exact RunsQ.bind h (RunsQ.pure _ _)

/-- The prefix of the callout program, to a trap. -/
theorem traps_hostCallout_of {th : Option ThreadId} {m mT : Machine.Config (E3 P) σ}
    {f : FuncId} {inst : InstId} {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
    {tr : List (Label (E3 P) σ)}
    (hentry : calloutEntry m.store th (.lowered f (witFt p) {} inst) = none)
    (h : TrapsQ (DA P g) th (canonLower Limits.spec Quirks.none f (witFt p) {} inst ys) m tr mT) :
    TrapsQ (DA P g) th (DA P g (.hostCallout (.lowered f (witFt p) {} inst) ys)) m
      ([.tau] ++ ([.tau] ++ tr)) mT := by
  apply TrapsQ.bind (RunsQ.currentThread (RunsQ.pure _ _))
  apply TrapsQ.bind (RunsQ.get (RunsQ.pure _ _))
  show TrapsQ _ _ (match calloutEntry m.store th (.lowered f (witFt p) {} inst) with
    | some r => trap r | none => _) _ _ _
  rw [hentry]
  exact TrapsQ.left h

/-- The prefix of `canonLower`, to a trap in the host function. -/
theorem traps_canonLower_of {th : Option ThreadId} {m mT : Machine.Config (E3 P) σ}
    {f : FuncId} {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {tr : List (Label (E3 P) σ)}
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (h : TrapsQ (DA P g) th ((answerHostS P g).impl.funcs fn ⟨m.store.callers.length⟩)
      { m with store := allocSC m.store inst ys p } tr mT) :
    ∃ tr', TrapsQ (DA P g) th (canonLower Limits.spec Quirks.none f (witFt p) {} inst ys) m tr'
      mT := by
  have hf₂ : ArenaField.funcs.get? (allocSC m.store inst ys p) f = some (.host ft' fn) := hf
  apply Exists.intro
  apply TrapsQ.bind (RunsQ.getObj _ _ hi)
  rw [hleave]
  apply TrapsQ.bind (RunsQ.pure _ _)
  apply TrapsQ.bind (runsQ_allocObj _ _ rfl)
  apply TrapsQ.bind (runsQ_allocObj _ _ rfl)
  apply TrapsQ.left
  apply TrapsQ.callIn
  exact TrapsQ.bind (RunsQ.getObj _ _ hf₂) h

/-- **A callout answered by `g`** runs deterministically to its flat results. -/
theorem runs_callout {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {ws us : List Silmaril.Wasm.Component.Val}
    (hentry : calloutEntry m.store th (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    {s' : σ} (hg : g m.host fn (ws.map toRefVal) = some (us.map toRefVal, s'))
    (hres : p.results.length ≤ 1) (hrf : floatFreeList p.results = true)
    (hus : ValTy.checkList p.results us = true) (hmaxr : (ValTy.flatList p.results).length ≤ 1) :
    ∃ pos tr, RunsQ (DA P g) th (DA P g (.hostCallout (.lowered f (witFt p) {} inst) ys)) m tr
      (.flat (lowerArgs p.results us))
      { m with host := s', store := calloutSt m.store inst ys p pos (lowerArgs p.results us) } := by
  obtain ⟨pos, tr, h⟩ := runs_canonLower (g := g) (th := th) hi hleave hf hpf hys hmaxp hws hg hres
    hrf hus hmaxr
  exact ⟨pos, _, runs_hostCallout_of hentry h⟩

/-- **A callout whose arguments do not lift traps.** -/
theorem traps_callout_lift {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy}
    (hentry : calloutEntry m.store th (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = none) :
    ∃ tr mT, TrapsQ (DA P g) th (DA P g (.hostCallout (.lowered f (witFt p) {} inst) ys)) m tr
      mT := by
  let S : SubtaskId := ⟨m.store.subtasks.length⟩
  let cx : LiftLowerContext (E3 P) := { opts := {}, inst := inst, scope := .subtask S }
  let m₂ : Machine.Config (E3 P) σ := { m with store := allocSC m.store inst ys p }
  have hT : IsTrap (liftFlatTypes (σ := σ) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m₂.store) cx) (toClosedList p.params) ⟨ys, 0⟩) := by
    have h := liftFlatTypes_liftArgs (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m₂.store) cx) hpf hys
    rwa [hws] at h
  have hmp : RunsQ (DA P g) th (maybeOnProgress S) m₂ [.tau] () m₂ :=
    RunsQ.getObj_bind _ _ (allocSC_subtasks _ _ _ _) (RunsQ.pure _ _)
  have hstart : ∃ tr, TrapsQ (DA P g) th (lowerOnStart Limits.spec Quirks.none ⟨m.store.callers.length⟩)
      m₂ tr { m₂ with store := LowerSt.startSt S m₂.store } := by
    apply Exists.intro
    apply TrapsQ.bind (RunsQ.getObj _ _ (allocSC_callers _ _ _ _))
    apply TrapsQ.bind hmp
    apply TrapsQ.bind (RunsQ.modify rfl (RunsQ.pure _ _))
    show TrapsQ _ _ (liftFlatValues Limits.spec Quirks.none cx 16 ⟨ys, 0⟩
      ((witFt p).params.map (·.2)) >>= _) _ _ _
    rw [liftFlatValues_witFt hmaxp]
    exact TrapsQ.left (TrapsQ.bind (RunsQ.get (RunsQ.pure _ _)) (TrapsQ.trap _ hT))
  have hfn : TrapsQ (DA P g) th ((answerHostS P g).impl.funcs fn ⟨m.store.callers.length⟩) m₂
      (.tau :: (.tau :: hstart.choose)) { m₂ with store := LowerSt.startSt S m₂.store } :=
    TrapsQ.left (TrapsQ.callIn (TrapsQ.bind (RunsQ.getObj _ _ (allocSC_callers _ _ _ _))
      (TrapsQ.left hstart.choose_spec)))
  obtain ⟨tr', h⟩ := traps_canonLower_of (ys := ys) (p := p) hi hleave hf hfn
  exact ⟨_, _, traps_hostCallout_of hentry h⟩

/-- **A callout whose host function has no answer traps.** -/
theorem traps_callout_host {th : Option ThreadId} {m : Machine.Config (E3 P) σ} {f : FuncId}
    {ft' : WIT.FuncType Empty RtId} {fn : HostFuncId} {inst : InstId} {st : InstState}
    {ys : List Flat} {p : Silmaril.Wasm.Component.FuncTy} {ws : List Silmaril.Wasm.Component.Val}
    (hentry : calloutEntry m.store th (.lowered f (witFt p) {} inst) = none)
    (hi : ArenaField.insts.get? m.store inst = some st) (hleave : st.mayLeave = true)
    (hf : ArenaField.funcs.get? m.store f = some (.host ft' fn))
    (hpf : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmaxp : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws)
    (hg : g m.host fn (ws.map toRefVal) = none) :
    ∃ tr mT, TrapsQ (DA P g) th (DA P g (.hostCallout (.lowered f (witFt p) {} inst) ys)) m tr
      mT := by
  let C : CallerId := ⟨m.store.callers.length⟩
  let m₂ : Machine.Config (E3 P) σ := { m with store := allocSC m.store inst ys p }
  obtain ⟨pos, tr₁, h₁⟩ := runs_lowerOnStart (d := DA P g) (th := th) (m := m₂)
    (allocSC_callers _ _ _ _) (allocSC_subtasks _ _ _ _) rfl hpf hys hmaxp hws
  have hon := runs_onStartLower (g := g) (allocSC_callers m.store inst ys p)
    (fun _ _ _ _ _ _ _ _ => h₁) ⟨_, _, _, _, _, _, _, rfl⟩
  have hfn : ∃ tr, TrapsQ (DA P g) th ((answerHostS P g).impl.funcs fn C) m₂ tr
      { m₂ with store :=
        (LowerSt.setCallerPosSt C pos (LowerSt.startSt ⟨m.store.subtasks.length⟩ m₂.store)) } := by
    apply Exists.intro
    apply TrapsQ.bind (RunsQ.call_bind hon (RunsQ.pure _ _))
    apply TrapsQ.bind (RunsQ.hostGet (RunsQ.pure _ _))
    show TrapsQ _ _ (match g m.host fn (ws.map toRefVal) with
      | some (rs, s') => _
      | none => trap (TrapReason.hostTrap "answerImpl: no answer")) _ _ _
    rw [hg]
    exact TrapsQ.trap _ (isTrap_trap _)
  obtain ⟨tr', h⟩ := traps_canonLower_of (ys := ys) (p := p) hi hleave hf hfn.choose_spec
  exact ⟨_, _, traps_hostCallout_of hentry h⟩

/-- **The store after a callout** has one more subtask and one more caller record. -/
theorem calloutSt_eq (s : CStore (E3 P)) (inst : InstId) (ys : List Flat)
    (p : Silmaril.Wasm.Component.FuncTy) (pos : Nat) (flat : List Flat) :
    calloutSt s inst ys p pos flat =
      { s with
          subtasks := s.subtasks ++ [{ resolvedSub inst flat with lenders := none }]
          callers := s.callers ++ [lowerRec ⟨s.subtasks.length⟩ inst ys p pos] } := by
  have hd := subtasks_resolved s inst ys p pos flat
  simp only [calloutSt, CStore.deliverResolveSt, CStore.subtask?, hd]
  simp [allocSC, ArenaOps.allocSt, ArenaField.alloc, Arena.alloc, ArenaField.modify, Arena.modify,
    ArenaField.subtasks, ArenaField.callers, LowerSt.setOnCancelSt, CStore.subtaskResolveSt,
    LowerSt.setCallerPosSt, LowerSt.startSt, modify_concat_length, resolvedSub, lowerRec,
    LowerSt.Caller.withPos]

end Callout

end Silmaril.Proofs.Wasm.Component.Reference

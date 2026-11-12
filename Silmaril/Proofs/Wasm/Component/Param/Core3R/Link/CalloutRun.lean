module

public import Silmaril.Proofs.Wasm.Component.Reference.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.CalloutRun` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.CalloutRun` that the
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

/-! ## The callout program -/

section Callout

variable {P : Profile} {σ : Type} {d : Call (E3 P V IR) → Canon.P (E3 P V IR) σ (Ret (E3 P V IR))}
  {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)}

/-- The flat arguments of a callout lifted at the parameter types: `liftFlatValues` is the
IR lift, or traps. -/
theorem liftFlatValues_witFt {cx : LiftLowerContext (E3 P V IR)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} (hmax : (ValTy.flatList p.params).length ≤ 16) :
    liftFlatValues Limits.spec Quirks.none cx 16 ⟨ys, 0⟩ ((witFt p).params.map (·.2)) =
      (ptrType cx >>= fun p' => liftFlatTypes Limits.spec Quirks.none cx p'
        (toClosedList p.params) ⟨ys, 0⟩ : Canon.P (E3 P V IR) σ _) := by
  rw [params_witFt]
  exact liftFlatValues_toClosed (max := 16) Limits.spec Quirks.none cx hmax

/-- `on_start` of a `canon_lower` caller record lifts the flat arguments. -/
theorem runs_lowerOnStart {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext (E3 P V IR)} {ys : List Flat}
    {p : Silmaril.Wasm.Component.FuncTy} {xS : Subtask} {ws : List Silmaril.Wasm.Component.Val}
    (hc : ArenaField.callers.get? m.store c = some (.lower S cx ys 0 (witFt p) 16 1))
    (hS : ArenaField.subtasks.get? m.store S = some xS) (hidx : xS.index = none)
    (hff : floatFreeList p.params = true) (hys : ys.map (·.type) = ValTy.flatList p.params)
    (hmax : (ValTy.flatList p.params).length ≤ 16) (hws : liftArgs p.params ys = some ws) :
    ∃ pos tr, RunsQ d th (lowerOnStart Limits.spec Quirks.none c) m tr (ws.map toRefVal)
      { m with store := LowerSt.setCallerPosSt c pos (LowerSt.startSt S m.store) } := by
  have hl : ∃ cur, liftFlatTypes (σ := σ) (E := E3 P V IR) Limits.spec Quirks.none cx
      (ptrTypeIn (LowerSt.startSt S m.store) cx) (toClosedList p.params) ⟨ys, 0⟩ =
        pure (ws.map toRefVal, cur) := by
    have h := liftFlatTypes_liftArgs (σ := σ) (E := E3 P V IR) Limits.spec Quirks.none cx
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
theorem runs_lowerOnResolve {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ} {c : CallerId}
    {S : SubtaskId} {cx : LiftLowerContext (E3 P V IR)} {ys : List Flat} {pos : Nat}
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
      (ptrType cx >>= fun _ => pure (lowerArgs p.results us) : Canon.P (E3 P V IR) σ _) := by
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
abbrev DA (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) :
    Call (E3 P V IR) → Canon.P (E3 P V IR) σ (Ret (E3 P V IR)) := (answerHostS P V IR g).dispatch

/-- The `canon_lower` caller record of a callout with flat arguments `ys` to a function of type
`p`, for subtask `S` of instance `inst`. -/
def lowerRec (S : SubtaskId) (inst : InstId) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy)
    (pos : Nat) : Caller (E3 P V IR) :=
  .lower S { opts := {}, inst := inst, scope := .subtask S } ys pos (witFt p) 16 1

/-- The store after `canonLower` allocated the subtask and the caller record of a callout. -/
def allocSC (s : CStore (E3 P V IR)) (inst : InstId) (ys : List Flat) (p : Silmaril.Wasm.Component.FuncTy) :
    CStore (E3 P V IR) :=
  ArenaOps.allocSt ArenaField.callers (lowerRec (P := P) (V := V) (IR := IR) ⟨s.subtasks.length⟩ inst ys p 0)
    (ArenaOps.allocSt ArenaField.subtasks ({ inst := inst } : Subtask) s)

/-- The end of a synchronous `canonLower` whose subtask has resolved: the resolution is
delivered and the flat results returned. -/
theorem runs_lowerTail {th : Option ThreadId} {m : Machine.Config (E3 P V IR) σ} {S : SubtaskId}
    {X : Subtask} (hS : ArenaField.subtasks.get? m.store S = some X) (hst : X.state = .returned)
    (hlen : X.lenders = some []) :
    RunsQ d th (do
        let resolved ← gets fun x => x.subtaskResolved S
        (if (!resolved) = true then Thread.waitUntilGuest WaitSite.syncLower (ReadyCond.subtaskResolved S)
          else pure () : Canon.P (E3 P V IR) σ Unit)
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

end Callout

end Silmaril.Proofs.Wasm.Component.Param.Core3R

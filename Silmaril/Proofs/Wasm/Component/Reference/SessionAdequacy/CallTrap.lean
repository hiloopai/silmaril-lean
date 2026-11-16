module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.CallAt

/-!
# The deterministic parts of call `k`, with the store of a lift trap

`call_at_kT` is `call_at_kS` (`Adequacy.CallAt`, same proof), recording in addition that the
trap of a failing lift happens at the store the core activation returned with
(`TrapsNextT`, from `lrun_lift_trapT`): the lift reads no state and writes none before it
traps. A resumable session (`SessionAdequacy.Defs`) resumes from the core store of the trapped
configuration, so it needs that store.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type}

/-- From `mS`, the call traps after one live step that keeps the store, with a specification
trap. -/
def TrapsNextT (prof : ProfileKind) (P : Profile) (mS : Machine.Config (E3 P) Unit) : Prop :=
  ∃ mT r, (∀ msg, r ≠ .internal msg) ∧ LRun prof (refHost P).hr (D P) mS [.tau] mT ∧
    (mT.store = mS.store ∧ mT.core = mS.core) ∧ Live mT ∧
    UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT)

/-- `lrun_lift_trapS`, keeping the store. -/
theorem lrun_lift_trapT {α : Type} {th : Option ThreadId} (prof : ProfileKind) (x : SimpleExport)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hff : floatFreeList x.ty.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList x.ty.results)
    (hnone : liftArgs x.ty.results ys = none)
    {cx : LiftLowerContext (E3 P)}
    {f : List Silmaril.Wasm.Component.Reference.Val × FlatCursor → Canon.P (E3 P) Unit α}
    {g : α → Canon.P (E3 P) Unit (Ret (E3 P))} {M : Machine.Config (E3 P) Unit}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (liftedFt x)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) :
    ∃ mT r, (∀ msg, r ≠ .internal msg) ∧ LRun prof (refHost P).hr (D P) M [.tau] mT ∧
      (mT.store = M.store ∧ mT.core = M.core) ∧ Live mT ∧
      UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT) := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x)) =
        (ptrType cx >>= fun p => liftFlatTypes Limits.spec Quirks.none cx p
        (toClosedList x.ty.results) ⟨ys, 0⟩ : Canon.P (E3 P) Unit _) := by
    rw [resultTypes_liftedFt x hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := liftFlatTypes_liftArgsS (σ := Unit) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn (CoreEngine.view _ M.core) cx) hff hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hr, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) Unit) .readCore fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (refHost P).hr (D P) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn (CoreEngine.view _ M.core) cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.readCore hc'
  rw [hk] at s₁
  refine ⟨_, r, hr, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨rfl, rfl⟩, ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl)⟩

/-- `CallAtK`, with specification traps at the returned store where the IR lift fails. -/
structure CallAtKT (prof : ProfileKind) (P : Profile)
    (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat)
    (x : SimpleExport) (a : (E3 P).FuncAddr) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
    (rest : List (Activation (E3 P) Unit)) : Prop
    extends CallAtK prof P cs ι' fs G k j x a vs M₀ th K segs rest where
  trapT : ∀ (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextT prof P (retCfg M₀ th K segs rest y ys)

/-- **The deterministic parts of call `k`** (`call_at_kS`), with the store of a lift trap. -/
theorem call_at_kT (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat)
    (a : (E3 P).FuncAddr) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι'))
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (refHost P).hr (D P)
      (invokedAt cs ι fs G k j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtKT prof P cs ι' fs G k j x a vs M₀ th K segs rest := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (refHost P).hr (D P) (invokedAt cs ι fs G k j (vs.map toRefVal)) _ _
    unfold invokedAt
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (.host ⟨k⟩ (vs.map toRefVal) 0) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) :=
      funcs_get? hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S : CStore (E3 P), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
        threadStatusSt ⟨G.threads.length⟩ .running S =
          { S with threads := G.threads ++ [thread₁ G.tasks] } :=
      fun S h => threadStatus_last h _
    apply LRun.store_congr (S' := store₁ cs ι fs G x k (vs.map toRefVal)) ((e₁ _ rfl).trans rfl)
    have hS₁ : (store₁ cs ι fs G x k (vs.map toRefVal)).insts = [ι] := rfl
    apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
      (runs_enter (Gt := G.tasks) (y := task₀ x G.callers) rfl rfl rfl hS₁ hadd) rfl
    have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
          (store₁ cs ι fs G x k (vs.map toRefVal))) = store₂ cs ι ι' fs G x k (vs.map toRefVal) :=
      enter_eq rfl rfl rfl hadd rfl
    apply LRun.store_congr (S' := store₂ cs ι ι' fs G x k (vs.map toRefVal)) (by exact e₂)
    have hS₂ : (store₂ cs ι ι' fs G x k (vs.map toRefVal)).tasks =
        G.tasks ++ [task₁ x G.callers ⟨G.threads.length⟩] := rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last (Gt := G.tasks) hS₂))
      rfl
    apply RunsQ.chunk rfl (runs_start (Gt := G.tasks) (Gc := G.callers) hS₂ rfl rfl) rfl
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) Unit),
        RunsQ (D P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none cx
          ABI.maxFlatParams (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau]
          (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lower x vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    apply LRun.store_congr (S' := store₃ cs ι ι' fs G x k (vs.map toRefVal))
      (setTaskState_last (Gt := G.tasks) rfl _)
    mstep
    exact .refl _

  refine ⟨⟨rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
  · show ∀ (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
      ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
      ResolvesAt prof P _ (readyCfg y.1 (InstState.removeThread 1 ι') fs
        (nextGarb G x k j a (vs.map toRefVal) (ws.map toRefVal)))
    intro y ys ws hys hws
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · show LRun prof (refHost P).hr (D P) (retCfg _ _ _ _ _ y ys) _ _
      apply LRun.store_congr (S' := store₃ y.1 ι ι' fs G x k (vs.map toRefVal)) rfl
      have hS₃ : (store₃ y.1 ι ι' fs G x k (vs.map toRefVal)).tasks =
          G.tasks ++ [(task₁ x G.callers ⟨G.threads.length⟩).withState .started] := rfl
      unfold retCfg
      apply RunsQ.chunk2 rfl (runs_lift_some x hres hmaxr hffr hys hws _ _).choose_spec rfl
      apply RunsQ.chunk2 rfl
        (runs_return (Gt := G.tasks) (Gc := G.callers) _ hS₃ rfl rfl rfl rfl) rfl
      apply LRun.store_congr (S' := store₄ y.1 ι ι' fs G x k (vs.map toRefVal))
        (by refine setTaskState_last (Gt := G.tasks) ?_ _; rfl)
      apply RunsQ.chunk rfl
        (runs_exit (Gt := G.tasks) (Gth := G.threads)
          (y := ((task₁ x G.callers ⟨G.threads.length⟩).withState .started).withState .resolved)
          (z := (thread₁ G.tasks).withIndex 1) (ι := ι') rfl rfl rfl rfl rfl rfl rfl rfl hrem) rfl
      have e₄ : CStore.unregisterThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩ 1
          (store₄ y.1 ι ι' fs G x k (vs.map toRefVal)) =
            { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
              tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
              insts := [InstState.removeThread 1 ι'] } :=
        unregisterThreadSt_eq _ _ rfl rfl rfl
      apply LRun.store_congr (S' := { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
          tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
          insts := [InstState.removeThread 1 ι'] }) e₄
      mstep
      have e₅ : threadStatusSt ⟨G.threads.length⟩ .exited
          { store₄ y.1 ι ι' fs G x k (vs.map toRefVal) with
            tasks := G.tasks ++ [task₂ x G.callers ⟨G.threads.length⟩]
            insts := [InstState.removeThread 1 ι'] } = store₅ y.1 ι ι' fs G x k (vs.map toRefVal) :=
        threadStatus_last (z := (thread₁ G.tasks).withIndex 1) rfl _
      apply LRun.store_congr (S' := store₅ y.1 ι ι' fs G x k (vs.map toRefVal)) e₅
      apply RunsQ.chunk rfl (runs_callUnit_loop (Gt := G.tasks) rfl rfl) rfl
      mstep
      mstep
      mstep
      exact .refl _
    · rw [hostFinish_cancel _ G.pending ⟨k⟩ ⟨j⟩ (vs.map toRefVal) _ rfl]
      rfl
  · intro y ys hys hn
    exact lrun_lift_trap prof x hres hmaxr hffr hys hn rfl rfl
  · intro y ys hys hn
    exact lrun_lift_trapT prof x hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy

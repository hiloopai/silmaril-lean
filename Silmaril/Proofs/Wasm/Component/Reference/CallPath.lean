module

public import Silmaril.Proofs.Wasm.Component.Reference.CallCore
public import Silmaril.Proofs.Wasm.Component.Reference.Phases
public import Silmaril.Proofs.Wasm.Component.Reference.CallTyping

/-!
# The deterministic parts of an export call

The call of a lifted function from `afterInst`, over `core3P P` with the reference host, up to
the core activation, and from its returned values to the host (`call_at`): a live
deterministic run from the host's invocation (`invokedCfg`) to the configuration running the
core activation on the lowered arguments (`CallAt`), whose continuation, on flat values of the
result types, resolves the call with the IR lift of the values (`Resolves`, with ticks returning
to the final configuration) or traps where the IR lift fails (`TrapsNext`). Lowering and lifting
are the flat ABI agreement of `Silmaril.Proofs.Wasm.Component.Reference.FlatABI`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type}

/-- The engine. -/
abbrev E3 (P : Profile) : CoreEngine := core3P P

/-- The dispatcher of the reference host. -/
abbrev D (P : Profile) : Call (E3 P) → Canon.P (E3 P) Unit (Ret (E3 P)) :=
  (refHost P).dispatch

/-- The host caller record of top-level call `0`. -/
def hostCaller (args : List Val) : Caller (E3 P) := .host ⟨0⟩ args 0

theorem runs_allocObj {d : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))} {α Id : Type}
    {th : Option ThreadId} (F : ArenaField (E3 P) Id α) (x : α)
    (m : Machine.Config (E3 P) σ)
    (hl : (ArenaOps.allocSt F x m.store).lockdown = m.store.lockdown) :
    RunsQ d th (allocObj F x) m [.tau, .tau] (F.mkId (F.size m.store))
      { m with store := ArenaOps.allocSt F x m.store } :=
  .get (.modify hl (.pure _ _))

macro "mstep" : tactic => `(tactic| apply LRun.prog rfl (fun _ _ e => by cases e) rfl
  (by first
    | exact Step.get rfl | exact Step.modify rfl | exact Step.call rfl | exact Step.popProg rfl
    | exact Step.currentThread rfl | exact Step.hostGet rfl | exact Step.hostSet rfl
    | exact Step.emit rfl
    | exact Step.resumeThread rfl rfl | exact Step.newThread rfl rfl | exact Step.threadExit rfl
    | exact Step.hostDone rfl | exact Step.callCore rfl))

theorem runs_getObj {d : Call (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))} {α Id : Type}
    {th : Option ThreadId} (F : ArenaField (E3 P) Id α) (i : Id)
    (m : Machine.Config (E3 P) σ) {x : α} (h : F.get? m.store i = some x) :
    RunsQ d th (getObj F i) m [.tau] x m := by
  refine .get ?_
  show RunsQ _ _ (match F.get? m.store i with | some x => pure x | none => internal _) _ _ _ _
  rw [h]
  exact .pure _ _

theorem paramTypes_liftedFt (x : SimpleExport) :
    paramTypes (liftedFt x) = toClosedList x.ty.params := labels_map_snd _ _

theorem runs_lower {th : Option ThreadId} (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (cx : LiftLowerContext (E3 P))
    (hf : floatFreeList x.ty.params = true) (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16) (m : Machine.Config (E3 P) Unit) :
    RunsQ (D P) th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams (vs.map toRefVal)
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
    (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) Unit) :
    ∃ c, RunsQ (D P) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x))) m [.tau] (ws.map toRefVal, c) m := by
  have h := liftFlatTypes_liftArgs (σ := Unit) (E := E3 P) Limits.spec Quirks.none cx
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
    {cx : LiftLowerContext (E3 P)} {f : List Val × FlatCursor → Canon.P (E3 P) Unit α}
    {g : α → Canon.P (E3 P) Unit (Ret (E3 P))} {M : Machine.Config (E3 P) Unit}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (liftedFt x)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) :
    ∃ mT r, LRun prof (refHost P).hr (D P) M [.tau] mT ∧ Live mT ∧
      UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT) := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x)) =
        (ptrType cx >>= fun p => liftFlatTypes Limits.spec Quirks.none cx p
        (toClosedList x.ty.results) ⟨ys, 0⟩ : Canon.P (E3 P) Unit _) := by
    rw [resultTypes_liftedFt x hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := liftFlatTypes_liftArgs (σ := Unit) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn M.store cx) hff hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) Unit) .get fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (refHost P).hr (D P) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn M.store cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.get hc'
  rw [hk] at s₁
  refine ⟨_, r, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl)⟩


/-- The configuration after the host invoked function `j` on `args` from `afterInst`. -/
def invokedCfgH (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h : σ) (j : Nat) (args : List Val) :
    Machine.Config (E3 P) σ :=
  { afterInstH P cs fs h with
    pending := [] ++ [(⟨0⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨0⟩ ⟨j⟩ args)] }

/-- The configuration after the host invoked function `j` on `args` from `afterInst`. -/
abbrev invokedCfg (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (j : Nat) (args : List Val) : Machine.Config (E3 P) Unit :=
  invokedCfgH P cs fs () j args

/-- From `mS`, the call resolves with `rs`: a live run to a configuration with the host in
control, results `rs`, from which a tick returns to itself. -/
def Resolves (prof : ProfileKind) (P : Profile) (mS : Machine.Config (E3 P) Unit)
    (rs : List Val) : Prop :=
  ∃ tr mE, LRun prof (refHost P).hr (D P) mS tr mE ∧ mE.ctl = [] ∧
    mE.store.lockdown = false ∧ mE.result? ⟨0⟩ = some (some rs) ∧
    ∀ m₁, Step prof (refHost P).hr (D P) mE (.host .tick) m₁ →
      ∃ trT, LRun prof (refHost P).hr (D P) m₁ trT mE

/-- From `mS`, the call traps after one live step. -/
def TrapsNext (prof : ProfileKind) (P : Profile) (mS : Machine.Config (E3 P) Unit) : Prop :=
  ∃ mT r, LRun prof (refHost P).hr (D P) mS [.tau] mT ∧ Live mT ∧
    UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT)

/-- The configuration `M₀` runs the core activation of export `x` (address `a`) on the
lowered values of `vs`; when it returns flat values of the result types, the call resolves
or traps as the IR lift prescribes. -/
structure CallAt (prof : ProfileKind) (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config (E3 P) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
    (rest : List (Activation (E3 P) Unit)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    Resolves prof P (retCfg M₀ th K segs rest y ys) (ws.map toRefVal)
  trap : ∀ (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNext prof P (retCfg M₀ th K segs rest y ys)

/-- The function value `j` of `fs` is the lift of export `x` at core address `a`. -/
theorem funcs_get? {fs : List (CFuncInst (core3P P))} {j a : Nat} {x : SimpleExport}
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) (s : CStore (E3 P)) (e : s.funcs = fs) :
    ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) := by
  simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
  exact hf

/-- **The deterministic parts of an export call.** -/
theorem call_at (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (j a : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (refHost P).hr (D P)
      (invokedCfg P cs fs j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAt prof P cs x a vs M₀ th K segs rest := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (refHost P).hr (D P) (invokedCfg P cs fs j (vs.map toRefVal)) _ _
    unfold invokedCfg
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (hostCaller (vs.map toRefVal)) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) :=
      funcs_get? hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk rfl (RunsQ.get (.pure _ _)) rfl
    iterate 14 mstep
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) Unit),
        RunsQ (D P) (some ⟨0⟩) (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
          (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau] (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lower x vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    mstep
    exact .refl _
  apply CallAt.mk
  · rfl
  · rfl
  · rfl
  · show ∀ (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
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

end Silmaril.Proofs.Wasm.Component.Reference

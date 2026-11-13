module

public import Silmaril.Proofs.Wasm.Component.Reference.CalloutCore

/-!
# The deterministic parts of an export call with imports

`call_atA`: the call of a lifted function from `afterInst`, over `core3P P` with the host
`answerHostS P g` (a stateful host; `answerHost P g` is its stateless instance), up to the core activation, and from its returned values to the host. As
`call_at` (`CallPath`), with the dispatcher of `answerHostS P g` (a stateful host; `answerHost P g` is its stateless instance); the return is taken from any
configuration whose store has the subtask and caller records of the callouts appended
(`extSC`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)} {prof : ProfileKind}

/-- From `mS`, the call resolves with `rs` under `answerHostS P g` (a stateful host; `answerHost P g` is its stateless instance). -/
def ResolvesA (prof : ProfileKind) (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (mS : Machine.Config (E3 P) σ) (rs : List Silmaril.Wasm.Component.Reference.Val) : Prop :=
  ∃ tr mE, LRun prof (answerHostS P g).hr (DA P g) mS tr mE ∧ mE.ctl = [] ∧
    mE.store.lockdown = false ∧ mE.result? ⟨0⟩ = some (some rs) ∧
    ∀ m₁, Step prof (answerHostS P g).hr (DA P g) mE (.host .tick) m₁ →
      ∃ trT, LRun prof (answerHostS P g).hr (DA P g) m₁ trT mE

/-- From `mS`, the call traps after one live step under `answerHostS P g` (a stateful host; `answerHost P g` is its stateless instance). -/
def TrapsNextA (prof : ProfileKind) (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (mS : Machine.Config (E3 P) σ) : Prop :=
  ∃ mT r, LRun prof (answerHostS P g).hr (DA P g) mS [.tau] mT ∧ Live mT ∧
    UniqueStep prof (answerHostS P g).hr (DA P g) mT (.trap r) (trapCfg mT)

/-- The configuration `M₀` runs the core activation of export `x` (address `a`) on the
lowered values of `vs`; whenever it returns flat values of the result types, after callouts
that appended subtask and caller records, the call resolves or traps as the IR lift
prescribes. -/
structure CallAtA (prof : ProfileKind) (P : Profile) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (cs : (core3P P).Store (CanonHost (core3P P))) (fs : List (CFuncInst (core3P P)))
    (x : SimpleExport) (a : Nat)
    (vs : List Silmaril.Wasm.Component.Val) (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  funcs : M₀.store.funcs = fs
  entry : ∀ f ft opts, calloutEntry M₀.store th (.lowered f ft opts ⟨0⟩) = none
  inst : ∃ st, ArenaField.insts.get? M₀.store ⟨0⟩ = some st ∧ st.mayLeave = true
  ret : ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P))) (y : CoreSt (E3 P))
    (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesA prof P g (retCfg (extSC (withH M₀ s) ST CL) th K segs rest y ys) (ws.map toRefVal)
  trap : ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P))) (y : CoreSt (E3 P))
    (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextA prof P g (retCfg (extSC (withH M₀ s) ST CL) th K segs rest y ys)

theorem lrun_lift_trapA {α : Type} {th : Option ThreadId} (prof : ProfileKind) (x : SimpleExport)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hff : floatFreeList x.ty.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList x.ty.results)
    (hnone : liftArgs x.ty.results ys = none)
    {cx : LiftLowerContext (E3 P)} {f : List Silmaril.Wasm.Component.Reference.Val × FlatCursor → Canon.P (E3 P) σ α}
    {k : α → Canon.P (E3 P) σ (Ret (E3 P))} {M : Machine.Config (E3 P) σ}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (liftedFt x)) >>= f) >>= k), segs⟩ :: rest)
    (hl : M.store.lockdown = false) : TrapsNextA prof P g M := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x)) =
        (ptrType cx >>= fun p => liftFlatTypes Limits.spec Quirks.none cx p
        (toClosedList x.ty.results) ⟨ys, 0⟩ : Canon.P (E3 P) σ _) := by
    rw [resultTypes_liftedFt x hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT : IsTrap (liftFlatTypes (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
      (ptrTypeIn M.store cx) (toClosedList x.ty.results) ⟨ys, 0⟩) := by
    have h := liftFlatTypes_liftArgs (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
      (ptrTypeIn M.store cx) hff hys
    rwa [hnone] at h
  obtain ⟨r, k₀, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) σ) .get fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= k), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (answerHostS P g).hr (DA P g) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn M.store cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= k), segs⟩ :: rest } := Step.get hc'
  rw [hk] at s₁
  exact ⟨_, r, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl)⟩

theorem runs_lift_someA {th : Option ThreadId} (x : SimpleExport)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hff : floatFreeList x.ty.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList x.ty.results)
    {ws : List Silmaril.Wasm.Component.Val} (hws : liftArgs x.ty.results ys = some ws)
    (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ) :
    ∃ c, RunsQ (DA P g) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (liftedFt x))) m [.tau] (ws.map toRefVal, c) m := by
  have h := liftFlatTypes_liftArgs (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
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

theorem runs_lowerA {th : Option ThreadId} (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (cx : LiftLowerContext (E3 P))
    (hf : floatFreeList x.ty.params = true) (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16) (m : Machine.Config (E3 P) σ) :
    RunsQ (DA P g) th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
      (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau]
      (Silmaril.Wasm.Component.lowerArgs x.ty.params vs) m := by
  rw [paramTypes_liftedFt, lowerFlatValues_toClosed (max := ABI.maxFlatParams) _ _ _ hf hck hmax]
  exact .get (.pure _ _)

/-- **The deterministic parts of an export call with imports.** -/
theorem call_atA (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h₀ : σ) (j a : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (answerHostS P g).hr (DA P g)
      (invokedCfgH P cs fs h₀ j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAtA prof P g cs fs x a vs M₀ th K segs rest ∧ M₀.host = h₀ := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (answerHostS P g).hr (DA P g) (invokedCfgH P cs fs h₀ j (vs.map toRefVal)) _ _
    unfold invokedCfgH
    apply RunsQ.chunk rfl
      (runsQ_allocObj (d := DA P g) ArenaField.callers (hostCaller (vs.map toRefVal)) rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P), s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) :=
      funcs_get? hf
    apply RunsQ.chunk rfl (RunsQ.getObj (dispatch := DA P g) _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runsQ_allocObj (d := DA P g) ArenaField.tasks _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk rfl (RunsQ.get (.pure _ _)) rfl
    iterate 14 mstep
    have hlow : ∀ (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ),
        RunsQ (DA P g) (some ⟨0⟩) (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
          (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau] (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lowerA x vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    mstep
    exact .refl _
  refine ⟨?_, rfl⟩
  apply CallAtA.mk
  · rfl
  · rfl
  · rfl
  · rfl
  · intro f ft opts
    rfl
  · exact ⟨_, rfl, rfl⟩
  · show ∀ (s : σ) (ST : List Subtask) (CL : List (Caller (E3 P))) (y : CoreSt (E3 P))
      (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
      ResolvesA prof P g (retCfg (extSC (withH _ s) ST CL) _ _ _ _ y ys) (ws.map toRefVal)
    intro s ST CL y ys ws hys hws
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · unfold retCfg
      apply RunsQ.chunk2 rfl (runs_lift_someA (g := g) x hres hmaxr hffr hys hws _ _).choose_spec rfl
      repeat mstep
      exact .refl _
    refine ⟨rfl, rfl, rfl, ?_⟩
    · intro m₁ hs
      cases hs
      apply Exists.intro
      repeat mstep
      exact .refl _
  · intro s ST CL y ys hys hn
    exact lrun_lift_trapA prof x hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Reference

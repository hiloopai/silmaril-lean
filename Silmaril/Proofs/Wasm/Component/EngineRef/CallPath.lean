module

public import Silmaril.Proofs.Wasm.Component.EngineRef.Inst
public import Silmaril.Proofs.Wasm.Component.Reference.CallRun

/-!
# The call path over any engine

`Silmaril.Proofs.Wasm.Component.Reference.CallPath` over an arbitrary engine `E` (provenance: a copy
of the `Path` section of `Param.Core3R.Call`, with `core3R P V IR` replaced by `E`): from
`afterInstE`, the host invocation of a lifted export runs deterministically to the core
activation `E.invoke a xs` of its core function on the lowered arguments (`call_at`), and a
returned activation resolves or traps as the IR lift prescribes (`CallAt`).

New proofs (copied structure).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.EngineRef

open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.EngineRef Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)

/-! ## The call path (`Reference.CallPath`) -/

section Path

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- The dispatcher of the reference host. -/
abbrev D (E : Engine) [∀ a b, Decidable (E.ExternSub a b)] : Call E → Canon.P E Unit (Ret E) :=
  (refHostE E).dispatch

/-- The host caller record of top-level call `0`. -/
def hostCaller (args : List Val) : Caller E := .host ⟨0⟩ args 0

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem runs_allocObj {d : Call E → Canon.P E σ (Ret E)} {α Id : Type}
    {th : Option ThreadId} (F : ArenaField E Id α) (x : α)
    (m : Machine.Config E σ)
    (hl : (ArenaOps.allocSt F x m.store).lockdown = m.store.lockdown) :
    RunsQ d th (allocObj F x) m [.tau, .tau] (F.mkId (F.size m.store))
      { m with store := ArenaOps.allocSt F x m.store } :=
  .get (.modify hl (.pure _ _))


omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem runs_getObj {d : Call E → Canon.P E σ (Ret E)} {α Id : Type}
    {th : Option ThreadId} (F : ArenaField E Id α) (i : Id)
    (m : Machine.Config E σ) {x : α} (h : F.get? m.store i = some x) :
    RunsQ d th (getObj F i) m [.tau] x m := by
  refine .get ?_
  show RunsQ _ _ (match F.get? m.store i with | some x => pure x | none => internal _) _ _ _ _
  rw [h]
  exact .pure _ _

theorem paramTypes_liftedFt (x : SimpleExport) :
    paramTypes (liftedFt x) = toClosedList x.ty.params := labels_map_snd _ _

theorem runs_lower {th : Option ThreadId} (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (cx : LiftLowerContext E)
    (hf : floatFreeList x.ty.params = true) (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16) (m : Machine.Config E Unit) :
    RunsQ (D E) th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams (vs.map toRefVal)
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
    (cx : LiftLowerContext E) (m : Machine.Config E Unit) :
    ∃ c, RunsQ (D E) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x))) m [.tau] (ws.map toRefVal, c) m := by
  have h := liftFlatTypes_liftArgs (σ := Unit) (E := E) Limits.spec Quirks.none cx
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
    {cx : LiftLowerContext E} {f : List Val × FlatCursor → Canon.P E Unit α}
    {g : α → Canon.P E Unit (Ret E)} {M : Machine.Config E Unit}
    {segs : List (Seg E Unit)} {rest : List (Activation E Unit)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (liftedFt x)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) :
    ∃ mT r, LRun prof (refHostE E).hr (D E) M [.tau] mT ∧ Live mT ∧
      UniqueStep prof (refHostE E).hr (D E) mT (.trap r) (trapCfg mT) := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x)) =
        (ptrType cx >>= fun p => liftFlatTypes Limits.spec Quirks.none cx p
        (toClosedList x.ty.results) ⟨ys, 0⟩ : Canon.P E Unit _) := by
    rw [resultTypes_liftedFt x hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := liftFlatTypes_liftArgs (σ := Unit) (E := E) Limits.spec Quirks.none cx
    (ptrTypeIn M.store cx) hff hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff E Unit) .get fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (refHostE E).hr (D E) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn M.store cx) (toClosedList x.ty.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.get hc'
  rw [hk] at s₁
  refine ⟨_, r, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl)⟩


/-- The configuration after the host invoked function `j` on `args` from `afterInstE`. -/
noncomputable def invokedCfg (cs : E.Store (CanonHost E)) (fs : List (CFuncInst E)) (j : Nat)
    (args : List Val) : Machine.Config E Unit :=
  { afterInstE cs fs with
    pending := [] ++ [(⟨0⟩, ⟨j⟩, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨0⟩ ⟨j⟩ args)] }

/-- From `mS`, the call resolves with `rs`: a live run to a configuration with the host in
control, results `rs`, from which a tick returns to itself. -/
def Resolves (prof : ProfileKind) (mS : Machine.Config E Unit)
    (rs : List Val) : Prop :=
  ∃ tr mE, LRun prof (refHostE E).hr (D E) mS tr mE ∧ mE.ctl = [] ∧
    mE.store.lockdown = false ∧ mE.result? ⟨0⟩ = some (some rs) ∧
    ∀ m₁, Step prof (refHostE E).hr (D E) mE (.host .tick) m₁ →
      ∃ trT, LRun prof (refHostE E).hr (D E) m₁ trT mE

/-- From `mS`, the call traps after one live step. -/
def TrapsNext (prof : ProfileKind) (mS : Machine.Config E Unit) : Prop :=
  ∃ mT r, LRun prof (refHostE E).hr (D E) mS [.tau] mT ∧ Live mT ∧
    UniqueStep prof (refHostE E).hr (D E) mT (.trap r) (trapCfg mT)

/-- The configuration `M₀` runs the core activation of export `x` (address `a`) on the
lowered values of `vs`; when it returns flat values of the result types, the call resolves
or traps as the IR lift prescribes. -/
structure CallAt (prof : ProfileKind) (cs : E.Store (CanonHost E))
    (x : SimpleExport) (a : E.FuncAddr) (vs : List Silmaril.Wasm.Component.Val)
    (M₀ : Machine.Config E Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P E Unit (Ret E)) (segs : List (Seg E Unit))
    (rest : List (Activation E Unit)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (E.invoke a (lowerArgs x.ty.params vs)) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ (y : CoreSt E) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    Resolves prof (retCfg M₀ th K segs rest y ys) (ws.map toRefVal)
  trap : ∀ (y : CoreSt E) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNext prof (retCfg M₀ th K segs rest y ys)

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The function value `j` of `fs` is the lift of export `x` at core address `a`. -/
theorem funcs_get? {fs : List (CFuncInst E)} {j : Nat} {a : E.FuncAddr} {x : SimpleExport}
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) (s : CStore E) (e : s.funcs = fs) :
    ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) := by
  simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
  exact hf

/-- **The deterministic parts of an export call.** -/
theorem call_at (prof : ProfileKind) (cs : E.Store (CanonHost E))
    (fs : List (CFuncInst E)) (j : Nat) (a : E.FuncAddr) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (hff : floatFreeList x.ty.params = true)
    (hck : ValTy.checkList x.ty.params vs = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ M₀ th K segs rest tr₁, LRun prof (refHostE E).hr (D E)
      (invokedCfg cs fs j (vs.map toRefVal)) tr₁ M₀ ∧
      CallAt prof cs x a vs M₀ th K segs rest := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  · show LRun prof (refHostE E).hr (D E) (invokedCfg cs fs j (vs.map toRefVal)) _ _
    unfold invokedCfg
    apply RunsQ.chunk rfl
      (runs_allocObj ArenaField.callers (hostCaller (vs.map toRefVal)) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore E, s.funcs = fs →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) = some (.lifted a (liftedFt x) {} ⟨0⟩) :=
      funcs_get? hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk rfl (RunsQ.get (.pure _ _)) rfl
    iterate 14 mstep
    have hlow : ∀ (cx : LiftLowerContext E) (m : Machine.Config E Unit),
        RunsQ (D E) (some ⟨0⟩) (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
          (vs.map toRefVal) (paramTypes (liftedFt x)) none) m [.tau] (lowerArgs x.ty.params vs) m :=
      fun cx m => runs_lower x vs cx hff hck hmax m
    apply RunsQ.chunk rfl (hlow _ _) rfl
    mstep
    exact .refl _
  apply CallAt.mk
  · rfl
  · rfl
  · rfl
  · show ∀ (y : CoreSt E) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
      Resolves prof (retCfg _ _ _ _ _ y ys) (ws.map toRefVal)
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

end Silmaril.Proofs.Wasm.Component.EngineRef

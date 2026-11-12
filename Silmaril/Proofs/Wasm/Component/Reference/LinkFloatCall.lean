module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCall
public import Silmaril.Proofs.Wasm.Component.Reference.FloatVCall

/-!
# The top-level call of a linked component with floats in the importer's export

`call_atL` (`LinkCall`) with floats at every type in the importer's export `x`, variant payloads
included. Lowering the arguments issues NaN choices (C7), so the run from the host's invocation
branches: `call_at_floatL` runs deterministically to the lowering of the arguments and, for
every flat argument list `xs`, from its result to the importer's core activation on `xs`
(`CallAtLV`, `CallAtL` on `xs` with canonicalised results); `call_trunL` (a `TRun`) collects the
branches: every run from the invocation stays live until it reaches the core activation of
`lowerArgs x.ty.params vs'` for an admissible lowering `vs'` of `vs` (`NanAtVList prof`).
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

/-! ## Lifting results with floats under `DI P impl` -/

theorem runs_lift_somePV {th : Option ThreadId} (p : Silmaril.Wasm.Component.FuncTy)
    (hres : p.results.length ≤ 1) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    {ys : List Flat} (hys : ys.map (·.type) = ValTy.flatList p.results)
    {ws : List Silmaril.Wasm.Component.Val} (hws : liftArgs p.results ys = some ws)
    (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) σ) :
    ∃ c, RunsQ (DI P impl) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (witFt p))) m [.tau]
      ((canonAtVList p.results ws).map toRefVal, c) m := by
  have h := liftFlatTypes_liftArgs_floatV (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn m.store cx) hys
  rw [hws] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [resultTypes_witFt p hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
    liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  refine .get ?_
  show RunsQ _ _ (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn m.store cx)
    (toClosedList p.results) ⟨ys, 0⟩) _ _ _ _
  rw [hc]
  exact .pure _ _

theorem lrun_lift_trapPV {α : Type} {th : Option ThreadId} (p : Silmaril.Wasm.Component.FuncTy)
    (hres : p.results.length ≤ 1) (hmaxr : (ValTy.flatList p.results).length ≤ 1)
    {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList p.results) (hnone : liftArgs p.results ys = none)
    {cx : LiftLowerContext (E3 P)} {f : List Val × FlatCursor → Canon.P (E3 P) σ α}
    {g : α → Canon.P (E3 P) σ (Ret (E3 P))} {M : Machine.Config (E3 P) σ}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog ((liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList ys) (resultTypes (witFt p)) >>= f) >>= g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) : TrapsNextD prof P impl M := by
  have e : liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (witFt p)) =
        (ptrType cx >>= fun q => liftFlatTypes Limits.spec Quirks.none cx q
        (toClosedList p.results) ⟨ys, 0⟩ : Canon.P (E3 P) σ _) := by
    rw [resultTypes_witFt p hres, show FlatCursor.ofList ys = ⟨ys, 0⟩ from rfl,
      liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none cx hmaxr]
  have hT := liftFlatTypes_liftArgs_floatV (σ := σ) (E := E3 P) Limits.spec Quirks.none cx
    (ptrTypeIn M.store cx) hys
  rw [hnone] at hT
  obtain ⟨r, k₀, hk⟩ := hT
  have hc' : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) σ) .get fun s =>
      (liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toClosedList p.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest := by
    rw [hc, e]
    rfl
  have s₁ : Step prof (fun _ _ => false) (DI P impl) M .tau { M with ctl := ⟨th, .prog
      ((liftFlatTypes Limits.spec Quirks.none cx (ptrTypeIn M.store cx) (toClosedList p.results)
        ⟨ys, 0⟩ >>= f) >>= g), segs⟩ :: rest } := Step.get hc'
  rw [hk] at s₁
  exact ⟨_, r, .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) s₁) (.refl _), ⟨List.cons_ne_nil _ _, hl⟩,
    .of_prog rfl (fun _ _ e => by cases e) (.trap rfl)⟩

/-- A `get` in focus is one live deterministic step under `DI P impl`. -/
theorem uniqueStep_getD {M : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {g : CStore (E3 P) → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)}
    (hc : M.ctl = ⟨th, .prog (.op (S := Eff (E3 P) σ) .get g), segs⟩ :: rest)
    (hl : M.store.lockdown = false) :
    LRun prof (fun _ _ => false) (DI P impl) M [.tau]
      { M with ctl := ⟨th, .prog (g M.store), segs⟩ :: rest } :=
  .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩
    (.of_prog hc (fun _ _ e => by cases e) (.get hc)) (.refl _)

/-! ## The call on flat arguments -/

/-- `CallAtL` on the flat arguments `xs`, with canonicalised results. -/
structure CallAtLV (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (cs : (core3P P).Store (CanonHost (core3P P))) (fs : List (CFuncInst (core3P P)))
    (x : SimpleExport) (a : Nat) (xs : List Flat)
    (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop where
  start : M₀ = coreCfg (extN M₀ {} [] M₀.conts) th K segs rest
    (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)
  funcs : M₀.store.funcs = fs
  frame : LFrame M₀ th
  ret : ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesD prof P impl (retCfg (extN M₀ ιe N C) th K segs rest y ys)
      ((canonAtVList x.ty.results ws).map toRefVal)
  trap : ∀ (ιe : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextD prof P impl (retCfg (extN M₀ ιe N C) th K segs rest y ys)

/-- **The machine path of the importer's top-level call with floats**: a live run to the
lowering of the arguments, after which, for every flat argument list `xs`, a live run reaches
the importer's core activation on `xs`. -/
theorem call_at_floatL (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h₀ : σ) (j a : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨2⟩)) :
    ∃ (Mℓ : Machine.Config (E3 P) σ) (th : Option ThreadId) (cx : LiftLowerContext (E3 P))
      (f : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
      (rest : List (Activation (E3 P) σ)) (tr₁ : List (Label (E3 P) σ)),
      LRun prof (fun _ _ => false) (DI P impl) (invoked3 P cs fs h₀ j (vs.map toRefVal)) tr₁ Mℓ ∧
      Mℓ.ctl = ⟨th, .prog (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
        (vs.map toRefVal) (paramTypes (liftedFt x)) none >>= f), segs⟩ :: rest ∧
      Mℓ.store.lockdown = false ∧
      ∀ xs : List Flat,
        ∃ M₀ th' K segs' rest' tr₂, LRun prof (fun _ _ => false) (DI P impl)
          { Mℓ with ctl := ⟨th, .prog (f xs), segs⟩ :: rest } tr₂ M₀ ∧
          CallAtLV prof P impl cs fs x a xs M₀ th' K segs' rest' := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?pre, ?c₁, ?c₂, ?post⟩
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
    exact .refl _
  · rfl
  · rfl
  · intro xs
    apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · mstep
      apply LRun.store_congr (S' := storeLN cs {} (enterInst {} ⟨0⟩) fs
        ((taskL x).withState .started) threadL (vs.map toRefVal) []) rfl
      exact .refl _
    apply CallAtLV.mk
    · rfl
    · rfl
    · exact ⟨fun _ _ _ _ _ => rfl, ⟨_, rfl, rfl⟩⟩
    · intro ιe N C y ys ws hys hws
      apply Exists.intro; apply Exists.intro
      apply And.intro
      · show LRun prof (fun _ _ => false) (DI P impl) (retCfg _ _ _ _ _ y ys) _ _
        apply LRun.store_congr (S' := storeLN y.1 ιe (enterInst {} ⟨0⟩) fs
          ((taskL x).withState .started) threadL (vs.map toRefVal) N) rfl
        unfold retCfg
        apply RunsQ.chunk2 rfl (runs_lift_somePV x.ty hres hmaxr hys hws _ _).choose_spec rfl
        apply RunsQ.chunk2 rfl (runs_returnH (CL := N.map (·.caller)) _ rfl rfl rfl rfl rfl) rfl
        apply LRun.store_congr (S' := storeLN y.1 ιe (enterInst {} ⟨0⟩) fs
          (((taskL x).withState .started).withState .resolved) threadL (vs.map toRefVal) N) rfl
        have hrem : (enterInst ({} : InstState) ⟨0⟩).removeThread? 1 =
            some (⟨0⟩, InstState.removeThread 1 (enterInst {} ⟨0⟩)) := removeThread?_enter {} ⟨0⟩
        apply RunsQ.chunk rfl (runs_exitH rfl rfl rfl rfl rfl rfl rfl hrem) rfl
        apply LRun.store_congr (S' := storeLN y.1 ιe (InstState.removeThread 1 (enterInst {} ⟨0⟩))
          fs (taskRetL x) threadL (vs.map toRefVal) N) rfl
        mstep
        apply LRun.store_congr (S' := storeLN y.1 ιe (InstState.removeThread 1 (enterInst {} ⟨0⟩))
          fs (taskRetL x) { threadL with status := .exited } (vs.map toRefVal) N) rfl
        have hloop : ∀ (th : Option ThreadId) (m : Machine.Config (E3 P) σ),
            m.store.tasks = taskRetL x :: N.map (·.task) →
            RunsQ (DI P impl) th (callUnit (.loop (.syncLiftLoop ⟨0⟩))) m [.tau, .tau, .tau] () m :=
          fun _ _ h => runs_callUnit_loopH h rfl
        apply RunsQ.chunk rfl (hloop _ _ rfl) rfl
        iterate 3 mstep
        exact .refl _
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro m₁ hs
      cases hs
      apply Exists.intro
      repeat mstep
      exact .refl _
    · intro ιe N C y ys hys hn
      exact lrun_lift_trapPV x.ty hres hmaxr hys hn rfl rfl

/-! ## The branching run -/

/-- The configurations running the importer's core activation of an admissible argument list. -/
def QL (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (cs : (core3P P).Store (CanonHost (core3P P))) (fs : List (CFuncInst (core3P P)))
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (m : Machine.Config (E3 P) σ) : Prop :=
  ∃ vs' th K segs rest, NanAtVList prof x.ty.params vs vs' ∧
    ValTy.checkList x.ty.params vs' = true ∧
    CallAtLV prof P impl cs fs x a (lowerArgs x.ty.params vs') m th K segs rest

/-- **The branching run of the importer's top-level call with floats**: every run from the
host's invocation stays live until it reaches the importer's core activation of an admissible
argument list. -/
theorem call_trunL (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h₀ : σ) (j a : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨2⟩)) :
    TRun prof (fun _ _ => false) (DI P impl) (QL prof P impl cs fs x a vs)
      (invoked3 P cs fs h₀ j (vs.map toRefVal)) := by
  obtain ⟨Mℓ, th, cx, f, segs, rest, tr₁, hpre, hc, hl, hpost⟩ :=
    call_at_floatL (impl := impl) prof cs fs h₀ j a x vs hres hmaxr hf
  have hc' : Mℓ.ctl = ⟨th, .prog (.op (S := Eff (E3 P) σ) .get fun s =>
      lowerFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toRefVals vs)
        (toClosedList x.ty.params) >>= f), segs⟩ :: rest := by
    rw [hc, paramTypes_liftedFt, lowerFlatValues_float (max := ABI.maxFlatParams) _ _ _ hmax]
    rfl
  have hch := lowerFlatTypesV (E := E3 P) (σ := σ) Limits.spec Quirks.none cx
    (ptrTypeIn Mℓ.store cx) prof x.ty.params vs hck
  have ht := ChoiceProg.trun (hr := fun _ _ => false) (dispatch := DI P impl) hch
    { Mℓ with ctl := ⟨th, .prog (lowerFlatTypes Limits.spec Quirks.none cx (ptrTypeIn Mℓ.store cx)
      (toRefVals vs) (toClosedList x.ty.params) >>= f), segs⟩ :: rest } f th segs rest rfl hl
  refine TRun.of_lrun hpre (TRun.of_lrun (uniqueStep_getD hc' hl) (ht.bind ?_))
  rintro m ⟨out, ⟨vs', hn, hck', rfl⟩, rfl⟩
  obtain ⟨M₀, th', K, segs', rest', tr₂, hl₁, hat⟩ := hpost (lowerArgs x.ty.params vs')
  exact TRun.of_lrun hl₁ (.done ⟨vs', th', K, segs', rest', hn, hck', hat⟩)

end Silmaril.Proofs.Wasm.Component.Reference

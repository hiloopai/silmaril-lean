module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCallK
public import Silmaril.Proofs.Wasm.Component.Reference.LinkFloatCall

/-!
# The top-level call of a linked component between other calls, with floats

`call_atLK` (`LinkCallK`) with floats at every type in the importer's export `x`, variant
payloads included, as `call_at_floatL` is `call_atL` with floats. From a configuration between
linked calls (`readyCfgL`), `call_atLKV` runs deterministically to the lowering of the
arguments and, for every flat argument list `xs`, from its result to the importer's core
activation on `xs` (`CallAtLKV`: `CallAtLK` on `xs`, the results reported canonicalised
(`canonAtVList`) in the next configuration between calls); `call_trunLK` (a `TRun`) collects
the branches over the NaN choices of lowering the arguments: every run from the invocation stays
live until it reaches the core activation of `lowerArgs x.ty.params vs'` for an admissible
lowering `vs'` of `vs` (`NanAtVList prof`).
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

/-- `CallAtLK` on the flat arguments `xs` of the call on `args`, the results reported
canonicalised in the next configuration between calls. -/
structure CallAtLKV (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi' : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h₀ : σ) (k j : Nat)
    (x : SimpleExport) (a : Nat) (args : List Val) (xs : List Flat)
    (M₀ : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) : Prop where
  start : M₀ = coreCfg (extN M₀ ιe [] M₀.conts) th K segs rest
    (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)
  funcs : M₀.store.funcs = fs
  frame : LFrame M₀ th
  ret : ∀ (ιe' : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ∃ C', ResolvesAtL prof P impl (retCfg (extN M₀ ιe' N C) th K segs rest y ys)
      (readyCfgL y.1 ιe' (InstState.removeThread 1 ιi') fs
        (nextGarbL G x k j args ((canonAtVList x.ty.results ws).map toRefVal) N C')
        (ST ++ N.map (·.sub)) h₀)
  trap : ∀ (ιe' : InstState) (N : List (NRec P)) (C : List (Option (Activation (E3 P) σ)))
    (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNextD prof P impl (retCfg (extN M₀ ιe' N C) th K segs rest y ys)

/-- **The machine path of the importer's top-level call `k` with floats** from a configuration
between linked calls: a live run to the lowering of the arguments, after which, for every flat
argument list `xs`, a live run reaches the importer's core activation on `xs`. -/
theorem call_atLKV (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ιe ιi : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask)
    (h₀ : σ) (k j a : Nat) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hth : ThreadsOk ιi) (hleave : ιi.mayLeave = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨2⟩)) :
    ∃ (Mℓ : Machine.Config (E3 P) σ) (th : Option ThreadId) (cx : LiftLowerContext (E3 P))
      (f : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
      (rest : List (Activation (E3 P) σ)) (tr₁ : List (Label (E3 P) σ)),
      LRun prof (fun _ _ => false) (DI P impl)
        (invokedAtL cs ιe ιi fs G ST h₀ k j (vs.map toRefVal)) tr₁ Mℓ ∧
      Mℓ.ctl = ⟨th, .prog (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
        (vs.map toRefVal) (paramTypes (liftedFt x)) none >>= f), segs⟩ :: rest ∧
      Mℓ.store.lockdown = false ∧
      ∀ xs : List Flat,
        ∃ M₀ th' K segs' rest' tr₂, LRun prof (fun _ _ => false) (DI P impl)
          { Mℓ with ctl := ⟨th, .prog (f xs), segs⟩ :: rest } tr₂ M₀ ∧
          CallAtLKV prof P impl cs ιe (enterInst ιi ⟨G.threads.length⟩) fs G ST h₀ k j x a
            (vs.map toRefVal) xs M₀ th' K segs' rest' := by
  have hadd : ιi.addThread? ⟨G.threads.length⟩ = some (1, enterInst ιi ⟨G.threads.length⟩) :=
    addThread?_ok hth _
  have hrem : (enterInst ιi ⟨G.threads.length⟩).removeThread? 1 = some (⟨G.threads.length⟩,
      InstState.removeThread 1 (enterInst ιi ⟨G.threads.length⟩)) :=
    removeThread?_enter ιi _
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?pre, ?c₁, ?c₂, ?post⟩
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
    exact .refl _
  · rfl
  · rfl
  · intro xs
    apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · apply LRun.store_congr
        (S' := storeK₃ cs ιe ιi (enterInst ιi ⟨G.threads.length⟩) fs G ST x k (vs.map toRefVal))
        (setTaskState_last (Gt := G.tasks) rfl _)
      mstep
      exact .refl _
    apply CallAtLKV.mk
    · exact start_of rfl rfl rfl rfl
    · rfl
    · refine ⟨fun f ft ιe' N C => ?_, ⟨_, rfl, hleave⟩⟩
      exact calloutEntry_mid (Gt := G.tasks) (Gth := G.threads) rfl rfl rfl rfl f ft {}
    · intro ιe' N C y ys ws hys hws
      apply Exists.intro; apply Exists.intro; apply Exists.intro
      apply And.intro
      · show LRun prof (fun _ _ => false) (DI P impl) (retCfg _ _ _ _ _ y ys) _ _
        unfold retCfg
        apply RunsQ.chunk2 rfl (runs_lift_somePV x.ty hres hmaxr hys hws _ _).choose_spec rfl
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
      exact lrun_lift_trapPV x.ty hres hmaxr hys hn rfl rfl

/-- The configurations running the importer's core activation of call `k` on an admissible
argument list. -/
def QLK (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi' : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h₀ : σ) (k j : Nat)
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (m : Machine.Config (E3 P) σ) : Prop :=
  ∃ vs' th K segs rest, NanAtVList prof x.ty.params vs vs' ∧
    ValTy.checkList x.ty.params vs' = true ∧
    CallAtLKV prof P impl cs ιe ιi' fs G ST h₀ k j x a (vs.map toRefVal)
      (lowerArgs x.ty.params vs') m th K segs rest

/-- **The branching run of the importer's top-level call `k` with floats**: every run from the
host's invocation stays live until it reaches the importer's core activation of an admissible
argument list. -/
theorem call_trunLK (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ιe ιi : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask)
    (h₀ : σ) (k j a : Nat) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hth : ThreadsOk ιi) (hleave : ιi.mayLeave = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨2⟩)) :
    TRun prof (fun _ _ => false) (DI P impl)
      (QLK prof P impl cs ιe (enterInst ιi ⟨G.threads.length⟩) fs G ST h₀ k j x a vs)
      (invokedAtL cs ιe ιi fs G ST h₀ k j (vs.map toRefVal)) := by
  obtain ⟨Mℓ, th, cx, f, segs, rest, tr₁, hpre, hc, hl, hpost⟩ :=
    call_atLKV (impl := impl) prof cs ιe ιi fs G ST h₀ k j a x vs hres hmaxr hth hleave hf
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

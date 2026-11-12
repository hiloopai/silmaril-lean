module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiPath
public import Silmaril.Proofs.Wasm.Component.Reference.FloatVCall

/-!
# An export call between other calls, with floats: the machine path

`call_at_k` (`MultiPath`) with floats at every type, variant payloads included: from the
configuration `readyCfg` left by earlier calls, the call runs live to the lowering of its
arguments, which issues the NaN choices C7; for every admissible argument list `vs'`
(`NanAtVList prof ts vs vs'`) it reaches the core activation on `lowerArgs ts vs'`, and a
resolution reports the canonicalised IR lift (`canonAtVList`) at the next configuration between
calls.

* `CallAtKFV`: `CallAtK` on arbitrary flat arguments `xs`, the host caller record holding the
  original arguments `args`, with canonicalised results;
* `call_at_kFV`: the deterministic parts around the choice;
* `call_trunKV`: every run from the host's invocation stays live until it reaches the core
  activation of some admissible argument list (`QFKV`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat)

variable {P : Profile}

/-- `CallAtK` on the flat arguments `xs`, the host caller record holding `args`, with
canonicalised results. -/
structure CallAtKFV (prof : ProfileKind) (P : Profile)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ι' : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat) (x : SimpleExport)
    (a : (E3 P).FuncAddr) (args : List Silmaril.Wasm.Component.Reference.Val) (xs : List Flat) (M₀ : Machine.Config (E3 P) Unit)
    (th : Option ThreadId) (K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P)))
    (segs : List (Seg (E3 P) Unit)) (rest : List (Activation (E3 P) Unit)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    ResolvesAt prof P (retCfg M₀ th K segs rest y ys)
      (readyCfg y.1 (InstState.removeThread 1 ι') fs
        (nextGarb G x k j a args ((canonAtVList x.ty.results ws).map toRefVal)))
  trap : ∀ (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNext prof P (retCfg M₀ th K segs rest y ys)

/-- **The deterministic parts of call `k` with floats**: a live run to the lowering of the
arguments, after which, for every flat argument list, a live run reaches the core activation. -/
theorem call_at_kFV (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat)
    (a : (E3 P).FuncAddr) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι'))
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ (Mℓ : Machine.Config (E3 P) Unit) (th : Option ThreadId) (cx : LiftLowerContext (E3 P))
      (f : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
      (rest : List (Activation (E3 P) Unit)) (tr₁ : List (Label (E3 P) Unit)),
      LRun prof (refHost P).hr (D P) (invokedAt cs ι fs G k j (vs.map toRefVal)) tr₁ Mℓ ∧
      Mℓ.ctl = ⟨th, .prog (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
        (vs.map toRefVal) (paramTypes (liftedFt x)) none >>= f), segs⟩ :: rest ∧
      Mℓ.store.lockdown = false ∧
      ∀ xs : List Flat,
        ∃ M₀ th' K segs' rest' tr₂, LRun prof (refHost P).hr (D P)
          { Mℓ with ctl := ⟨th, .prog (f xs), segs⟩ :: rest } tr₂ M₀ ∧
          CallAtKFV prof P cs ι' fs G k j x a (vs.map toRefVal) xs M₀ th' K segs' rest' := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?pre, ?c₁, ?c₂, ?post⟩
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
    exact .refl _
  · rfl
  · rfl
  · intro xs
    apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
    apply Exists.intro; apply Exists.intro
    apply And.intro
    · apply LRun.store_congr (S' := store₃ cs ι ι' fs G x k (vs.map toRefVal))
        (setTaskState_last (Gt := G.tasks) rfl _)
      mstep
      exact .refl _
    apply CallAtKFV.mk
    · rfl
    · rfl
    · rfl
    · intro y ys ws hys hws
      apply Exists.intro; apply Exists.intro
      apply And.intro
      · show LRun prof (refHost P).hr (D P) (retCfg _ _ _ _ _ y ys) _ _
        apply LRun.store_congr (S' := store₃ y.1 ι ι' fs G x k (vs.map toRefVal)) rfl
        have hS₃ : (store₃ y.1 ι ι' fs G x k (vs.map toRefVal)).tasks =
            G.tasks ++ [(task₁ x G.callers ⟨G.threads.length⟩).withState .started] := rfl
        unfold retCfg
        apply RunsQ.chunk2 rfl (runs_lift_some_floatV x hres hmaxr hys hws _ _).choose_spec
          rfl
        apply RunsQ.chunk2 rfl
          (runs_return (Gt := G.tasks) (Gc := G.callers) _ hS₃ rfl rfl rfl rfl) rfl
        apply LRun.store_congr (S' := store₄ y.1 ι ι' fs G x k (vs.map toRefVal))
          (by refine setTaskState_last (Gt := G.tasks) ?_ _; rfl)
        apply RunsQ.chunk rfl
          (runs_exit (Gt := G.tasks) (Gth := G.threads)
            (y := ((task₁ x G.callers ⟨G.threads.length⟩).withState .started).withState .resolved)
            (z := (thread₁ G.tasks).withIndex 1) (ι := ι') rfl rfl rfl rfl rfl rfl rfl rfl hrem)
          rfl
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
              insts := [InstState.removeThread 1 ι'] } =
              store₅ y.1 ι ι' fs G x k (vs.map toRefVal) :=
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
      exact lrun_lift_trap_floatV prof x hres hmaxr hys hn rfl rfl

/-- The configurations of call `k` running the core activation of an admissible argument
list. -/
def QFKV (prof : ProfileKind) (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat)
    (x : SimpleExport) (a : Nat) (vs : List Silmaril.Wasm.Component.Val)
    (m : Machine.Config (E3 P) Unit) : Prop :=
  ∃ vs' th K segs rest, NanAtVList prof x.ty.params vs vs' ∧
    ValTy.checkList x.ty.params vs' = true ∧
    CallAtKFV prof P cs ι' fs G k j x a (vs.map toRefVal) (lowerArgs x.ty.params vs') m th K segs
      rest

/-- **The branching run of call `k` with floats**: every run from the host's invocation stays
live until it reaches the core activation of an admissible argument list. -/
theorem call_trunKV (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι ι' : InstState) (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j a : Nat)
    (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hck : ValTy.checkList x.ty.params vs = true)
    (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hrem : ι'.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι'))
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    TRun prof (refHost P).hr (D P) (QFKV prof P cs ι' fs G k j x a vs)
      (invokedAt cs ι fs G k j (vs.map toRefVal)) := by
  obtain ⟨Mℓ, th, cx, f, segs, rest, tr₁, hpre, hc, hl, hpost⟩ :=
    call_at_kFV prof cs ι ι' fs G k j a x vs hres hmaxr hadd hrem hf
  have hc' : Mℓ.ctl = ⟨th, .prog (.op (S := Eff (E3 P) Unit) .get fun s =>
      lowerFlatTypes Limits.spec Quirks.none cx (ptrTypeIn s cx) (toRefVals vs)
        (toClosedList x.ty.params) >>= f), segs⟩ :: rest := by
    rw [hc, paramTypes_liftedFt, lowerFlatValues_float (max := ABI.maxFlatParams) _ _ _ hmax]
    rfl
  have hch := lowerFlatTypesV (E := E3 P) (σ := Unit) Limits.spec Quirks.none cx
    (ptrTypeIn Mℓ.store cx) prof x.ty.params vs hck
  have ht := ChoiceProg.trun (hr := (refHost P).hr) (dispatch := D P) hch
    { Mℓ with ctl := ⟨th, .prog (lowerFlatTypes Limits.spec Quirks.none cx (ptrTypeIn Mℓ.store cx)
      (toRefVals vs) (toClosedList x.ty.params) >>= f), segs⟩ :: rest } f th segs rest rfl hl
  refine TRun.of_lrun hpre (TRun.of_lrun (uniqueStep_get hc' hl) (ht.bind ?_))
  rintro m ⟨out, ⟨vs', hn, hck', rfl⟩, rfl⟩
  obtain ⟨M₀, th', K, segs', rest', tr₂, hl₁, hat⟩ := hpost (lowerArgs x.ty.params vs')
  exact TRun.of_lrun hl₁ (.done ⟨vs', th', K, segs', rest', hn, hck', hat⟩)

end Silmaril.Proofs.Wasm.Component.Reference

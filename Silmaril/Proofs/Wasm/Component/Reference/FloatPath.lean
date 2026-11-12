module

public import Silmaril.Proofs.Wasm.Component.Reference.CallRun
public import Silmaril.Proofs.Wasm.Component.Reference.FloatRun

/-!
# An export call with floats: the machine path

The machine path of `call_at` (`CallPath`), with floats allowed outside variant payloads
(`floatOk`): the prefix up to the lowering of the arguments is the same live run; the lowering
issues the NaN choices C7 and reaches, for every admissible argument list `vs'`
(`NanAtList prof ts vs vs'`), the core activation on `lowerArgs ts vs'`; the lift returns the
canonicalised IR lift (`canonAtList`).

* `CallAtF`: `CallAt` on arbitrary flat arguments `xs`, with canonicalised results;
* `call_trun`: from the host's invocation, every run stays live until it reaches the core
  activation of some admissible argument list (`QF`).
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

namespace TRun

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- Sequencing of branching runs. -/
theorem bind {Q R : Machine.Config E σ → Prop} {m : Machine.Config E σ}
    (h : TRun prof hr dispatch Q m) (hQ : ∀ m, Q m → TRun prof hr dispatch R m) :
    TRun prof hr dispatch R m := by
  induction h with
  | done hq => exact hQ _ hq
  | step hl _ ih => exact .step hl ih

end TRun

/-- `CallAt` on the flat arguments `xs`, with canonicalised results. -/
structure CallAtF (prof : ProfileKind) (P : Profile)
    (cs : (core3P P).Store (CanonHost (core3P P))) (x : SimpleExport) (a : Nat) (xs : List Flat)
    (M₀ : Machine.Config (E3 P) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
    (rest : List (Activation (E3 P) Unit)) : Prop where
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = some ws →
    Resolves prof P (retCfg M₀ th K segs rest y ys)
      ((canonAtList x.ty.results ws).map toRefVal)
  trap : ∀ (y : CoreSt (E3 P)) (ys : List Flat),
    ys.map (·.type) = ValTy.flatList x.ty.results → liftArgs x.ty.results ys = none →
    TrapsNext prof P (retCfg M₀ th K segs rest y ys)

theorem runs_lift_some_float {th : Option ThreadId} (x : SimpleExport)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hff : floatOkList x.ty.results = true) {ys : List Flat}
    (hys : ys.map (·.type) = ValTy.flatList x.ty.results)
    {ws : List Silmaril.Wasm.Component.Val} (hws : liftArgs x.ty.results ys = some ws)
    (cx : LiftLowerContext (E3 P)) (m : Machine.Config (E3 P) Unit) :
    ∃ c, RunsQ (D P) th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList ys)
      (resultTypes (liftedFt x))) m [.tau] ((canonAtList x.ty.results ws).map toRefVal, c) m := by
  have h := liftFlatTypes_liftArgs_float (σ := Unit) (E := E3 P) Limits.spec Quirks.none cx
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

theorem lrun_lift_trap_float {α : Type} {th : Option ThreadId} (prof : ProfileKind)
    (x : SimpleExport) (hres : x.ty.results.length ≤ 1)
    (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hff : floatOkList x.ty.results = true) {ys : List Flat}
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
  have hT := liftFlatTypes_liftArgs_float (σ := Unit) (E := E3 P) Limits.spec Quirks.none cx
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

/-- **The machine path of a call with floats**: a live run to the lowering of the arguments,
after which, for every flat argument list, one step reaches the core activation. -/
theorem call_at_float (prof : ProfileKind) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (j a : Nat) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatOkList x.ty.results = true)
    (hf : fs[j]? = some (.lifted a (liftedFt x) {} ⟨0⟩)) :
    ∃ (Mℓ : Machine.Config (E3 P) Unit) (th : Option ThreadId) (cx : LiftLowerContext (E3 P))
      (f : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
      (rest : List (Activation (E3 P) Unit)) (tr₁ : List (Label (E3 P) Unit)),
      LRun prof (refHost P).hr (D P) (invokedCfg P cs fs j (vs.map toRefVal)) tr₁ Mℓ ∧
      Mℓ.ctl = ⟨th, .prog (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
        (vs.map toRefVal) (paramTypes (liftedFt x)) none >>= f), segs⟩ :: rest ∧
      Mℓ.store.lockdown = false ∧
      ∀ xs : List Flat,
        ∃ M₀ th' K segs' rest', LRun prof (refHost P).hr (D P)
          { Mℓ with ctl := ⟨th, .prog (f xs), segs⟩ :: rest } [.tau] M₀ ∧
          CallAtF prof P cs x a xs M₀ th' K segs' rest' := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?pre, ?c₁, ?c₂, ?post⟩
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
    exact .refl _
  · rfl
  · rfl
  · intro xs
    apply Exists.intro; apply Exists.intro; apply Exists.intro; apply Exists.intro
    apply Exists.intro
    apply And.intro
    · mstep
      exact .refl _
    apply CallAtF.mk
    · rfl
    · rfl
    · rfl
    · show ∀ (y : CoreSt (E3 P)) (ys : List Flat) (ws : List Silmaril.Wasm.Component.Val), _ → _ →
        Resolves prof P (retCfg _ _ _ _ _ y ys) ((canonAtList x.ty.results ws).map toRefVal)
      intro y ys ws hys hws
      apply Exists.intro; apply Exists.intro
      apply And.intro
      · unfold retCfg
        apply RunsQ.chunk2 rfl (runs_lift_some_float x hres hmaxr hffr hys hws _ _).choose_spec
          rfl
        repeat mstep
        exact .refl _
      refine ⟨rfl, rfl, rfl, ?_⟩
      · intro m₁ hs
        cases hs
        apply Exists.intro
        repeat mstep
        exact .refl _
    · intro y ys hys hn
      exact lrun_lift_trap_float prof x hres hmaxr hffr hys hn rfl rfl

end Silmaril.Proofs.Wasm.Component.Reference

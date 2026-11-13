module

public import Silmaril.Proofs.Wasm.Component.Reference.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Reference.CallRun
public import Silmaril.Proofs.Wasm.Component.Reference.CalloutMap

/-!
# Core activations with callouts in the reference machine

A core activation of `core3P P` under the host `answerHostS P g` (a stateful host; `answerHost P g` is its stateless instance), whose callouts are
`canon lower` trampolines of host functions (`LowerAt`), runs in segments: host-free core runs
separated by callouts, each dispatched through `hostCalloutProg` (`runs_callout`) and resumed
with the flat results, or trapping (`traps_callout_lift`, `traps_callout_host`). The machine
configurations of the activation are `coreCfg (extSC B ST CL) …`: the frame `B` with the
subtask and caller records `ST`, `CL` of the callouts so far appended.

* `callout_lrun`, `callout_traps`: one callout, as a live deterministic run of the machine to
  the resumed activation, or to a configuration whose only step is a trap;
* `segs_inv`: every machine run from the activation that ends where a call outcome holds is a
  segmented run (`SegRun`, with the host renaming `trampIdx`) followed by an exit of the core
  phase (returned values or a core trap, `CoreExit`) and the rest of the run, or by a callout
  that traps.
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

/-! ## Callout sites -/

/-- The frame `B` with the subtask and caller records `ST`, `CL` appended. -/
def extSC (B : Machine.Config (E3 P) σ) (ST : List Subtask) (CL : List (Caller (E3 P))) :
    Machine.Config (E3 P) σ :=
  { B with store := { B.store with
      subtasks := B.store.subtasks ++ ST
      callers := B.store.callers ++ CL } }

/-- The frame `B` in host state `s`. -/
abbrev withH (B : Machine.Config (E3 P) σ) (s : σ) : Machine.Config (E3 P) σ := { B with host := s }

theorem extSC_append (B : Machine.Config (E3 P) σ) (ST ST' : List Subtask)
    (CL CL' : List (Caller (E3 P))) :
    extSC (extSC B ST CL) ST' CL' = extSC B (ST ++ ST') (CL ++ CL') := by
  simp only [extSC, List.append_assoc]

/-- A `canon lower` trampoline of a host function at an IR type. -/
structure LowerSite (P : Profile) where
  /-- The lowered component function. -/
  f : FuncId
  /-- The instance of the `canon lower`. -/
  inst : InstId
  /-- Its state. -/
  st : InstState
  /-- The resolved type of the host function value. -/
  ft' : WIT.FuncType Empty RtId
  /-- The host function. -/
  fn : HostFuncId
  /-- The IR type of the import. -/
  p : Silmaril.Wasm.Component.FuncTy

variable {Q : LowerSite P → Prop}

/-- The trampoline. -/
def LowerSite.host (L : LowerSite P) : CanonHost (E3 P) := .lowered L.f (witFt L.p) {} L.inst

/-- The conditions under which a callout to `L` from thread `th` in store `B` with flat
arguments `ys` is answered by `g` as the IR adapter prescribes: the entry check passes, the
instance may leave, `L.f` is the host function `L.fn`, the types are float-free and within the
flat arities of a synchronous lower, the arguments have the flat parameter types, and `g`
answers images of well-typed values. -/
structure LowerSite.Ok (L : LowerSite P) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (B : CStore (E3 P)) (th : Option ThreadId) (ys : List Flat) : Prop where
  entry : calloutEntry B th L.host = none
  inst : ArenaField.insts.get? B L.inst = some L.st
  leave : L.st.mayLeave = true
  func : ArenaField.funcs.get? B L.f = some (.host L.ft' L.fn)
  pff : floatFreeList L.p.params = true
  rff : floatFreeList L.p.results = true
  typed : ys.map (·.type) = ValTy.flatList L.p.params
  maxp : (ValTy.flatList L.p.params).length ≤ 16
  res : L.p.results.length ≤ 1
  maxr : (ValTy.flatList L.p.results).length ≤ 1
  answers : ∀ (s : σ) (ws : List Silmaril.Wasm.Component.Val) rs (s' : σ),
    g s L.fn (ws.map toRefVal) = some (rs, s') →
    ∃ us, rs = us.map toRefVal ∧ ValTy.checkList L.p.results us = true

/-- The callout `h ys` from thread `th` in store `B` is to a `canon lower` site that `g` answers
as the IR prescribes. -/
def LowerAt (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (Q : LowerSite P → Prop)
    (B : CStore (E3 P)) (th : Option ThreadId) (h : CanonHost (E3 P)) (ys : List Flat) : Prop :=
  ∃ L : LowerSite P, Q L ∧ h = L.host ∧ L.Ok g B th ys

/-- The callout is answered in host state `s` with the flat results `flat`, moving to `s'`. -/
def LowerSite.Answers (L : LowerSite P) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (s : σ)
    (ys flat : List Flat) (s' : σ) : Prop :=
  ∃ ws us, liftArgs L.p.params ys = some ws ∧
    g s L.fn (ws.map toRefVal) = some (us.map toRefVal, s') ∧
    ValTy.checkList L.p.results us = true ∧ flat = lowerArgs L.p.results us

/-- The callout traps in host state `s`: its arguments do not lift, or `g` has no answer. -/
def LowerSite.Fails (L : LowerSite P) (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (s : σ)
    (ys : List Flat) : Prop :=
  liftArgs L.p.params ys = none ∨
    ∃ ws, liftArgs L.p.params ys = some ws ∧ g s L.fn (ws.map toRefVal) = none

/-- A callout is answered or fails. -/
theorem LowerSite.answers_or_fails {L : LowerSite P} {B : CStore (E3 P)} {th : Option ThreadId}
    {ys : List Flat} (s : σ) (hok : L.Ok g B th ys) :
    (∃ flat s', L.Answers g s ys flat s') ∨ L.Fails g s ys := by
  cases hl : liftArgs L.p.params ys with
  | none => exact .inr (.inl hl)
  | some ws =>
    cases hg : g s L.fn (ws.map toRefVal) with
    | none => exact .inr (.inr ⟨ws, hl, hg⟩)
    | some rs =>
      obtain ⟨rs, s'⟩ := rs
      obtain ⟨us, rfl, hus⟩ := hok.answers s ws rs s' hg
      exact .inl ⟨_, s', ws, us, hl, hg, hus, rfl⟩

/-- `Ok` depends only on the fields that callouts do not change. -/
theorem LowerSite.Ok.extSC {L : LowerSite P} {B : Machine.Config (E3 P) σ}
    {th : Option ThreadId} {ys : List Flat} (ST : List Subtask) (CL : List (Caller (E3 P)))
    (cs : (E3 P).Store (CanonHost (E3 P))) (hok : L.Ok g B.store th ys) :
    L.Ok g { (Silmaril.Proofs.Wasm.Component.Reference.extSC B ST CL).store with core := cs } th ys :=
  { entry := hok.entry, inst := hok.inst, leave := hok.leave, func := hok.func, pff := hok.pff
    rff := hok.rff, typed := hok.typed, maxp := hok.maxp, res := hok.res, maxr := hok.maxr
    answers := hok.answers }

/-! ## One callout in the machine -/

/-- A callout status is neither running nor stuck. -/
theorem callout_status_ne {s : (E3 P).Store (CanonHost (E3 P))} {t : (E3 P).Thread (CanonHost (E3 P))}
    {h : CanonHost (E3 P)} {ys : List Flat} (hs : (E3 P).status s t = .callout h ys) :
    (E3 P).status s t ≠ .running ∧ (E3 P).status s t ≠ .stuck := by
  rw [hs]
  exact ⟨(fun e => by cases e), (fun e => by cases e)⟩

/-- The callout step of the machine. -/
theorem callout_step {M : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {ct : (E3 P).Thread (CanonHost (E3 P))} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
    {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)}
    {h : CanonHost (E3 P)} {ys : List Flat}
    (hc : M.ctl = ⟨th, .core ct K, segs⟩ :: rest) (hs : (E3 P).status M.store.core ct = .callout h ys) :
    UniqueStep prof (answerHostS P g).hr (DA P g) M .tau
      { M with ctl := ⟨th, .prog (DA P g (.hostCallout h ys)), .core ct K :: segs⟩ :: rest } :=
  .of_core hc (callout_status_ne hs) (.coreCallout hc hs)

/-- **An answered callout** is a live deterministic run of the machine to the activation
resumed with the flat results. -/
theorem callout_lrun {B : Machine.Config (E3 P) σ} {ST : List Subtask}
    {CL : List (Caller (E3 P))} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {x : CoreSt (E3 P)} {L : LowerSite P} {ys flat : List Flat}
    {s' : σ} (hl : B.store.lockdown = false) (hs : (E3 P).status x.1 x.2 = .callout L.host ys)
    (hok : L.Ok g B.store th ys) (ha : L.Answers g B.host ys flat s') :
    ∃ ST' CL' tr, LRun prof (answerHostS P g).hr (DA P g) (coreCfg (extSC B ST CL) th K segs rest x)
      (.tau :: tr)
      (coreCfg (extSC (withH B s') ST' CL') th K segs rest (x.1, (E3 P).resume x.1 x.2 (.values flat))) := by
  obtain ⟨ws, us, hws, hg, hus, rfl⟩ := ha
  let M := coreCfg (extSC B ST CL) th K segs rest x
  let M₁ : Machine.Config (E3 P) σ :=
    { M with ctl := ⟨th, .prog (DA P g (.hostCallout L.host ys)), .core x.2 K :: segs⟩ :: rest }
  have hok' := hok.extSC ST CL x.1
  obtain ⟨pos, tr, hr⟩ := runs_callout (g := g) (th := th) (m := M₁) hok'.entry hok'.inst
    hok'.leave hok'.func hok'.pff hok'.typed hok'.maxp hws hg hok'.res hok'.rff hus hok'.maxr
  have s₁ := callout_step (prof := prof) (g := g) (M := M) rfl hs
  have hc₁ : M₁.ctl =
      ⟨th, .prog (DA P g (.hostCallout L.host ys) >>= Prog.pure), .core x.2 K :: segs⟩ :: rest := by
    show _ :: _ = _ :: _
    rw [Prog.bind_eq, Prog.bind_pure]
  have r₁ := hr.lrun_at (prof := prof) (hr := (answerHostS P g).hr) hl Prog.pure hc₁
  have hst : calloutSt M.store L.inst ys L.p pos (lowerArgs L.p.results us) =
      { (extSC (extSC B ST CL) [{ resolvedSub L.inst (lowerArgs L.p.results us) with lenders := none }]
        [lowerRec ⟨(B.store.subtasks ++ ST).length⟩ L.inst ys L.p pos]).store with core := x.1 } := by
    rw [calloutSt_eq]
    rfl
  let cst := calloutSt M.store L.inst ys L.p pos (lowerArgs L.p.results us)
  have s₂ : UniqueStep prof (answerHostS P g).hr (DA P g)
      { M with host := s', store := cst,
               ctl := ⟨th, .prog (Prog.pure (.flat (lowerArgs L.p.results us))), .core x.2 K :: segs⟩ ::
                 rest } .tau
      { M with host := s', store := cst,
               ctl := ⟨th, .core ((E3 P).resume cst.core x.2 (.values (lowerArgs L.p.results us))) K,
                 segs⟩ :: rest } :=
    .of_prog rfl (fun _ _ e => by cases e) (Step.popCore rfl)
  have heq : ({ M with
        host := s'
        store := cst
        ctl := ⟨th, .core ((E3 P).resume cst.core x.2 (.values (lowerArgs L.p.results us))) K,
          segs⟩ :: rest } : Machine.Config (E3 P) σ) =
      coreCfg (extSC (withH B s') (ST ++ [{ resolvedSub L.inst (lowerArgs L.p.results us) with lenders := none }])
        (CL ++ [lowerRec ⟨(B.store.subtasks ++ ST).length⟩ L.inst ys L.p pos])) th K segs rest
        (x.1, (E3 P).resume x.1 x.2 (.values (lowerArgs L.p.results us))) := by
    show ({ M with host := s', store := cst, ctl := _ } : Machine.Config (E3 P) σ) = _
    rw [show cst = _ from hst, ← extSC_append]
    rfl
  have hl₂ : cst.lockdown = false := by
    rw [show cst = _ from hst]
    exact hl
  exact ⟨_, _, _, .cons ⟨List.cons_ne_nil _ _, hl⟩ s₁ (r₁.trans (.cons ⟨List.cons_ne_nil _ _, hl₂⟩
    (heq ▸ s₂) (.refl _)))⟩

/-- **A failing callout** is a live deterministic run of the machine to a configuration whose
only step is a trap. -/
theorem callout_traps {B : Machine.Config (E3 P) σ} {ST : List Subtask}
    {CL : List (Caller (E3 P))} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {x : CoreSt (E3 P)} {L : LowerSite P} {ys : List Flat}
    (hl : B.store.lockdown = false) (hs : (E3 P).status x.1 x.2 = .callout L.host ys)
    (hok : L.Ok g B.store th ys) (hf : L.Fails g B.host ys) :
    ∃ tr mT r, LRun prof (answerHostS P g).hr (DA P g) (coreCfg (extSC B ST CL) th K segs rest x) tr
      mT ∧ Live mT ∧ UniqueStep prof (answerHostS P g).hr (DA P g) mT (.trap r) (trapCfg mT) := by
  let M := coreCfg (extSC B ST CL) th K segs rest x
  let M₁ : Machine.Config (E3 P) σ :=
    { M with ctl := ⟨th, .prog (DA P g (.hostCallout L.host ys)), .core x.2 K :: segs⟩ :: rest }
  have hok' := hok.extSC ST CL x.1
  have hT : ∃ tr mT, TrapsQ (DA P g) th (DA P g (.hostCallout L.host ys)) M₁ tr mT := by
    rcases hf with hws | ⟨ws, hws, hg⟩
    · exact traps_callout_lift (m := M₁) hok'.entry hok'.inst hok'.leave hok'.func hok'.pff
        hok'.typed hok'.maxp hws
    · exact traps_callout_host (m := M₁) hok'.entry hok'.inst hok'.leave hok'.func hok'.pff
        hok'.typed hok'.maxp hws hg
  obtain ⟨tr, mT, hT⟩ := hT
  have s₁ := callout_step (prof := prof) (g := g) (M := M) rfl hs
  obtain ⟨q, segs', r, hrun, hlive, hu⟩ := hT.lrun (prof := prof) (hr := (answerHostS P g).hr) hl
    Prog.pure (.core x.2 K :: segs) rest
  have e : ({ M₁ with ctl := ⟨th, .prog (DA P g (.hostCallout L.host ys) >>= Prog.pure),
      .core x.2 K :: segs⟩ :: rest } : Machine.Config (E3 P) σ) = M₁ := by
    rw [Prog.bind_eq, Prog.bind_pure]
  rw [e] at hrun
  exact ⟨_, _, r, .cons ⟨List.cons_ne_nil _ _, hl⟩ s₁ hrun, hlive, hu⟩

/-! ## Segmented runs of the core phase -/

open Silmaril.Wasm.SingleThreaded in
/-- A callout status of `core3P P` is the host-call redex of the thread, with flat arguments. -/
theorem status_callout_redex {s : (E3 P).Store (CanonHost (E3 P))} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {h : CanonHost (E3 P)} {ys : List Flat} (hs : (E3 P).status s t = .callout h ys) :
    ∃ E a args, decompose? s (t.config s).code = some (E, a, h, args) ∧ args.mapM toFlat? = some ys := by
  have hs' : flatStatus (Silmaril.Wasm.Game.statusP P s t) = .callout h ys := hs
  unfold flatStatus at hs'
  split at hs'
  · cases hs'
  · split at hs' <;> cases hs'
  · cases hs'
  next h' args' heq =>
    split at hs'
    next fargs hm =>
      obtain ⟨rfl, rfl⟩ : h' = h ∧ fargs = ys := by
        simpa only [Silmaril.Wasm.Component.Engine.Status.callout.injEq] using hs'
      obtain ⟨E, a, hd⟩ := statusP_callout heq
      exact ⟨E, a, args', hd, hm⟩
    next => cases hs'
  · cases hs'

open Silmaril.Wasm.SingleThreaded in
/-- The machine's resumption with flat values is the Core resumption with their values. -/
theorem resume_values (s : (E3 P).Store (CanonHost (E3 P))) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (flat : List Flat) :
    (E3 P).resume s t (.values flat) =
      resumeResult s t (.values (flat.map Silmaril.Wasm.SingleThreaded.ofFlat)) := by
  show resume s t _ = _
  simp only [resume, resumeResult, Silmaril.Wasm.Component.Engine.Core3.toCR, CallResult.toAdmin,
    Silmaril.Wasm.Execution.Core.Result.toAdmin]

/-- A recorded callout: the index of the lowered function, the core arguments and the core
result of the resumption. -/
abbrev CallRec := Nat × List Silmaril.Wasm.Execution.Core.Val × Silmaril.Wasm.Execution.Core.Result

variable (g Q) in
/-- **A segmented run of the core phase answered by the stateful `g`**: host-free core runs
separated by callouts to `canon lower` sites (from thread `th`, in store `B`) that `g` answers in
the current host state, each resumed with the lowered answer. Each callout is recorded with the
host states before and after it, the index of the lowered function, the core arguments and the
core result of the resumption. -/
inductive ASeg (B : CStore (E3 P)) (th : Option ThreadId) :
    σ → CoreSt (E3 P) → List (σ × CallRec × σ) → σ → CoreSt (E3 P) → Prop
  | done {s : σ} {x y : CoreSt (E3 P)} : Relation.ReflTransGen (CoreStep (E3 P)) x y →
      ASeg B th s x [] s y
  | call {s s' s'' : σ} {x y z : CoreSt (E3 P)} {L : LowerSite P} {ys flat : List Flat}
      {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
      {rest : List (σ × CallRec × σ)} :
      Relation.ReflTransGen (CoreStep (E3 P)) x y → (E3 P).status y.1 y.2 = .callout L.host ys →
      Q L → L.Ok g B th ys → L.Answers g s ys flat s' →
      Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, L.host, args) →
      ASeg B th s' (y.1, (E3 P).resume y.1 y.2 (.values flat)) rest s'' z →
      ASeg B th s x ((s, (L.f.idx, args, .values (flat.map Silmaril.Wasm.SingleThreaded.ofFlat)), s') ::
        rest) s'' z

/-- Core steps of the machine are host-free thread steps. -/
theorem coreSteps_internalP {x y : CoreSt (E3 P)}
    (h : Relation.ReflTransGen (CoreStep (E3 P)) x y) :
    Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) x y :=
  Relation.ReflTransGen.mono (fun _ _ h => h.2) _ _ h

/-- **A segmented run answered by `g` is a `SegRun`** (`CalloutMap`) under the renaming
`trampIdx`. -/
theorem ASeg.segRun {B : CStore (E3 P)} {th : Option ThreadId} {s s' : σ} {x z : CoreSt (E3 P)}
    {calls : List (σ × CallRec × σ)}
    (h : ASeg g Q B th s x calls s' z) :
    SegRun trampIdx P x.1 x.2 (calls.map (·.2.1)) z.1 z.2 := by
  induction h with
  | done hy => exact .done (coreSteps_internalP hy)
  | @call s s' s'' x y z L ys flat E a args rest hy _ _ _ _ hd _ ih =>
    have hr : (E3 P).resume y.1 y.2 (.values flat) =
        Silmaril.Wasm.SingleThreaded.resumeResult y.1 y.2
          (.values (flat.map Silmaril.Wasm.SingleThreaded.ofFlat)) := resume_values _ _ _
    rw [hr] at ih
    exact .call (g := trampIdx) (h := L.host) (coreSteps_internalP hy) hd ih

theorem ASeg.trans_done {B : CStore (E3 P)} {th : Option ThreadId} {s s' : σ}
    {x y : CoreSt (E3 P)} {calls : List (σ × CallRec × σ)}
    {z : CoreSt (E3 P)} (hs : ASeg g Q B th s x calls s' y)
    (hz : Relation.ReflTransGen (CoreStep (E3 P)) y z) : ASeg g Q B th s x calls s' z := by
  induction hs with
  | done hy => exact .done (hy.trans hz)
  | call hy hst hq hok ha hd _ ih => exact .call hy hst hq hok ha hd (ih hz)

/-! ## Inversion of the core phase with callouts -/

section Inv

variable {E : CoreEngine} {σ : Type} {hr : HostReady σ} {dispatch : Call E → Canon.P E σ (Ret E)}

/-- **Runs of a core activation**, with the step leaving the core phase. -/
theorem coreCfg_steps_inv' {B : Machine.Config E σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E} {tr : List (Label E σ)} {m' : Machine.Config E σ}
    (h : Steps prof hr dispatch (coreCfg B th K segs rest x) tr m') :
    (∃ y, Relation.ReflTransGen (CoreStep E) x y ∧ m' = coreCfg B th K segs rest y) ∨
      ∃ y pre l m₁ tr₂, Relation.ReflTransGen (CoreStep E) x y ∧ tr = pre ++ l :: tr₂ ∧
        Step prof hr dispatch (coreCfg B th K segs rest y) l m₁ ∧
        CoreExit B th K segs rest y l m₁ ∧ Steps prof hr dispatch m₁ tr₂ m' := by
  generalize hm : coreCfg B th K segs rest x = m at h
  induction h generalizing x with
  | refl => exact .inl ⟨x, .refl, hm.symm⟩
  | cons s r ih =>
    subst hm
    rcases coreCfg_step_inv s with ⟨rfl, y, hy, rfl⟩ | hx
    · rcases ih rfl with ⟨z, hz, e⟩ | ⟨z, pre, l, m₁, tr₂, hz, e, s', hx, r'⟩
      · exact .inl ⟨z, .head hy hz, e⟩
      · exact .inr ⟨z, .core :: pre, l, m₁, tr₂, .head hy hz, by rw [e]; rfl, s', hx, r'⟩
    · exact .inr ⟨x, [], _, _, _, .refl, rfl, s, hx, r⟩

end Inv

/-- The callouts reachable from `x` in host state `s` along runs answered by `g` are
`canon lower` sites answered as the IR prescribes. -/
def CalloutsOk (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (Q : LowerSite P → Prop)
    (B : CStore (E3 P)) (th : Option ThreadId) (s : σ) (x : CoreSt (E3 P)) : Prop :=
  ∀ calls s' y h ys, ASeg g Q B th s x calls s' y → (E3 P).status y.1 y.2 = .callout h ys →
    LowerAt g Q B th h ys

/-- `CalloutsOk` after an answered callout. -/
theorem CalloutsOk.after {B : CStore (E3 P)} {th : Option ThreadId} {s s' : σ}
    {x y : CoreSt (E3 P)}
    {L : LowerSite P} {ys flat : List Flat} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} (hc : CalloutsOk g Q B th s x)
    (hy : Relation.ReflTransGen (CoreStep (E3 P)) x y) (hs : (E3 P).status y.1 y.2 = .callout L.host ys)
    (hq : Q L) (hok : L.Ok g B th ys) (ha : L.Answers g s ys flat s')
    (hd : Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, L.host, args)) :
    CalloutsOk g Q B th s' (y.1, (E3 P).resume y.1 y.2 (.values flat)) :=
  fun _ _ z h ys' hz hs' => hc _ _ z h ys' (.call hy hs hq hok ha hd hz) hs'

/-- How a run of the core phase from host state `s` ends where a call outcome holds. -/
def CoreEnd (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)) (Q : LowerSite P → Prop)
    (B : Machine.Config (E3 P) σ) (s : σ)
    (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P))
    (tr : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ) (out : CallOutcome) : Prop :=
  ∃ calls s' y, ASeg g Q B.store th s x calls s' y ∧
    ((∃ ST CL pre l m₁ tr₂, tr = pre ++ tr₂ ∧
        (∀ h ys, (E3 P).status y.1 y.2 ≠ .callout h ys) ∧
        CoreExit (extSC (withH B s') ST CL) th K segs rest y l m₁ ∧
        Steps prof (answerHostS P g).hr (DA P g) m₁ tr₂ m') ∨
      (∃ (L : LowerSite P) (ys : List Flat) (E : Silmaril.Wasm.SingleThreaded.Ctx) (a : Nat)
          (args : List Silmaril.Wasm.Execution.Core.Val), (E3 P).status y.1 y.2 = .callout L.host ys ∧ Q L ∧
        L.Ok g B.store th ys ∧
        L.Fails g s' ys ∧
        Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, L.host, args) ∧
        out = .trap))

/-- A call outcome holding at a trapped configuration is the trap. -/
theorem holds_trapCfg' {m : Machine.Config (E3 P) σ} {out : CallOutcome} {cid : CallId}
    (ho : out.Holds (answerHostS P g).hr cid (trapCfg m)) : out = .trap := by
  cases out with
  | resolved r => exact absurd ho.2.1 (by simp)
  | trap => rfl
  | deadlock => exact absurd ho.1.2.1 (by simp)

/-- The core phase is live. -/
theorem coreCfg_live (B : Machine.Config (E3 P) σ) (ST : List Subtask) (CL : List (Caller (E3 P)))
    (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ)) (x : CoreSt (E3 P))
    (hl : B.store.lockdown = false) : Live (coreCfg (extSC B ST CL) th K segs rest x) :=
  ⟨List.cons_ne_nil _ _, hl⟩

/-- An exit of the core phase that is not a callout. -/
theorem coreEnd_exit {B : Machine.Config (E3 P) σ} {s : σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {x y : CoreSt (E3 P)} {ST : List Subtask}
    {CL : List (Caller (E3 P))} {pre tr₂ : List (Label (E3 P) σ)} {l : Label (E3 P) σ}
    {m₁ m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hy : Relation.ReflTransGen (CoreStep (E3 P)) x y)
    (hco : ∀ h ys, (E3 P).status y.1 y.2 ≠ .callout h ys)
    (hx : CoreExit (extSC (withH B s) ST CL) th K segs rest y l m₁)
    (r : Steps prof (answerHostS P g).hr (DA P g) m₁ tr₂ m') :
    CoreEnd (prof := prof) g Q B s th K segs rest x (pre ++ l :: tr₂) m' out :=
  ⟨[], s, y, .done hy, .inl ⟨ST, CL, pre ++ [l], l, m₁, tr₂, by simp, hco, hx, r⟩⟩

/-- A failing callout: the run traps. -/
theorem coreEnd_fails {B : Machine.Config (E3 P) σ} {s : σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {x y : CoreSt (E3 P)} {ST : List Subtask}
    {CL : List (Caller (E3 P))} {tr tr' : List (Label (E3 P) σ)}
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome} {L : LowerSite P} {ys : List Flat}
    {cid : CallId} (hl : B.store.lockdown = false) (hy : Relation.ReflTransGen (CoreStep (E3 P)) x y)
    (hs : (E3 P).status y.1 y.2 = .callout L.host ys) (hq : Q L) (hok : L.Ok g B.store th ys)
    (hf : L.Fails g s ys)
    (r : Steps prof (answerHostS P g).hr (DA P g)
      (coreCfg (extSC (withH B s) ST CL) th K segs rest y) tr m')
    (ho : out.Holds (answerHostS P g).hr cid m') :
    CoreEnd (prof := prof) g Q B s th K segs rest x tr' m' out := by
  obtain ⟨E, a, args, hd, -⟩ := status_callout_redex hs
  obtain ⟨tr₃, mT, rT, hrun, hlive, hu⟩ := callout_traps (prof := prof) (B := withH B s) (ST := ST)
    (CL := CL) (K := K) (segs := segs) (rest := rest) hl hs hok hf
  have hout : out = .trap := by
    rcases hrun.inv r with hl' | ⟨tr'', -, r''⟩
    · exact absurd ho (hl'.not_holds _ _)
    cases r'' with
    | refl => exact absurd ho (hlive.not_holds _ _)
    | cons s' r''' =>
      obtain ⟨rfl, rfl⟩ := hu.2 _ _ s'
      rw [steps_of_locked rfl rfl r'''] at ho
      exact holds_trapCfg' ho
  exact ⟨[], s, y, .done hy, .inr ⟨L, ys, E, a, args, hs, hq, hok, hf, hd, hout⟩⟩

/-- An answered callout followed by a segmented end is a segmented end. -/
theorem coreEnd_cons {B : Machine.Config (E3 P) σ} {s s' : σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {x y : CoreSt (E3 P)} {L : LowerSite P}
    {ys flat : List Flat} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} {pre tr'' : List (Label (E3 P) σ)}
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hy : Relation.ReflTransGen (CoreStep (E3 P)) x y) (hs : (E3 P).status y.1 y.2 = .callout L.host ys)
    (hq : Q L) (hok : L.Ok g B.store th ys) (ha : L.Answers g s ys flat s')
    (hd : Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, L.host, args))
    (ih : CoreEnd (prof := prof) g Q B s' th K segs rest (y.1, (E3 P).resume y.1 y.2 (.values flat))
      tr'' m' out) :
    CoreEnd (prof := prof) g Q B s th K segs rest x (pre ++ tr'') m' out := by
  obtain ⟨calls, s'', z, hz, hend⟩ := ih
  refine ⟨_, s'', z, .call hy hs hq hok ha hd hz, ?_⟩
  rcases hend with ⟨ST, CL, pre', l, m₁, tr₂, rfl, hco, hx, r⟩ | hT
  · exact .inl ⟨ST, CL, pre ++ pre', l, m₁, tr₂, by rw [List.append_assoc], hco, hx, r⟩
  · exact .inr hT

/-- **Inversion of the core phase with callouts**: a run of the machine from the activation in
host state `s`, ending where a call outcome holds, is a segmented run answered by `g` followed
by an exit of the core phase and the rest of the run, or by a failing callout (and the outcome
is the trap). -/
theorem segs_inv {B : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {cid : CallId} (hl : B.store.lockdown = false) :
    ∀ (n : Nat) (s : σ) (x : CoreSt (E3 P)) (ST : List Subtask) (CL : List (Caller (E3 P)))
      (tr : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ) (out : CallOutcome),
      tr.length ≤ n → CalloutsOk g Q B.store th s x →
      Steps prof (answerHostS P g).hr (DA P g)
        (coreCfg (extSC (withH B s) ST CL) th K segs rest x) tr m' →
      out.Holds (answerHostS P g).hr cid m' →
      CoreEnd (prof := prof) g Q B s th K segs rest x tr m' out := by
  intro n
  induction n with
  | zero =>
    intro s x ST CL tr m' out hn _ hs ho
    have htr : tr = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst htr
    cases hs
    exact absurd ho ((coreCfg_live (withH B s) ST CL th K segs rest x hl).not_holds _ _)
  | succ n ih =>
    intro s x ST CL tr m' out hn hc hs ho
    rcases coreCfg_steps_inv' hs with ⟨y, -, rfl⟩ | ⟨y, pre, l, m₁, tr₂, hy, rfl, st, hx, r⟩
    · exact absurd ho ((coreCfg_live (withH B s) ST CL th K segs rest y hl).not_holds _ _)
    by_cases hco : ∃ h ys, (E3 P).status y.1 y.2 = .callout h ys
    swap
    · exact coreEnd_exit hy (fun h ys e => hco ⟨h, ys, e⟩) hx r
    obtain ⟨h, ys, hst⟩ := hco
    obtain ⟨L, hq, rfl, hok⟩ : LowerAt g Q B.store th h ys := hc [] s y h ys (.done hy) hst
    have r' : Steps prof (answerHostS P g).hr (DA P g)
        (coreCfg (extSC (withH B s) ST CL) th K segs rest y) (l :: tr₂) m' := .cons st r
    rcases LowerSite.answers_or_fails s hok with ⟨flat, s', ha⟩ | hf
    swap
    · exact coreEnd_fails hl hy hst hq hok hf r' ho
    show CoreEnd g Q B s th K segs rest x (pre ++ l :: tr₂) m' out
    obtain ⟨E, a, args, hd, -⟩ := status_callout_redex hst
    obtain ⟨ST', CL', tr₃, hrun⟩ := callout_lrun (prof := prof) (B := withH B s) (ST := ST)
      (CL := CL) (K := K) (segs := segs) (rest := rest) hl hst hok ha
    rcases hrun.inv r' with hl' | ⟨tr'', e, r''⟩
    · exact absurd ho (hl'.not_holds _ _)
    have htr₂ : tr₂ = tr₃ ++ tr'' := (List.cons.inj e).2
    have hlen : tr''.length ≤ n := by
      have h₁ : (pre ++ l :: tr₂).length ≤ n + 1 := hn
      rw [htr₂] at h₁
      simp only [List.length_append, List.length_cons] at h₁
      omega
    have hend := ih s' _ ST' CL' tr'' m' out hlen (hc.after hy hst hq hok ha hd) r'' ho
    have e' : pre ++ l :: tr₂ = (pre ++ l :: tr₃) ++ tr'' := by
      rw [htr₂, List.append_assoc, List.cons_append]
    rw [e']
    exact coreEnd_cons hy hst hq hok ha hd hend

end Silmaril.Proofs.Wasm.Component.Reference

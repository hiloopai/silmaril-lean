module

public import Silmaril.Proofs.Wasm.Resource.CompToy.Call
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Open.Thms

/-!
# The toy resource component: calls of `get`

`get(borrow<r>) -> u32` lifts the core function `3` (`local.get 0`), at every profile `P`:

* `runs_lower_borrow`: the borrow of a resource the instance implements is lowered to its bare
  representation (REF `lower_borrow`), with no handle; `lower_get_traps`: any other argument
  list makes the lowering trap;
* `getSpec_valid` (the every-run program logic `Silmaril.Wasm.Logic.Hoare`): the core function
  returns its argument and leaves the store unchanged; `get_core`: hence every core run of the
  activation that returns values returns `[i32 w]` in the same store, and none reaches a callout
  (under the host without functions, a host-call redex is stuck, `decompose?_none_of_step`);
* **`toy_get`**: a resolved call of `get` from a configuration between calls `toyCfgX Silmaril.Wasm.Component.Canon.P c ι G`
  (thread table reusable, leftovers `Ok`) was on `[borrow rep]` and ends at
  `toyCfgX Silmaril.Wasm.Component.Canon.P c (removeThread 1 (callIn ι t)) (nextG …)`: same counter, same handles.

New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs

/-! ## Lowering the borrow -/

section Lower

variable {Silmaril.Wasm.Component.Canon.P : Silmaril.Wasm.Numerics.Profile}

theorem lower_borrow_eq (cx : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P)) (vs : List Val) :
    (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams vs (paramTypes ftGet) none :
      Canon.P (E3 Silmaril.Wasm.Component.Canon.P) Unit _) =
      ptrType cx >>= fun p => lowerFlatTypes Limits.spec Quirks.none cx p vs [.borrow ⟨0⟩] := by
  unfold lowerFlatValues
  congr 1
  funext p
  cases p <;> (rw [ite_eq_right_iff.mpr (by intro h; exact absurd h (by decide +kernel))]; rfl)

theorem runs_lower_borrow {th : Option ThreadId} (t : TaskId) (rep : ℕ)
    (m : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit) (hrt : m.store.resourceTypes = [{ impl := some ⟨0⟩ }]) :
    RunsQ (D Silmaril.Wasm.Component.Canon.P) th (lowerFlatValues Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P))
      ABI.maxFlatParams [.borrow rep] (paramTypes ftGet) none) m [.tau, .tau] [i32Flat rep] m := by
  rw [lower_borrow_eq]
  refine .get ?_
  show RunsQ _ _ (lowerFlatTypes Limits.spec Quirks.none _ (ptrTypeIn m.store _) [.borrow rep]
    [.borrow ⟨0⟩]) _ _ _ _
  unfold lowerFlatTypes
  rw [lowerFlatAt.eq_def]
  simp only [lowerBorrow, getResourceType]
  have hget : ArenaField.resourceTypes.get? m.store (⟨0⟩ : RtId) =
      some ({ impl := some ⟨0⟩ } : ResourceType (E3 Silmaril.Wasm.Component.Canon.P)) := by
    simp only [ArenaField.get?, ArenaField.resourceTypes, hrt, Arena.get?_eq_getElem?]
    rfl
  apply RunsQ.of_tr
  · exact RunsQ.bind (RunsQ.bind (RunsQ.bind (runs_getObj ArenaField.resourceTypes _ _ hget)
      (.pure _ _)) (.pure _ _)) (RunsQ.bind (.pure _ _) (.pure _ _))
  · rfl


theorem lowerFlatAt_borrow_other (cx : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P)) (p : Silmaril.Wasm.AddrType)
    (v : Val) (hv : ∀ rep, v ≠ .borrow rep) :
    (lowerFlatAt Limits.spec Quirks.none cx p v (.borrow ⟨0⟩) : Canon.P (E3 Silmaril.Wasm.Component.Canon.P) Unit _) =
      flatMismatch := by
  rw [lowerFlatAt.eq_def]
  cases v <;> first | rfl | exact absurd rfl (hv _)

/-- Any argument list other than one borrow makes the lowering of `get`'s arguments trap. -/
theorem lower_get_traps {th : Option ThreadId} (t : TaskId) (args : List Val)
    (hne : ∀ rep, args ≠ [.borrow rep]) (m : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit)
    (hrt : m.store.resourceTypes = [{ impl := some ⟨0⟩ }]) :
    ∃ trT mT, TrapsQ (D Silmaril.Wasm.Component.Canon.P) th (lowerFlatValues Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P))
      ABI.maxFlatParams args (paramTypes ftGet) none) m trT mT := by
  have h : ∀ p, ∃ trT mT, TrapsQ (D Silmaril.Wasm.Component.Canon.P) th (lowerFlatTypes Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P)) p args
      [.borrow ⟨0⟩]) m trT mT := by
    intro p
    match args, hne with
    | [], _ => exact ⟨_, _, TrapsQ.trap _ (isTrap_trap _)⟩
    | v :: rest, hne =>
      unfold lowerFlatTypes
      by_cases hv : ∃ rep, v = .borrow rep
      · obtain ⟨rep, rfl⟩ := hv
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, rest = x :: xs := by
          cases rest with
          | nil => exact absurd rfl (hne rep)
          | cons x xs => exact ⟨x, xs, rfl⟩
        have hget : ArenaField.resourceTypes.get? m.store (⟨0⟩ : RtId) =
            some ({ impl := some ⟨0⟩ } : ResourceType (E3 Silmaril.Wasm.Component.Canon.P)) := by
          simp only [ArenaField.get?, ArenaField.resourceTypes, hrt, Arena.get?_eq_getElem?]
          rfl
        rw [lowerFlatAt.eq_def]
        simp only [lowerBorrow, getResourceType]
        exact ⟨_, _, TrapsQ.bind (RunsQ.bind (RunsQ.bind
          (runs_getObj ArenaField.resourceTypes _ _ hget) (.pure _ _)) (.pure _ _))
          (TrapsQ.left (TrapsQ.trap _ (isTrap_trap _)))⟩
      · rw [lowerFlatAt_borrow_other _ _ v (fun rep e => hv ⟨rep, e⟩)]
        exact ⟨_, _, TrapsQ.left (TrapsQ.trap _ (isTrap_trap _))⟩
  obtain ⟨trT, mT, hT⟩ := h (ptrTypeIn m.store
    ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P)))
  rw [lower_borrow_eq]
  exact ⟨_, _, TrapsQ.bind (RunsQ.get (RunsQ.pure _ _)) hT⟩

end Lower

/-! ## The core function -/

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable (Silmaril.Wasm.Component.Canon.P : Silmaril.Wasm.Numerics.Profile)

/-- The toy's core store with the counter at `c`. -/
noncomputable abbrev toyCs (c : ℕ) := setCtr Silmaril.Wasm.Component.Canon.P (toyInst Silmaril.Wasm.Component.Canon.P).store.core c

theorem toyCs_funcs (c : ℕ) : (toyCs Silmaril.Wasm.Component.Canon.P c).funcs = (toyInst Silmaril.Wasm.Component.Canon.P).store.core.funcs := rfl

theorem toyCore_get_code : ((toyInst Silmaril.Wasm.Component.Canon.P).store.core.funcs[3]?).map FuncInst.code =
    some (.wasm ⟨⟨0⟩, [], [.localGet ⟨0⟩]⟩) := by kernel_rfl

theorem toyCore_get_type : ((toyInst Silmaril.Wasm.Component.Canon.P).store.core.funcs[3]?).map
    (fun fi => decide (Expand fi.type
      (Silmaril.Wasm.Game.FnType.toComp ⟨[.num (.int .i32)], [.num (.int .i32)]⟩))) =
      some true := by kernel_rfl


/-- The specification of `get` (core function `3`): on one `i32`, it returns its argument and
leaves the store unchanged. -/
def getSpec {H : Type} (fs : List (FuncInst H)) : FSpec H where
  pre s args := s.funcs[3]? = fs[3]? ∧ ∃ w : BitVec 32, args = [.i32 w]
  post s args s' o := s' = s ∧ o = .normal args

variable {Silmaril.Wasm.Component.Canon.P}

theorem getSpec_valid
    {host : HostSemantics (Silmaril.Wasm.Component.Runtime.CanonHost
      (Silmaril.Wasm.Component.Reference.core3P Silmaril.Wasm.Component.Canon.P))} :
    FSpecValid Silmaril.Wasm.Component.Canon.P host 3 (getSpec (toyInst Silmaril.Wasm.Component.Canon.P).store.core.funcs)
  | 0 => fun _ _ _ _ _ _ _ => trivial
  | n + 1 => by
    have hc := toyCore_get_code Silmaril.Wasm.Component.Canon.P
    have ht := toyCore_get_type Silmaril.Wasm.Component.Canon.P
    cases hf : (toyInst Silmaril.Wasm.Component.Canon.P).store.core.funcs[3]? with
    | none => simp [hf] at hc
    | some fi =>
      simp only [hf, Option.map_some, Option.some.injEq, decide_eq_true_eq] at hc ht
      refine FSpecAt.of_body (fi := fi) (fun s args h => h.1.trans hf) hc ht ?_ ?_
      · rintro s args ⟨-, w, rfl⟩
        rfl
      · rintro s args ⟨-, w, rfl⟩ f vs₀
        have hv : (Frame.forCall fi.module [.i32 w] []).local? ⟨0⟩ = some (some (.i32 w)) := by
          rfl
        exact Wp.localGet (m := .part) (us := []) (rest := []) hv
          (HWP.of_vals (vs := [.i32 w]) ⟨rfl, rfl, .inl ⟨[.i32 w], by simp, rfl, rfl⟩⟩) n


open Silmaril.Proofs.Wasm.Component.Reference in
/-- **The core phase of `get`**: every core run of the activation of `get` on `i32 w` that
returns values returns `[i32 w]` in the same store, and no run reaches a callout. -/
theorem get_core {c : ℕ} {w : BitVec 32} {y : CoreSt (E3 Silmaril.Wasm.Component.Canon.P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Silmaril.Wasm.Component.Canon.P))
      (toyCs Silmaril.Wasm.Component.Canon.P c, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 3 [.int .i32 w]) y) :
    (∀ ys, (E3 Silmaril.Wasm.Component.Canon.P).status y.1 y.2 = .returned (.values ys) →
      y.1 = toyCs Silmaril.Wasm.Component.Canon.P c ∧ ys = [.int .i32 w]) ∧
    (∀ h args, (E3 Silmaril.Wasm.Component.Canon.P).status y.1 y.2 ≠ .callout h args) := by
  have hs : Steps Silmaril.Wasm.Component.Canon.P (noHostH _) (invoke (toyCs Silmaril.Wasm.Component.Canon.P c) 3 [.i32 w]) (y.2.config y.1) :=
    internalP_steps (coreSteps_internalP hy)
  have hpre : (getSpec (toyInst Silmaril.Wasm.Component.Canon.P).store.core.funcs).pre (toyCs Silmaril.Wasm.Component.Canon.P c) [.i32 w] := ⟨rfl, w, rfl⟩
  have hv := getSpec_valid (Silmaril.Wasm.Component.Canon.P := Silmaril.Wasm.Component.Canon.P) (host := noHostH _)
  refine ⟨fun ys hst => ?_, fun h args hst => ?_⟩
  · show y.1 = toyCs Silmaril.Wasm.Component.Canon.P c ∧ ys = [.int .i32 w]
    obtain ⟨vs, hc, hm⟩ := status_values hst
    have hs' : Steps Silmaril.Wasm.Component.Canon.P (noHostH _) (invoke (toyCs Silmaril.Wasm.Component.Canon.P c) 3 [.i32 w])
        ⟨y.2.config y.1 |>.store, y.2.config y.1 |>.frame, vals vs⟩ := by
      rw [← hc]
      exact hs
    obtain ⟨h₁, h₂⟩ := hv.invoke_vals hpre hs'
    obtain rfl : vs = [.i32 w] := Outcome.normal.inj h₂
    refine ⟨(Silmaril.Wasm.SingleThreaded.Thread.config_store y.1 y.2).symm.trans h₁, ?_⟩
    have e : [Val.i32 w].mapM Silmaril.Wasm.SingleThreaded.toFlat? = some [.int .i32 w] := rfl
    exact (Option.some.inj (hm.symm.trans e))
  · show False
    obtain ⟨E, a, h', args', hd⟩ := status_callout hst
    have hs₀ : Steps Silmaril.Wasm.Component.Canon.P (noHostH _) ⟨toyCs Silmaril.Wasm.Component.Canon.P c, {}, (invoke (toyCs Silmaril.Wasm.Component.Canon.P c) 3 [.i32 w]).code⟩
        (y.2.config y.1) := hs
    rcases (hv.hwp_invoke hpre).sound hs₀ with
      ⟨c'', hc''⟩ | ⟨o, he, -⟩
    · have hn := Silmaril.Wasm.Logic.Open.decompose?_none_of_step hc''
      have e : (y.2.config y.1).store = y.1 :=
        Silmaril.Wasm.SingleThreaded.Thread.config_store y.1 y.2
      rw [e, hd] at hn
      cases hn
    · exact Silmaril.Wasm.Logic.Open.not_exits_of_redex Silmaril.Wasm.Component.Canon.P hd o he


  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine in
/-- The lift of `get`'s result `[i32 w]`: one `u32`, no store access but the pointer type. -/
theorem runs_lift_get {th : Option ThreadId} (t : TaskId) (w : BitVec 32) :
    ∃ ws cur, ∀ m : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit, RunsQ (D Silmaril.Wasm.Component.Canon.P) th
      (liftFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P))
        ABI.maxFlatResults (.ofList [.int .i32 w]) (resultTypes ftGet)) m [.tau] (ws, cur) m := by
  let x : Silmaril.Wasm.Component.Reference.SimpleExport := ⟨"get", ⟨[], [.u32]⟩, 0⟩
  have h := liftFlatTypes_liftArgs (σ := Unit) (E := E3 Silmaril.Wasm.Component.Canon.P) Limits.spec Quirks.none
    ({ opts := {}, inst := ⟨0⟩, scope := .task t } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P)) .i32
    (ts := x.ty.results) (ys := [.int .i32 w]) rfl rfl
  have hws : Silmaril.Wasm.Component.liftArgs x.ty.results [.int .i32 w] = some [.u32 w] := rfl
  rw [hws] at h
  obtain ⟨cur, hc⟩ := h
  refine ⟨[Silmaril.Wasm.Component.Val.u32 w].map toRefVal, cur, fun m => ?_⟩
  rw [show resultTypes ftGet = resultTypes (liftedFt x) from rfl,
    resultTypes_liftedFt x (by decide),
    show FlatCursor.ofList [.int .i32 w] = ⟨[.int .i32 w], 0⟩ from rfl,
    liftFlatValues_toClosed (max := ABI.maxFlatResults) Limits.spec Quirks.none _ (by decide)]
  refine .get ?_
  show RunsQ _ _ (liftFlatTypes Limits.spec Quirks.none _ (ptrTypeIn m.store _)
    (toClosedList x.ty.results) ⟨[.int .i32 w], 0⟩) _ _ _ _
  rw [ptrTypeIn_none _ _ rfl, hc]
  exact .pure _ _

/-! ## Calls of `get` -/

variable {prof : ProfileKind} {c : ℕ} {ι : InstState} {G : ToyGarb Silmaril.Wasm.Component.Canon.P} {k rep : ℕ}

/-- The lowering of `[borrow rep]` at the lowering point of a call of `get`. -/
theorem get_lowerAt : ∀ m : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit,
    m.store = tStore₃ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep] →
    RunsQ (D Silmaril.Wasm.Component.Canon.P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none
      ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P))
      ABI.maxFlatParams [.borrow rep] (paramTypes ftGet) none) m [.tau, .tau] [i32Flat rep]
      { m with
        store := tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
          (callIn ι ⟨G.threads.length⟩) G.handles } := by
  intro m hm
  obtain ⟨⟩ := m
  dsimp only at hm
  subst hm
  exact runs_lower_borrow _ rep _ rfl

/-- The lift of `[i32 w]` at the return point of a call of `get`. -/
theorem get_liftAt (cs' : (core3P Silmaril.Wasm.Component.Canon.P).Store (CanonHost (core3P Silmaril.Wasm.Component.Canon.P))) (w : BitVec 32) :
    ∃ ws cur, ∀ m : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit,
      m.store = { tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
          (callIn ι ⟨G.threads.length⟩) G.handles with core := cs' } →
      RunsQ (D Silmaril.Wasm.Component.Canon.P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P))
        ABI.maxFlatResults (.ofList [.int .i32 w]) (resultTypes ftGet)) m [.tau] (ws, cur)
        { m with
          store := { tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
              (callIn ι ⟨G.threads.length⟩) G.handles with core := cs' } } := by
  obtain ⟨ws, cur, hlift⟩ := runs_lift_get (Silmaril.Wasm.Component.Canon.P := Silmaril.Wasm.Component.Canon.P) (th := some ⟨G.threads.length⟩)
    ⟨G.tasks.length⟩ w
  refine ⟨ws, cur, fun m hm => ?_⟩
  obtain ⟨⟩ := m
  dsimp only at hm
  subst hm
  exact hlift _

/-- The leftovers after a call of `get` on `[borrow rep]` resolved with `ws`. -/
abbrev getG (G : ToyGarb Silmaril.Wasm.Component.Canon.P) (k rep : ℕ) (ws : List Silmaril.Wasm.Component.Value.Val) :
    ToyGarb Silmaril.Wasm.Component.Canon.P :=
  nextG Silmaril.Wasm.Component.Canon.P G ftGet k 1 3 [.borrow rep] ws G.handles

/-- The instance after a call of `get`. -/
abbrev getI (ι : InstState) (G : ToyGarb Silmaril.Wasm.Component.Canon.P) : InstState :=
  InstState.removeThread 1 (callIn ι ⟨G.threads.length⟩)

/-- **After the core activation of `get` returned**, the resolved outcome is the next
configuration between calls. -/
theorem get_after {M₀ m₁ m' : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 Silmaril.Wasm.Component.Canon.P) Unit (Silmaril.Wasm.Component.Canon.Ret (E3 Silmaril.Wasm.Component.Canon.P))} {segs : List (Seg (E3 Silmaril.Wasm.Component.Canon.P) Unit)}
    {rest : List (Activation (E3 Silmaril.Wasm.Component.Canon.P) Unit)} {y : CoreSt (E3 Silmaril.Wasm.Component.Canon.P)} {ys : List FlatValue}
    {tr : List (Label (E3 Silmaril.Wasm.Component.Canon.P) Unit)} {r : Option (List Silmaril.Wasm.Component.Value.Val)}
    (hG : G.Ok) (hk : ∀ x ∈ G.pending, x.1 ≠ ⟨k⟩)
    (hst : M₀.store = tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
      (callIn ι ⟨G.threads.length⟩) G.handles)
    (hret : ∀ ws cur, (∀ m : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit,
        m.store = { tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
          (callIn ι ⟨G.threads.length⟩) G.handles with core := y.1 } →
        RunsQ (D Silmaril.Wasm.Component.Canon.P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
          ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P))
          ABI.maxFlatResults (.ofList ys) (resultTypes ftGet)) m [.tau] (ws, cur)
          { m with
            store := { tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
                (callIn ι ⟨G.threads.length⟩) G.handles with core := y.1 } }) →
      ∃ trR, LRun prof (refHost Silmaril.Wasm.Component.Canon.P).hr (D Silmaril.Wasm.Component.Canon.P)
        { M₀ with
          store := { tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
              (callIn ι ⟨G.threads.length⟩) G.handles with core := y.1 },
          ctl := ⟨th, .prog (K ys), segs⟩ :: rest } trR (toyCfgX Silmaril.Wasm.Component.Canon.P c (getI ι G) (getG G k rep ws)))
    (hys : ys = [.int .i32 (BitVec.ofNat 32 rep)]) (hm₁ : m₁ = retCfg M₀ th K segs rest y ys)
    (r₃ : Steps prof (refHost Silmaril.Wasm.Component.Canon.P).hr (D Silmaril.Wasm.Component.Canon.P) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : (CallOutcome.resolved r).Holds (refHost Silmaril.Wasm.Component.Canon.P).hr ⟨k⟩ m') :
    ∃ ws, r = some ws ∧ m' = toyCfgX Silmaril.Wasm.Component.Canon.P c (getI ι G) (getG G k rep ws) := by
  obtain ⟨ws, cur, hlift⟩ := get_liftAt (Silmaril.Wasm.Component.Canon.P := Silmaril.Wasm.Component.Canon.P) (c := c) (ι := ι) (G := G) (k := k) (rep := rep)
    y.1 (BitVec.ofNat 32 rep)
  obtain ⟨trR, hR⟩ := hret ws cur (hys ▸ hlift)
  have hR' : LRun prof (refHost Silmaril.Wasm.Component.Canon.P).hr (D Silmaril.Wasm.Component.Canon.P) m₁ trR (toyCfgX Silmaril.Wasm.Component.Canon.P c (getI ι G) (getG G k rep ws)) := by
    rw [hm₁, retCfg, hst]
    exact hR
  have hres : (toyCfgX Silmaril.Wasm.Component.Canon.P c (getI ι G) (getG G k rep ws)).result? ⟨k⟩ = some (some ws) :=
    result?_nextG hG hk c _ ftGet 1 3 [.borrow rep] ws G.handles
  obtain ⟨hm', hr⟩ := resolved_of_lrun hR' rfl hres r₃ hev ho
  exact ⟨ws, hr, hm'⟩

/-- **The core phase of a call of `get` on `[borrow rep]`**: the resolved outcome is the next
configuration between calls. -/
theorem get_from_core {M₀ m' : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 Silmaril.Wasm.Component.Canon.P) Unit (Silmaril.Wasm.Component.Canon.Ret (E3 Silmaril.Wasm.Component.Canon.P))} {segs : List (Seg (E3 Silmaril.Wasm.Component.Canon.P) Unit)}
    {rest : List (Activation (E3 Silmaril.Wasm.Component.Canon.P) Unit)} {tr : List (Label (E3 Silmaril.Wasm.Component.Canon.P) Unit)}
    {r : Option (List Silmaril.Wasm.Component.Value.Val)}
    (hG : G.Ok) (hk : ∀ x ∈ G.pending, x.1 ≠ ⟨k⟩)
    (hst : M₀.store = tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
      (callIn ι ⟨G.threads.length⟩) G.handles)
    (hret : ∀ (cs' : (core3P Silmaril.Wasm.Component.Canon.P).Store (CanonHost (core3P Silmaril.Wasm.Component.Canon.P))) (ys : List FlatValue) ws cur,
      (∀ m : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit,
        m.store = { tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
          (callIn ι ⟨G.threads.length⟩) G.handles with core := cs' } →
        RunsQ (D Silmaril.Wasm.Component.Canon.P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
          ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 Silmaril.Wasm.Component.Canon.P))
          ABI.maxFlatResults (.ofList ys) (resultTypes ftGet)) m [.tau] (ws, cur)
          { m with
            store := { tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
                (callIn ι ⟨G.threads.length⟩) G.handles with core := cs' } }) →
      cs' = toyCs Silmaril.Wasm.Component.Canon.P c →
      ∃ trR, LRun prof (refHost Silmaril.Wasm.Component.Canon.P).hr (D Silmaril.Wasm.Component.Canon.P)
        { M₀ with
          store := { tStore₄ Silmaril.Wasm.Component.Canon.P ftGet c ι (callIn ι ⟨G.threads.length⟩) G k [.borrow rep]
              (callIn ι ⟨G.threads.length⟩) G.handles with core := cs' },
          ctl := ⟨th, .prog (K ys), segs⟩ :: rest } trR (toyCfgX Silmaril.Wasm.Component.Canon.P c (getI ι G) (getG G k rep ws)))
    (r' : Steps prof (refHost Silmaril.Wasm.Component.Canon.P).hr (D Silmaril.Wasm.Component.Canon.P) (coreCfg M₀ th K segs rest
      (toyCs Silmaril.Wasm.Component.Canon.P c, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 3 [i32Flat rep])) tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : (CallOutcome.resolved r).Holds (refHost Silmaril.Wasm.Component.Canon.P).hr ⟨k⟩ m') :
    ∃ ws, r = some ws ∧ m' = toyCfgX Silmaril.Wasm.Component.Canon.P c (getI ι G) (getG G k rep ws) := by
  have hlock : M₀.store.lockdown = false := by rw [hst]; rfl
  rcases coreCfg_steps_inv' r' with ⟨y, -, hm'⟩ | ⟨y, pre, l, m₁, tr₂, hy, e', -, hx, r₃⟩
  · exact absurd (hm' ▸ ho) ((show Live (coreCfg M₀ th K segs rest y) from
      ⟨List.cons_ne_nil _ _, hlock⟩).not_holds _ _)
  have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev := fun ev hm =>
    hev ev (by rw [e']; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm))
  obtain ⟨hval, hnco⟩ := get_core hy
  rcases hx with ⟨ys, hys, -, hm₁⟩ | ⟨-, -, hm₁⟩ | ⟨h', args', hco⟩
  · obtain ⟨hy1, hys'⟩ := hval ys hys
    exact get_after hG hk hst (fun ws cur hl => hret y.1 ys ws cur hl hy1) hys' hm₁ r₃ hev₂ ho
  · subst hm₁
    exact absurd ho (fun hh => absurd (steps_of_locked rfl rfl r₃ ▸ hh).2.1
      (by simp [trapCfg, lockdownSt]))
  · exact (hnco h' args' hco).elim

/-- **A resolved call of `get`** from a configuration between calls (thread table reusable,
leftovers `Ok`) was on one borrow and ends at the next configuration between calls, with the
same counter and handle objects. -/
theorem toy_get {a : List Silmaril.Wasm.Component.Value.Val} {m' : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit}
    {r : Option (List Silmaril.Wasm.Component.Value.Val)} (hth : ThreadsFree ι.threads) (hG : G.Ok)
    (h : Calls prof (refHost Silmaril.Wasm.Component.Canon.P).hr (D Silmaril.Wasm.Component.Canon.P) (toyCfgX Silmaril.Wasm.Component.Canon.P c ι G) ⟨k⟩ ⟨1⟩ a m' (.resolved r)) :
    ∃ rep ws, a = [.borrow rep] ∧ r = some ws ∧ (∀ x ∈ G.pending, x.1 ≠ ⟨k⟩) ∧
      m' = toyCfgX Silmaril.Wasm.Component.Canon.P c (getI ι G) (getG G k rep ws) := by
  obtain ⟨tr, hs, hev, -, ho⟩ := h
  obtain ⟨m₂, s, r₁⟩ := Steps.cons_iff.mp hs
  obtain ⟨hm₂, hk⟩ := toy_invoke_inv s
  have hadd := addThread?_free hth ⟨G.threads.length⟩
  by_cases ha : ∃ rep, a = [.borrow rep]
  · show ∃ rep ws, a = [.borrow rep] ∧ r = some ws ∧ (∀ x ∈ G.pending, x.1 ≠ ⟨k⟩) ∧
      m' = toyCfgX Silmaril.Wasm.Component.Canon.P c (getI ι G) (getG G k rep ws)
    obtain ⟨rep, ha⟩ := ha
    subst ha
    obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, -, hctl, hst, -, hret⟩ := toy_callAt prof ftGet 1 3
      [.borrow rep] [i32Flat rep] c ι _ _ G k G.handles _ rfl rfl hadd get_lowerAt
    rcases hpre.inv (hm₂ ▸ r₁) with hl | ⟨tr', e, r'⟩
    · exact absurd ho (hl.not_holds _ _)
    have hcore : M₀.store.core = toyCs Silmaril.Wasm.Component.Canon.P c := by rw [hst]; rfl
    have hev' : ∀ ev, Label.host ev ∈ tr' → CallHostEvent ⟨k⟩ ev :=
      fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
    obtain ⟨ws, hr, hm'⟩ := get_from_core hG hk hst
      (fun cs' ys ws cur hl hcs => hret cs' _ _ G.handles G.handles ys ws cur [.tau] c hl hcs
        (removeThread?_call _ _)) (hcore ▸ eq_coreCfg hctl ▸ r') hev' ho
    exact ⟨rep, ws, rfl, hr, hk, hm'⟩
  · obtain ⟨trT, mT, rT, hrun, hlive, hu⟩ := toy_callAt_trap prof ftGet 1 3 a c ι _ G k rfl rfl
      hadd (fun m hm => lower_get_traps _ a (fun rep e => ha ⟨rep, e⟩) m (by rw [hm]; rfl))
    exact absurd ho (not_resolved_of_trap hrun hlive hu (hm₂ ▸ r₁))

/-! ## `toyR` and the counter across calls of `get` -/

/-- **Resolved calls of `get` from `toyR`** keep `toyR` and the counter (`CtrVCOn.step` and
`CtrVCOn.mono` for `get`). -/
theorem toyR_get {es : List (String × FuncId)} {m m' : Machine.Config (E3 Silmaril.Wasm.Component.Canon.P) Unit}
    {f : FuncId} {a : List Silmaril.Wasm.Component.Value.Val}
    {r : Option (List Silmaril.Wasm.Component.Value.Val)} (hR : toyR Silmaril.Wasm.Component.Canon.P es m)
    (hf : es.lookup (names getE) = some f)
    (h : Calls prof (refHost Silmaril.Wasm.Component.Canon.P).hr (refHost Silmaril.Wasm.Component.Canon.P).dispatch m ⟨k⟩ f a m' (.resolved r)) :
    toyR Silmaril.Wasm.Component.Canon.P es m' ∧ toyCtrP Silmaril.Wasm.Component.Canon.P m' = toyCtrP Silmaril.Wasm.Component.Canon.P m := by
  obtain ⟨hes, c, ι, G, hm, hc, hι, hth, hTB, hG⟩ := hR
  subst hes hm
  obtain rfl : f = ⟨1⟩ := (Option.some.inj hf).symm
  rw [toyCfg_eq] at h
  obtain ⟨rep, ws, -, -, -, hm'⟩ := toy_get hth hG h
  subst hm'
  refine ⟨toyR_next hc hι hth hTB hG _ ftGet k 1 3 _ ws G.handles, ?_⟩
  rw [← toyCfg_eq, toyCtrP_toyCfg Silmaril.Wasm.Component.Canon.P _ _ hc, toyCtrP_toyCfg Silmaril.Wasm.Component.Canon.P _ _ hc]

end Silmaril.Wasm.Resource.CompToy

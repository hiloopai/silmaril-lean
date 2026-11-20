module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.TaskSpec
public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.CoreCall
public import Silmaril.Wasm.Component.Reference.ListLift.Defs
public import Silmaril.Wasm.Component.Core3G.Defs

/-!
# Accepting runs of `reallocate`

`LiftLowerContext.reallocate` (REF L625-641, `Canon.reallocProg`) of the reference machine over
`core3P P` with the reference host: a fresh `Caller.sub (.realloc args none)` record, the
`may_leave` window, and a nested synchronous `canon lift` of the allocator core function, whose
implicit thread runs above the caller's activation (`Thread.resume`) to its exit; the
synchronous loop then finds the task resolved and makes no choice. On an accepting path:

* `spec_reallocBody`: the allocator's thread body enters, starts (its `on_start` answers the
  four `u32` arguments), lowers them, runs the allocator core function (a typed export of the
  instance, `core_returned`), lifts its single `i32` result as a `u32`, records it through
  `on_resolve`, resolves the task and exits;
* `spec_realloc`: the dispatched `Call.reallocate` returns the recorded pointer `p`, and the
  core stores before and after are related by a Core run of the allocator returning `p`
  (`ReallocRun`, on the renamed stores), with the well-formedness of the instance and the
  memory address types kept, the caller records extended by the resolved record and the task
  view extended by the resolved allocator task.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.AsyncRef (TaskState)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {prof : ProfileKind}

/-- `Spec` over the reference machine of `core3P P`. -/
abbrev SpecR (prof : ProfileKind) (P : Profile) {α : Type} :=
  @Spec (E3 P) Unit prof (refHost P).hr (D P) α

/-- The renamed core store. -/
abbrev cmap (c : (E3 P).Store (CanonHost (E3 P))) : Silmaril.Wasm.Execution.Core.Store Nat :=
  Store.mapH (fun _ => 0) c

/-! ## Core facts -/

/-- Core steps keep the memory address types. -/
theorem coreSteps_memAddrType {x y : CoreSt (E3 P)}
    (h : Relation.ReflTransGen (CoreStep (E3 P)) x y) (a : Nat) (t : Silmaril.Wasm.AddrType)
    (ha : (E3 P).memAddrType? x.1 a = some t) : (E3 P).memAddrType? y.1 a = some t := by
  induction h with
  | refl => exact ha
  | tail _ hs ih =>
    exact (Silmaril.Wasm.Component.Engine.CoreEngine.internal_extends' hs.2).memAddrType a t ih

/-- The typed allocator of the instance `I` at address `ra`. -/
structure AllocAt (I : Silmaril.Wasm.Game.ScalarInstance) (ra : Nat) : Prop where
  noImports : I.imports = []
  idx : ∃ k, ∃ hk : k < I.exports.length,
    I.addrs.getD k 0 = ra ∧ I.exports[k] = reallocFnType

/-! ## Lowering and lifting the allocator's integers -/

/-- The flat `i32` of a `u32` argument. -/
abbrev u32Flat (n : Nat) : FlatValue := lowerFlatInt .u32 (n : Int)

theorem u32Flat_type (n : Nat) : (u32Flat n).type = .int .i32 := rfl

theorem ofFlat_u32Flat (n : Nat) :
    Silmaril.Wasm.SingleThreaded.ofFlat (u32Flat n) =
      Silmaril.Wasm.Execution.Core.Val.i32 (BitVec.ofNat 32 n) := by
  show Silmaril.Wasm.Execution.Core.Val.num ⟨.int .i32, BitVec.ofInt 32 (n : Int)⟩ = _
  rw [BitVec.ofInt_natCast]
  rfl

theorem flat_realloc_params :
    (ABI.flattenTypes .i32 (paramTypes (reallocType .i32))).length = 4 := by
  simp [paramTypes, reallocType, ptrPrim, ABI.flattenTypes, ABI.flatten, ABI.flattenPrimitive]

theorem flat_realloc_results :
    (ABI.flattenTypes .i32 (resultTypes (reallocType .i32))).length = 1 := by
  simp [resultTypes, reallocType, ptrPrim, ABI.flattenTypes, ABI.flatten, ABI.flattenPrimitive]

/-- The lowering of the allocator's four `u32` arguments (no memory option). -/
theorem spec_lowerU32s {th : Option ThreadId} {m : Config (E3 P) Unit}
    (cx : LiftLowerContext (E3 P)) (hcx : cx.opts.memory = none) (a b c d : Nat) :
    SpecR prof P th (lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams
      [.int .u32 (a : Int), .int .u32 (b : Int), .int .u32 (c : Int), .int .u32 (d : Int)]
      (paramTypes (reallocType .i32)) none) m
      (fun xs m' => xs = [u32Flat a, u32Flat b, u32Flat c, u32Flat d] ∧ m' = m) := by
  unfold lowerFlatValues
  refine Spec.bind (Spec.getsCore _) fun p m' ⟨hp, hm⟩ _ _ => ?_
  subst m'
  have hp' : p = .i32 := by
    rw [hp]
    simp [ptrTypeIn, CanonOpts.ptrType, hcx]
  subst hp'
  split
  · next h => exact absurd h (by rw [flat_realloc_params]; decide)
  have e : lowerFlatTypes (σ := Unit) Limits.spec Quirks.none cx .i32
      [.int .u32 (a : Int), .int .u32 (b : Int), .int .u32 (c : Int), .int .u32 (d : Int)]
      (paramTypes (reallocType .i32)) = Prog.pure [u32Flat a, u32Flat b, u32Flat c, u32Flat d] :=
    rfl
  rw [e]
  exact Spec.pure _

/-- The lift of the allocator's single `i32` result as a `u32` (no memory option). -/
theorem spec_liftU32 {th : Option ThreadId} {m : Config (E3 P) Unit}
    (cx : LiftLowerContext (E3 P)) (hcx : cx.opts.memory = none) (b : BitVec 32) :
    SpecR prof P th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList [⟨.int .i32, b⟩]) (resultTypes (reallocType .i32))) m
      (fun r m' => r.1 = [.int .u32 (b.toNat : Int)] ∧ m' = m) := by
  unfold liftFlatValues
  refine Spec.bind (Spec.getsCore _) fun p m' ⟨hp, hm⟩ _ _ => ?_
  subst m'
  have hp' : p = .i32 := by
    rw [hp]
    simp [ptrTypeIn, CanonOpts.ptrType, hcx]
  subst hp'
  split
  · next h => exact absurd h (by rw [flat_realloc_results]; decide)
  have e : liftFlatTypes (σ := Unit) Limits.spec Quirks.none cx .i32
      (resultTypes (reallocType .i32)) (.ofList [⟨.int .i32, b⟩]) =
        Prog.pure ([.int .u32 (liftFlatInt .u32 ⟨.int .i32, b⟩)], ⟨[⟨.int .i32, b⟩], 1⟩) :=
    rfl
  rw [e]
  refine Spec.mono (Spec.pure _) fun r m' ⟨hr, hm⟩ _ _ => ⟨?_, hm⟩
  subst hr
  show [Value.Val.int .u32 ((b.toNat : Int) % 2 ^ 32)] = _
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast b.isLt)]

/-! ## The allocator's caller record -/

/-- The four `u32` arguments `(0, 0, align, n)` of `allocate`. -/
abbrev reallocArgs (align n : Nat) : List Value.Val :=
  [.int .u32 ((0 : Nat) : Int), .int .u32 ((0 : Nat) : Int), .int .u32 (align : Int),
    .int .u32 (n : Int)]

theorem spec_onStart_realloc {th : Option ThreadId} {m : Config (E3 P) Unit} {c : CallerId}
    {args : List Value.Val} {r : Option Value.Val}
    (hc : ArenaField.callers.get? m.store c = some (.sub (.realloc args r))) :
    SpecR prof P th (D P (.onStart c)) m (fun x m' => x = .vals args ∧ m' = m) := by
  show SpecR prof P th (callerOnStart Limits.spec Quirks.none c) m _
  unfold callerOnStart
  refine Spec.bind (Spec.getObj _ _) fun x m₁ ⟨hx, hm⟩ _ _ => ?_
  subst m₁
  rw [hc] at hx
  cases hx
  dsimp only
  unfold onStartProg
  refine Spec.bind (Spec.getObj _ _) fun x m₂ ⟨hx, hm⟩ _ _ => ?_
  subst m₂
  rw [hc] at hx
  cases hx
  exact Spec.pure _

theorem spec_onResolve_realloc {th : Option ThreadId} {m : Config (E3 P) Unit} {c : CallerId}
    {args : List Value.Val} {r : Option Value.Val} (v : Value.Val)
    (hc : ArenaField.callers.get? m.store c = some (.sub (.realloc args r))) :
    SpecR prof P th (D P (.onResolve c (some [v]))) m (fun x m' => x = .unit ∧
      m' = { m with
        store := (ArenaOps.updateSt ArenaField.callers c (LiftSt.recordReallocResult v) m.store) })
      := by
  show SpecR prof P th (callerOnResolve Limits.spec Quirks.none c (some [v])) m _
  unfold callerOnResolve
  refine Spec.bind (Spec.getObj _ _) fun x m₁ ⟨hx, hm⟩ _ _ => ?_
  subst m₁
  rw [hc] at hx
  cases hx
  dsimp only
  unfold onResolveProg
  refine Spec.bind (Spec.getObj _ _) fun x m₂ ⟨hx, hm⟩ _ _ => ?_
  subst m₂
  rw [hc] at hx
  cases hx
  dsimp only
  refine Spec.bind (Spec.modify _ rfl) fun _ m₃ hm _ _ => ?_
  subst m₃
  exact Spec.mono (Spec.pure _) fun x m' ⟨hx, hm⟩ _ _ => ⟨hx, hm⟩

/-! ## The allocator's thread -/

/-- The key of the allocator's task in instance `inst` with caller record `c`. -/
abbrev keyR (inst : InstId) (c : CallerId) :
    WIT.FuncType Empty RtId × CanonOpts (E3 P) × InstId × CallerId :=
  (reallocType .i32, {}, inst, c)

/-- A list of flat values of the single type `i32`. -/
theorem single_i32 {vs : List FlatValue}
    (h : vs.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) =
      [.num (.int .i32)]) : ∃ b : BitVec 32, vs = [⟨.int .i32, b⟩] := by
  match vs, h with
  | [⟨t, b⟩], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true,
      Silmaril.Wasm.Game.ScalarType.num.injEq] at h
    subst h
    exact ⟨b, rfl⟩

/-- What the allocator's run leaves: a Core run of the allocator from the renamed core store
`cmap c` on `(0, 0, align, n)` returning `p` into `cmap c'`, a well-formed instance, the memory
address types of `c`. -/
structure AllocRun (P : Profile) (I : Silmaril.Wasm.Game.ScalarInstance) (ra align n : Nat)
    (c c' : (E3 P).Store (CanonHost (E3 P))) (p : Nat) : Prop where
  run : ReallocRun P ra (cmap c) align n p (cmap c')
  wf : I.WellFormed (cmap c')
  mem : ∀ a t, (E3 P).memAddrType? c a = some t → (E3 P).memAddrType? c' a = some t

theorem getElem?_modify_self {α : Type} (l : List α) (i : Nat) (f : α → α) :
    (l.modify i f)[i]? = l[i]?.map f := by
  simp

theorem modify_modify {α : Type} (l : List α) (i : Nat) (f g : α → α) :
    (l.modify i f).modify i g = l.modify i (g ∘ f) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_modify]
  split
  · cases l[j]? <;> rfl
  · simp

/-- The view of the allocator's task: resolved, other tasks unchanged. -/
abbrev BodyPost (I : Silmaril.Wasm.Game.ScalarInstance) (ra align n : Nat) (T : TaskId)
    (c : CallerId) (M m' : Config (E3 P) Unit) : Prop :=
  ∃ p, AllocRun P I ra align n M.core m'.core p ∧
    m'.store.callers = M.store.callers.modify c.idx
      (LiftSt.recordReallocResult (.int .u32 (p : Int))) ∧
    tview m'.store = (tview M.store).modify T.idx (fun x => (x.1, .resolved))

/-- **The allocator's thread body**: on an accepting path it records the pointer `p` that a
Core run of the allocator returns, resolves the task and exits. -/
theorem spec_reallocBody {I : Silmaril.Wasm.Game.ScalarInstance} {ra align n : Nat}
    (hA : AllocAt I ra) {t : ThreadId} {T : TaskId} {c : CallerId} {inst : InstId}
    {m : Config (E3 P) Unit}
    (hv : (tview m.store)[T.idx]? = some (keyR inst c, .initial))
    (hc : ArenaField.callers.get? m.store c = some (.sub (.realloc (reallocArgs align n) none)))
    (hw : I.WellFormed (cmap m.core)) :
    SpecR prof P (some t) (liftThreadBody Limits.spec Quirks.none T ra) m
      (fun _ m' => BodyPost I ra align n T c m m') := by
  obtain ⟨hI, k, hk, hra, hty⟩ := hA
  subst hra
  unfold liftThreadBody
  refine Spec.bind (spec_enterImplicitThread _ hv rfl) fun b m₁ ⟨hb, hcore₁, hcall₁, hv₁⟩ _ _ => ?_
  subst b
  refine Spec.ite_false rfl ?_
  refine Spec.bind (Spec.getTask _ _) fun tk m₂ ⟨htk, hm⟩ _ _ => ?_
  subst m₂
  have hv₁' : (tview m₁.store)[T.idx]? = some (keyR inst c, .initial) := by rw [hv₁]; exact hv
  obtain ⟨hk', -⟩ := tkey_of_get hv₁' htk
  obtain ⟨ft, opts, inst', caller, st', nb, it, ths⟩ := tk
  simp only [tkey, Prod.mk.injEq] at hk'
  obtain ⟨hft, hopts, hinst, hcaller⟩ := hk'
  subst ft opts inst' caller
  have hc₁ : ArenaField.callers.get? m₁.store c =
      some (.sub (.realloc (reallocArgs align n) none)) := by
    show m₁.store.callers[c.idx]? = _
    rw [hcall₁]
    exact hc
  refine Spec.bind (spec_start hv₁' (spec_onStart_realloc hc₁)) fun args m₃ ⟨hargs, hm⟩ _ _ => ?_
  subst args m₃
  refine Spec.bind (spec_lowerU32s _ rfl _ _ _ _) fun xs m₄ ⟨hxs, hm⟩ _ _ => ?_
  subst xs m₄
  refine Spec.ite_true rfl ?_
  refine Spec.bind (R := fun _ m' => BodyPost I (I.addrs.getD k 0) align n T c m m') ?_
    fun _ m₅ hR _ _ => Spec.mono (Spec.pure _) fun _ m' ⟨_, hm⟩ _ _ => hm ▸ hR
  unfold liftSyncTail
  have hw₁ : I.WellFormed (cmap m₁.core) := by
    show I.WellFormed (Store.mapH _ m₁.core)
    rw [hcore₁]
    exact hw
  have hxs : [u32Flat 0, u32Flat 0, u32Flat align, u32Flat n].map
      (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = I.exports[k].params := by
    rw [hty]
    rfl
  refine Spec.bind (Spec.callCore fun y hy h a =>
    core_no_callout (P := P) hI hw₁ hk hxs y hy h a) fun ys m₅ ⟨y, hy, hst, hm⟩ _ _ => ?_
  subst m₅
  obtain ⟨⟨f', run⟩, htys, hwf⟩ := core_returned (P := P) hI hw₁ hk hxs y hy hst
  rw [hty] at htys
  obtain ⟨b, rfl⟩ := single_i32 htys
  refine Spec.bind (spec_liftU32 _ rfl b) fun r m₆ ⟨hr, hm⟩ _ _ => ?_
  subst m₆
  obtain ⟨res, cur⟩ := r
  dsimp only at hr
  subst hr
  dsimp only
  have hvS : (tview (CStore.setTaskState T .started m₁.store))[T.idx]? =
      some (keyR inst c, .started) := by
    rw [tview_setTaskState, getElem?_modify_self, hv₁']
    rfl
  refine Spec.bind (spec_return (k := keyR inst c) (st := .started) hvS
    (spec_onResolve_realloc (args := reallocArgs align n) (r := none) _ hc₁))
    fun _ m₇ ⟨m₆', hm₆, hm₇⟩ _ _ => ?_
  subst m₆' m₇
  refine Spec.bind (Spec.pure ()) fun _ m₈ ⟨_, hm⟩ _ _ => ?_
  subst m₈
  have hvR : (tview (CStore.setTaskState T .resolved (CStore.setTaskState T .started
      m₁.store)))[T.idx]? = some (keyR inst c, .resolved) := by
    rw [tview_setTaskState, getElem?_modify_self, hvS]
    rfl
  refine Spec.mono (spec_exitImplicitThread (k := keyR inst c) (st := .resolved) hvR rfl)
    fun _ m' ⟨t', i, hm⟩ _ _ => ?_
  subst m'
  have run' : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke (Store.mapH (fun _ => 0) m₁.core)
        (I.addrs.getD k 0)
        ([u32Flat 0, u32Flat 0, u32Flat align, u32Flat n].map Silmaril.Wasm.SingleThreaded.ofFlat))
      ⟨Store.mapH (fun _ => 0) y.1, f',
        Silmaril.Wasm.Execution.Core.vals [Silmaril.Wasm.Execution.Core.Val.i32 b]⟩ := run
  have e1 : [u32Flat 0, u32Flat 0, u32Flat align, u32Flat n].map
      Silmaril.Wasm.SingleThreaded.ofFlat =
        [.i32 0, .i32 0, .i32 (BitVec.ofNat 32 align), .i32 (BitVec.ofNat 32 n)] := by
    simp only [List.map_cons, List.map_nil, ofFlat_u32Flat]
    rfl
  have e2 : BitVec.ofNat 32 b.toNat = b := by simp
  rw [hcore₁, e1] at run'
  refine ⟨b.toNat, ⟨⟨f', ?_, b.isLt⟩, ?_, fun a t₀ ha => ?_⟩, ?_, ?_⟩
  · dsimp only [cmap]
    rw [e2]
    exact run'
  · dsimp only [cmap]
    exact hwf
  · dsimp only
    refine coreSteps_memAddrType hy a t₀ ?_
    show (E3 P).memAddrType? m₁.core a = some t₀
    rw [hcore₁]
    exact ha
  · rw [unregisterThreadSt_callers]
    show m₁.store.callers.modify c.idx _ = _
    rw [hcall₁]
  · rw [tview_unregisterThreadSt, tview_setTaskState]
    show (tview (CStore.setTaskState T .started m₁.store)).modify T.idx _ = _
    rw [tview_setTaskState, hv₁, modify_modify]
    rfl

/-! ## `Thread.resume` and the nested `canon lift` -/

theorem AllocRun.congr {I : Silmaril.Wasm.Game.ScalarInstance} {ra align n p : Nat}
    {c₁ c₂ c₁' c₂' : (E3 P).Store (CanonHost (E3 P))} (hr : AllocRun P I ra align n c₁ c₁' p)
    (h : c₁ = c₂) (h' : c₁' = c₂') : AllocRun P I ra align n c₂ c₂' p := by
  subst h h'
  exact hr

/-- **`Thread.resume`** of a thread whose saved activation is the start of `body`: the body
runs (in a configuration with the same continuations, core store, callers and tasks) and the
thread exits. -/
theorem spec_threadResume {th : Option ThreadId} {t : ThreadId} {m : Config (E3 P) Unit}
    {body : Canon.P (E3 P) Unit (Ret (E3 P))} {R : Ret (E3 P) → Config (E3 P) Unit → Prop}
    (hb : m.cont? t = some ⟨some t, .prog body, []⟩)
    (hbody : ∀ m' : Config (E3 P) Unit, m'.conts = m.conts → m'.core = m.core →
      m'.store.callers = m.store.callers → m'.store.tasks = m.store.tasks →
      SpecR prof P (some t) body
        { m'.setCont t none with store := threadStatusSt t .running m'.store } R) :
    SpecR prof P th (Runtime.Thread.resume t) m
      (fun _ m' => ∃ r m₂, R r m₂ ∧ m₂.store.lockdown = false ∧
        m' = { m₂ with store := threadStatusSt t .exited m₂.store }) := by
  unfold Runtime.Thread.resume
  refine Spec.bind Spec.get fun st m₁ ⟨hst, hm⟩ _ _ => ?_
  subst m₁ st
  split
  · refine Spec.bind (Spec.modify _ rfl) fun _ m₂ hm _ _ => ?_
    subst m₂
    exact Spec.resumeThread hb (hbody _ rfl rfl rfl rfl)
  · refine Spec.bind (Spec.pure ()) fun _ m₂ ⟨_, hm⟩ _ _ => ?_
    subst m₂
    exact Spec.resumeThread hb (hbody _ rfl rfl rfl rfl)

theorem tview_allocTask (s : CStore (E3 P)) (tk : Task (E3 P)) :
    tview (ArenaOps.allocSt ArenaField.tasks tk s) = tview s ++ [(tkey tk, tk.state)] := by
  simp [tview, ArenaOps.allocSt, ArenaField.alloc, ArenaField.tasks, Arena.alloc]

theorem modify_append_singleton {α : Type} (l : List α) (x : α) (f : α → α) :
    (l ++ [x]).modify l.length f = l ++ [f x] := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_modify]
  split
  · next h =>
    subst h
    simp
  · next h =>
    rcases Nat.lt_or_ge j l.length with hj | hj
    · simp [List.getElem?_append_left hj]
    · have hj' : l.length < j := Nat.lt_of_le_of_ne hj h
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      rfl

/-- **The nested `canon lift` of the allocator** on an accepting path: a Core run of the
allocator returns `p`, recorded in the caller record `c`; the allocator's task is resolved. -/
theorem spec_canonLiftRealloc {I : Silmaril.Wasm.Game.ScalarInstance} {ra align n : Nat}
    (hA : AllocAt I ra) {th : Option ThreadId} {c : CallerId} {inst : InstId}
    {m : Config (E3 P) Unit}
    (hc : ArenaField.callers.get? m.store c = some (.sub (.realloc (reallocArgs align n) none)))
    (hw : I.WellFormed (cmap m.core)) :
    SpecR prof P th (canonLift Limits.spec Quirks.none ra (reallocType .i32) {} inst c) m
      (fun _ m' => ∃ p, AllocRun P I ra align n m.core m'.core p ∧
        m'.store.callers = m.store.callers.modify c.idx
          (LiftSt.recordReallocResult (.int .u32 (p : Int))) ∧
        tview m'.store = tview m.store ++ [(keyR inst c, .resolved)]) := by
  unfold canonLift
  refine Spec.bind (Spec.allocObj _ _ rfl) fun T m₁ ⟨hT, hm⟩ _ _ => ?_
  subst m₁ T
  refine Spec.bind (Spec.newThread _) fun t m₂ ⟨ht, hm⟩ _ _ => ?_
  subst m₂
  have hvA : (tview (ArenaOps.allocSt ArenaField.tasks
      ({ ft := reallocType .i32, opts := {}, inst := inst, caller := c } : Task (E3 P))
      m.store))[m.store.tasks.length]? = some (keyR inst c, TaskState.initial) := by
    rw [tview_allocTask]
    have hl : (tview m.store).length = m.store.tasks.length := List.length_map _
    rw [← hl, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hcont := Config.cont?_setCont_self
    { m with store := (ArenaOps.allocSt ArenaField.tasks
      ({ ft := reallocType .i32, opts := {}, inst := inst, caller := c } : Task (E3 P))
      m.store) } t
    (some (threadAct (D P) t (.liftImplicit (TaskId.mk m.store.tasks.length)
      ra)))
  refine Spec.bind (spec_threadResume (body := liftThreadBody Limits.spec Quirks.none
      (TaskId.mk m.store.tasks.length) ra)
      (R := fun _ m'' => BodyPost I ra align n
        (TaskId.mk m.store.tasks.length) c
        { m with store := (ArenaOps.allocSt ArenaField.tasks
          ({ ft := reallocType .i32, opts := {}, inst := inst, caller := c } : Task (E3 P))
          m.store) } m'')
      hcont fun m' hconts hcore hcall htasks => ?_)
    fun _ m₃ ⟨r, m₄, hpost, _, hm⟩ _ _ => ?_
  · have hv' : (tview (threadStatusSt t .running m'.store))[(TaskId.mk
        m.store.tasks.length).idx]? = some (keyR inst c, .initial) := by
      show (tview m'.store)[m.store.tasks.length]? = _
      rw [show tview m'.store = tview (ArenaOps.allocSt ArenaField.tasks
        ({ ft := reallocType .i32, opts := {}, inst := inst, caller := c } : Task (E3 P))
        m.store) from congrArg (List.map _) htasks]
      exact hvA
    have hc' : ArenaField.callers.get? (threadStatusSt t .running m'.store) c =
        some (.sub (.realloc (reallocArgs align n) none)) := by
      show m'.store.callers[c.idx]? = _
      rw [hcall]
      exact hc
    have hw' : I.WellFormed (cmap m'.core) := by
      rw [hcore]
      exact hw
    refine Spec.mono (spec_reallocBody (t := t) (c := c) hA hv' hc' hw')
      fun _ m'' ⟨p, hr, hcl, htv⟩ _ _ =>
        ⟨p, hr.congr hcore rfl, ?_, ?_⟩
    · rw [hcl]
      show m'.store.callers.modify _ _ = _
      rw [hcall]
      rfl
    · rw [htv]
      show (tview m'.store).modify _ _ = _
      rw [show tview m'.store = tview (ArenaOps.allocSt ArenaField.tasks
        ({ ft := reallocType .i32, opts := {}, inst := inst, caller := c } : Task (E3 P))
        m.store) from congrArg (List.map _) htasks]
  subst m₃
  obtain ⟨p, hrun, hcall₄, hv₄⟩ := hpost
  have hv₅ : tview (threadStatusSt t .exited m₄.store) =
      tview m.store ++ [(keyR inst c, .resolved)] := by
    show tview m₄.store = _
    rw [hv₄, tview_allocTask]
    have hl : (tview m.store).length = m.store.tasks.length := List.length_map _
    show (tview m.store ++ [(keyR inst c, TaskState.initial)]).modify m.store.tasks.length _ = _
    rw [← hl, modify_append_singleton]
  have hT : (tview (threadStatusSt t .exited m₄.store))[m.store.tasks.length]? =
      some (keyR inst c, .resolved) := by
    rw [hv₅]
    have hl : (tview m.store).length = m.store.tasks.length := List.length_map _
    rw [← hl, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  refine Spec.bind (R := fun _ m' => m' = { m₄ with store := threadStatusSt t .exited m₄.store })
    (Spec.ite_true rfl ?_) fun _ m₅ hm _ _ => ?_
  · unfold callUnit
    refine Spec.bind (R := fun r m' => r = .unit ∧
        m' = { m₄ with store := threadStatusSt t .exited m₄.store }) (Spec.call ?_)
      fun r m₆ ⟨hr, hm⟩ _ _ => ?_
    · show SpecR prof P th (syncLiftLoopBody (refHost P).hr _) _ _
      unfold syncLiftLoopBody
      refine Spec.bind (Spec.getTask _ _) fun tk m₇ ⟨htk, hm⟩ _ _ => ?_
      subst m₇
      obtain ⟨-, hst⟩ := tkey_of_get hT htk
      split
      · exact Spec.pure _
      · next h => exact absurd hst h
    · subst r m₆
      exact Spec.mono (Spec.pure ()) fun _ m' ⟨_, hm⟩ _ _ => hm
  · subst m₅
    refine Spec.mono (Spec.pure _) fun _ m' ⟨_, hm⟩ _ _ => ?_
    subst m'
    refine ⟨p, hrun.congr rfl rfl, ?_, hv₅⟩
    show m₄.store.callers = _
    rw [hcall₄]
    rfl

/-! ## `reallocate` -/

/-- The resolved caller record of an allocation of `n` bytes aligned to `align` answered with
`p`. -/
abbrev reallocRec (align n p : Nat) : Caller (E3 P) :=
  .sub (.realloc (reallocArgs align n) (some (.int .u32 (p : Int))))

/-- **`reallocate`** (the dispatched `Call.reallocate`) of a lift context with the memory at
address `ma` (32-bit) and the allocator `ra`, on an accepting path: the pointer `p` is the
answer of a Core run of the allocator (`AllocRun`); the caller records gain the resolved
record and the task view the resolved allocator task. -/
theorem spec_realloc {I : Silmaril.Wasm.Game.ScalarInstance} {ra ma : Nat} (hA : AllocAt I ra)
    {th : Option ThreadId} {cx : LiftLowerContext (E3 P)}
    (hmem : cx.opts.memory = some (show (E3 P).MemAddr from ma))
    (hra : cx.opts.realloc = some ra) {m : Config (E3 P) Unit}
    (hm0 : (E3 P).memAddrType? m.core (show (E3 P).MemAddr from ma) = some .i32)
    (hw : I.WellFormed (cmap m.core)) (align n : Nat) :
    SpecR prof P th (D P (.reallocate cx 0 0 align n)) m
      (fun r m' => ∃ p, r = .nat p ∧ AllocRun P I ra align n m.core m'.core p ∧
        m'.store.callers = m.store.callers ++ [reallocRec align n p] ∧
        tview m'.store = tview m.store ++
          [(keyR cx.inst ⟨m.store.callers.length⟩, .resolved)]) := by
  show SpecR prof P th (reallocProg Limits.spec Quirks.none cx 0 0 align n) m _
  unfold reallocProg
  refine Spec.bind (Spec.getsCore _) fun pt m₁ ⟨hpt, hm⟩ _ _ => ?_
  subst m₁
  have hpt' : pt = .i32 := by
    rw [hpt]
    simp only [ptrTypeIn, CanonOpts.ptrType, hmem]
    exact congrArg (Option.getD · _) hm0
  subst hpt'
  refine Spec.bind (Spec.orTrap _ _) fun f m₂ ⟨hf, hm⟩ _ _ => ?_
  subst m₂
  rw [hra] at hf
  cases hf
  refine Spec.bind (Spec.allocObj _ _ rfl) fun c m₃ ⟨hc, hm⟩ _ _ => ?_
  subst m₃ c
  refine Spec.bind Spec.currentThread fun me m₄ ⟨hme, hm⟩ _ _ => ?_
  subst m₄ me
  refine Spec.bind (Spec.getObj _ _) fun ist m₅ ⟨_, hm⟩ _ _ => ?_
  subst m₅
  refine Spec.bind (Spec.trapIf _ _) fun _ m₆ ⟨_, hm⟩ _ _ => ?_
  subst m₆
  refine Spec.bind (Spec.modify _ rfl) fun _ m₇ hm _ _ => ?_
  subst m₇
  refine Spec.bind (Spec.modify _ rfl) fun _ m₈ hm _ _ => ?_
  subst m₈
  have hcl : ArenaField.callers.get? (LiftSt.incNestingSt (ArenaOps.updateSt ArenaField.insts
      cx.inst (LiftSt.setMayLeave false th) (ArenaOps.allocSt ArenaField.callers
        (Caller.sub (.realloc (reallocArgs align n) none)) m.store)))
      (CallerId.mk m.store.callers.length) =
        some (.sub (.realloc (reallocArgs align n) none)) := by
    show (m.store.callers ++ [_])[m.store.callers.length]? = _
    simp
  refine Spec.bind (spec_canonLiftRealloc (inst := cx.inst) hA hcl hw)
    fun _ m₉ ⟨p, hrun, hcall, htv⟩ _ _ => ?_
  refine Spec.bind (Spec.modify _ rfl) fun _ m₁₀ hm _ _ => ?_
  subst m₁₀
  refine Spec.bind (Spec.modify _ rfl) fun _ m₁₁ hm _ _ => ?_
  subst m₁₁
  refine Spec.bind (Spec.getObj _ _) fun x m₁₂ ⟨hx, hm⟩ _ _ => ?_
  subst m₁₂
  have hcall' : m₉.store.callers = m.store.callers ++ [reallocRec align n p] := by
    rw [hcall]
    exact modify_append_singleton _ _ _
  have hx' : x = reallocRec align n p := by
    have h : m₉.store.callers[m.store.callers.length]? = some x := hx
    rw [hcall'] at h
    simp at h
    exact h.symm
  subst hx'
  refine Spec.mono (Spec.pure _) fun r m' ⟨hr, hm⟩ _ _ => ⟨p, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    simp
  · subst m'
    exact hrun.congr rfl rfl
  · subst m'
    exact hcall'
  · subst m'
    exact htv

end Silmaril.Proofs.Wasm.Component.Reference.ListLift

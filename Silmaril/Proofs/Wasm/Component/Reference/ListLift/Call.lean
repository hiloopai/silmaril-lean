module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.Lower
public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.Phases

/-!
# The call phase of `ListComp`

`callPhaseL : CallPhaseL`: an accepting call of export `j` from `afterInst` has the Core-level
explanation of `AcceptSound`. Every accepting run starts with the host's invocation
(`invokedCfg`); from there the machine runs `Store.invoke`, the `canon lift` of the export
(a task and its implicit thread, resumed above the host frame), and in the thread:
`enter_implicit_thread`, `Task.start` (whose `on_start` hands over the arguments), the
lowering of the arguments (`spec_lowerParams`: `LParams` on the renamed core stores, with the
nested allocator runs), the core call of the lifted core function (a typed export of the
instance, `core_returned`), the lift of its `i32` result as a `bool`, and `Task.return_`,
whose `on_resolve` emits the resolution of call `0`. That resolution is final
(`SpecQ.emitResolved`), so an accepting run has resolved call `0` with `[true]`: the core
function returned a nonzero `i32`.
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

/-- `SpecQ` over the reference machine of `core3P P`. -/
abbrev SpecQR (prof : ProfileKind) (P : Profile) (Q : Prop) {α : Type} :=
  @SpecQ (E3 P) Unit prof (refHost P).hr (D P) Q α

namespace SpecQ

variable {E : CoreEngine} {σ : Type} {hr : HostReady σ} {dispatch : Call E → Canon.P E σ (Ret E)}
  {α : Type} {m : Config E σ} {Q : Prop} {th : Option ThreadId} {R : α → Config E σ → Prop}

theorem ite_false {c : Bool} {p q : Canon.P E σ α} (hc : c = false)
    (h : SpecQ prof hr dispatch Q th q m R) :
    SpecQ prof hr dispatch Q th (if c = true then p else q) m R := by
  subst hc
  exact h

theorem ite_true {c : Bool} {p q : Canon.P E σ α} (hc : c = true)
    (h : SpecQ prof hr dispatch Q th p m R) :
    SpecQ prof hr dispatch Q th (if c = true then p else q) m R := by
  subst hc
  exact h

end SpecQ

/-- **`Thread.resume`** towards a goal. -/
theorem specQ_threadResume {Q : Prop} {th : Option ThreadId} {t : ThreadId}
    {m : Config (E3 P) Unit} {body : Canon.P (E3 P) Unit (Ret (E3 P))}
    {R : Ret (E3 P) → Config (E3 P) Unit → Prop}
    (hb : m.cont? t = some ⟨some t, .prog body, []⟩)
    (hbody : ∀ m' : Config (E3 P) Unit, m'.core = m.core →
      m'.store.callers = m.store.callers → m'.store.tasks = m.store.tasks →
      m'.results = m.results →
      SpecQR prof P Q (some t) body
        { m'.setCont t none with store := threadStatusSt t .running m'.store } R) :
    SpecQR prof P Q th (Runtime.Thread.resume t) m
      (fun _ m' => ∃ r m₂, R r m₂ ∧ m₂.store.lockdown = false ∧
        m' = { m₂ with store := threadStatusSt t .exited m₂.store }) := by
  unfold Runtime.Thread.resume
  refine SpecQ.bind (SpecQ.ofSpec Spec.get) fun st m₁ ⟨hst, hm⟩ _ _ => ?_
  subst m₁ st
  split
  · refine SpecQ.bind (SpecQ.ofSpec (Spec.modify _ rfl)) fun _ m₂ hm _ _ => ?_
    subst m₂
    exact SpecQ.resumeThread hb (hbody _ rfl rfl rfl rfl)
  · refine SpecQ.bind (SpecQ.ofSpec (Spec.pure ())) fun _ m₂ ⟨_, hm⟩ _ _ => ?_
    subst m₂
    exact SpecQ.resumeThread hb (hbody _ rfl rfl rfl rfl)

/-! ## The main caller record -/

theorem spec_onStart_host {th : Option ThreadId} {m : Config (E3 P) Unit} {c : CallerId}
    {call : CallId} {args : List Value.Val}
    (hc : ArenaField.callers.get? m.store c = some (.host call args 0)) :
    SpecR prof P th (D P (.onStart c)) m (fun x m' => x = .vals args ∧ m' = m) := by
  show SpecR prof P th (callerOnStart Limits.spec Quirks.none c) m _
  unfold callerOnStart
  refine Spec.bind (Spec.getObj _ _) fun x m₁ ⟨hx, hm⟩ _ _ => ?_
  subst m₁
  rw [hc] at hx
  cases hx
  dsimp only
  refine Spec.bind (Spec.emit _ fun _ => rfl) fun _ m₂ hm _ _ => ?_
  subst m₂
  exact Spec.pure _

/-- The `on_resolve` of the host caller of call `0`: the resolution. -/
theorem specQ_onResolve_host {Q : Prop} {th : Option ThreadId} {m : Config (E3 P) Unit}
    {c : CallerId} {args : List Value.Val} {r : Option (List Value.Val)}
    {R : Ret (E3 P) → Config (E3 P) Unit → Prop}
    (hc : ArenaField.callers.get? m.store c = some (.host ⟨0⟩ args 0))
    (hres : m.result? ⟨0⟩ = none) (hq : r = some [.bool true] → Q) :
    SpecQR prof P Q th (D P (.onResolve c r)) m R := by
  show SpecQR prof P Q th (callerOnResolve Limits.spec Quirks.none c r) m _
  unfold callerOnResolve
  refine SpecQ.bind (SpecQ.ofSpec (Spec.getObj _ _)) fun x m₁ ⟨hx, hm⟩ _ _ => ?_
  subst m₁
  rw [hc] at hx
  cases hx
  dsimp only
  exact SpecQ.bind (R := fun _ _ => False) (SpecQ.emitResolved hres hq) fun _ _ h => h.elim

/-! ## Flat types of the lowered parameters -/

theorem type_of_ofFlat {v : FlatValue} {b : BitVec 32}
    (h : Silmaril.Wasm.SingleThreaded.ofFlat v = .i32 b) : v.type = .int .i32 := by
  obtain ⟨t, bits⟩ := v
  simp only [Silmaril.Wasm.SingleThreaded.ofFlat, Silmaril.Wasm.Execution.Core.Val.i32,
    Silmaril.Wasm.Execution.Core.Val.num.injEq] at h
  exact (Silmaril.Wasm.Execution.Core.NumVal.mk.inj h).1

/-- The lowered parameters have the flat types of the parameter types. -/
theorem lparams_types {ra ma : Nat} {ts : List LTy} {vs : List LVal}
    {s s' : Silmaril.Wasm.Execution.Core.Store Nat} {fl' : List Silmaril.Wasm.Execution.Core.Val}
    (h : LParams P ra ma ts vs s fl' s') :
    ∀ fl : List FlatValue, fl.map Silmaril.Wasm.SingleThreaded.ofFlat = fl' →
      fl.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = ts.flatMap LTy.flat := by
  induction h with
  | nil =>
    intro fl hfl
    cases fl with
    | nil => rfl
    | cons _ _ => cases hfl
  | s32 _ ih =>
    intro fl hfl
    match fl, hfl with
    | v :: fl, hfl =>
      simp only [List.map_cons, List.cons.injEq] at hfl
      simp only [List.map_cons, List.flatMap_cons, LTy.flat, type_of_ofFlat hfl.1,
        ih fl hfl.2]
      rfl
  | list _ _ ih =>
    intro fl hfl
    match fl, hfl with
    | v :: w :: fl, hfl =>
      simp only [List.map_cons, List.cons.injEq] at hfl
      simp only [List.map_cons, List.flatMap_cons, LTy.flat, type_of_ofFlat hfl.1,
        type_of_ofFlat hfl.2.1, ih fl hfl.2.2]
      rfl
    | [_], hfl => simp at hfl

theorem prefix_getElem? {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : Nat} {x : α}
    (hx : l₁[i]? = some x) : l₂[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
  exact hx

/-! ## The lifted export's thread -/

/-- The task record of the call of export `x`. -/
abbrev mainTask (P : Profile) (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance)
    (x : ListExport) : Task (E3 P) :=
  { ft := liftedFtL x, opts := optsL P c I, inst := ⟨0⟩, caller := ⟨0⟩ }

/-- The goal of `CallPhaseL`. -/
def CallGoal (P : Profile) (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance) (x : ListExport)
    (vs : List LVal) : Prop :=
  ∃ (s : Silmaril.Wasm.Execution.Core.Store Nat) (fl : List Silmaril.Wasm.Execution.Core.Val)
    (s' : Silmaril.Wasm.Execution.Core.Store Nat) (f' : Silmaril.Wasm.Execution.Core.Frame)
    (r : BitVec 32),
    LParams P (c.coreAddr I c.reallocName) c.memIdx (x.params.map (·.2)) vs I.store fl s ∧
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke s (c.coreAddr I x.core) fl)
      ⟨s', f', Silmaril.Wasm.Execution.Core.vals [.i32 r]⟩ ∧ r ≠ 0

theorem paramTypes_liftedFtL (x : ListExport) :
    paramTypes (liftedFtL x) = (x.params.map (·.2)).map LTy.toClosed := by
  simp [paramTypes, liftedFtL, List.map_map, Function.comp_def]

/-- The lift of the core function's single `i32` result as a `bool`. -/
theorem spec_liftBool {th : Option ThreadId} {m : Config (E3 P) Unit}
    (cx : LiftLowerContext (E3 P)) (hp : ptrTypeIn ((E3 P).view m.core) cx = .i32) (b : BitVec 32)
    (rt : List (WIT.ClosedType RtId)) (hrt : rt = [.prim .bool]) :
    SpecR prof P th (liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults
      (.ofList [⟨.int .i32, b⟩]) rt) m
      (fun r m' => r.1 = [.bool (liftFlatBool ⟨.int .i32, b⟩)] ∧ m' = m) := by
  subst hrt
  unfold liftFlatValues
  refine Spec.bind (Spec.getsCore _) fun p m' ⟨hp', hm⟩ _ _ => ?_
  subst m'
  rw [hp] at hp'
  subst hp'
  split
  · next h => exact absurd h (by simp [ABI.flattenTypes, ABI.flatten, ABI.flattenPrimitive,
      ABI.maxFlatResults])
  have e : liftFlatTypes (σ := Unit) Limits.spec Quirks.none cx .i32 [.prim .bool]
      (.ofList [⟨.int .i32, b⟩]) =
        Prog.pure ([.bool (liftFlatBool ⟨.int .i32, b⟩)], ⟨[⟨.int .i32, b⟩], 1⟩) :=
    rfl
  rw [e]
  exact Spec.mono (Spec.pure _) fun r m' ⟨hr, hm⟩ _ _ => ⟨by rw [hr], hm⟩

theorem liftFlatBool_true {b : BitVec 32} (h : liftFlatBool ⟨.int .i32, b⟩ = true) : b ≠ 0 := by
  intro hb
  subst hb
  simp [liftFlatBool, convertIntToBool] at h

/-- **The thread of the lifted export** on an accepting path settles `CallGoal`. -/
theorem specQ_mainBody {c : ListComp} {I : Silmaril.Wasm.Game.ScalarInstance} (hi : c.Inst I)
    {j : Nat} (hj : j < c.exports.length) (hflat : 2 * c.exports[j].params.length ≤ 16)
    (htop : ∀ t ∈ c.exports[j].params.map (·.2), t.topLevel = true) {vs : List LVal} (hvs : LTy.checkParams (c.exports[j].params.map (·.2)) vs = true)
    {t₀ : ThreadId} {m : Config (E3 P) Unit}
    (hv : (tview m.store)[0]? = some (tkey (mainTask P c I c.exports[j]), .initial))
    (hcl : ArenaField.callers.get? m.store ⟨0⟩ = some (.host ⟨0⟩ (vs.map LVal.toRef) 0))
    (hres : m.results = []) (hcs : cmap m.core = I.store) (hinv : LInv P I c.memIdx m) :
    SpecQR prof P (CallGoal P c I c.exports[j] vs) (some t₀)
      (liftThreadBody Limits.spec Quirks.none ⟨0⟩ (c.coreAddr I c.exports[j].core)) m
      (fun _ _ => False) := by
  have hA : AllocAt I (c.coreAddr I c.reallocName) := ⟨hi.noImports, hi.realloc⟩
  obtain ⟨k, hk, hka, hkt⟩ := hi.core c.exports[j] (List.getElem_mem hj)
  have hcx : LowerCx P I (c.coreAddr I c.reallocName) c.memIdx
      ({ opts := optsL P c I, inst := ⟨0⟩, scope := .task ⟨0⟩ } : LiftLowerContext (E3 P)) :=
    ⟨rfl, rfl, hA⟩
  unfold liftThreadBody
  refine SpecQ.bind (SpecQ.ofSpec (spec_enterImplicitThread (T := ⟨0⟩) _ hv rfl))
    fun b m₁ ⟨hb, hcore₁, hcall₁, hv₁⟩ _ hres₁ => ?_
  subst b
  refine SpecQ.ite_false rfl ?_
  refine SpecQ.bind (SpecQ.ofSpec (Spec.getTask _ _)) fun tk m₂ ⟨htk, hm⟩ _ _ => ?_
  subst m₂
  have hv₁' : (tview m₁.store)[0]? = some (tkey (mainTask P c I c.exports[j]), .initial) := by
    rw [hv₁]
    exact hv
  obtain ⟨hk', -⟩ := tkey_of_get (T := ⟨0⟩) hv₁' htk
  obtain ⟨ft, opts, inst', caller, st', nb, it, ths⟩ := tk
  simp only [tkey, Prod.mk.injEq] at hk'
  obtain ⟨hft, hopts, hinst, hcaller⟩ := hk'
  subst ft opts inst' caller
  have hcl₁ : ArenaField.callers.get? m₁.store ⟨0⟩ = some (.host ⟨0⟩ (vs.map LVal.toRef) 0) := by
    show m₁.store.callers[0]? = _
    rw [hcall₁]
    exact hcl
  refine SpecQ.bind (SpecQ.ofSpec (spec_start (T := ⟨0⟩) hv₁' (spec_onStart_host hcl₁)))
    fun args m₃ ⟨hargs, hm⟩ _ _ => ?_
  subst args m₃
  have hinv₃ : LInv P I c.memIdx
      { m₁ with store := CStore.setTaskState ⟨0⟩ .started m₁.store } := by
    refine ⟨?_, ?_⟩
    · show (E3 P).memAddrType? m₁.core (memAt P c.memIdx) = some .i32
      rw [hcore₁]
      exact hinv.mem
    · show I.WellFormed (Store.mapH _ m₁.core)
      rw [hcore₁]
      exact hinv.wf
  have hcs₃ : cmap m₁.core = I.store := by
    rw [hcore₁]
    exact hcs
  rw [paramTypes_liftedFtL]
  refine SpecQ.bind (SpecQ.ofSpec (spec_lowerParams hcx _ (by simpa using hflat) htop vs hvs hinv₃))
    fun fl m₄ ⟨hi₄, hg₄, hp₄⟩ _ hres₄ => ?_
  refine SpecQ.ite_true rfl ?_
  refine SpecQ.bind (R := fun _ _ => False) ?_ fun _ _ h => h.elim
  unfold liftSyncTail
  have hxs : fl.map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) = I.exports[k].params := by
    rw [hkt]
    exact lparams_types hp₄ fl rfl
  rw [← hka]
  refine SpecQ.bind (SpecQ.ofSpec (Spec.callCore fun y hy h a =>
    core_no_callout (P := P) hi.noImports hi₄.wf hk hxs y hy h a))
    fun ys m₅ ⟨y, hy, hst, hm⟩ _ hres₅ => ?_
  subst m₅
  obtain ⟨⟨f', run⟩, htys, hwf⟩ := core_returned (P := P) hi.noImports hi₄.wf hk hxs y hy hst
  rw [hkt] at htys
  obtain ⟨r, rfl⟩ := single_i32 htys
  have hi₅ : LInv P I c.memIdx { m₄ with core := y.1 } :=
    ⟨coreSteps_memAddrType hy _ _ hi₄.mem, hwf⟩
  refine SpecQ.bind (SpecQ.ofSpec (spec_liftBool _ ?hp r _ ?hrt))
    fun res m₆ ⟨hr, hm⟩ _ _ => ?_
  case hp => exact ptrTypeIn_i32 hcx hi₅
  case hrt => rfl
  subst m₆
  obtain ⟨res, cur⟩ := res
  dsimp only at hr
  subst hr
  dsimp only
  refine SpecQ.bind (R := fun _ _ => False) ?_ fun _ _ h => h.elim
  unfold Task.return_
  refine SpecQ.bind (SpecQ.ofSpec (Spec.getTask _ _)) fun tk m₇ ⟨htk₇, hm⟩ _ _ => ?_
  subst m₇
  have hv₇ : (tview (CStore.setTaskState ⟨0⟩ .started m₁.store))[0]? =
      some (tkey (mainTask P c I c.exports[j]), .started) := by
    rw [tview_setTaskState]
    show ((tview m₁.store).modify 0 _)[0]? = _
    rw [getElem?_modify_self, hv₁']
    rfl
  have hv₇' : (tview m₄.store)[0]? = some (tkey (mainTask P c I c.exports[j]), .started) :=
    prefix_getElem? hg₄.2 hv₇
  obtain ⟨hk₇, -⟩ := tkey_of_get (T := ⟨0⟩) hv₇' htk₇
  refine SpecQ.bind (SpecQ.ofSpec (Spec.trapIf _ _)) fun _ m₈ ⟨_, hm⟩ _ _ => ?_
  subst m₈
  refine SpecQ.bind (SpecQ.ofSpec (Spec.trapIf _ _)) fun _ m₉ ⟨_, hm⟩ _ _ => ?_
  subst m₉
  unfold callUnit
  have hc₉ : tk.caller = ⟨0⟩ := by
    rw [← (show (tkey tk).2.2.2 = tk.caller from rfl), hk₇]
    rfl
  rw [hc₉]
  refine SpecQ.bind (R := fun _ _ => False) (SpecQ.bind (R := fun _ _ => False)
    (SpecQ.call (specQ_onResolve_host (args := vs.map LVal.toRef) ?hc ?hres ?hq))
      fun _ _ h => h.elim) fun _ _ h => h.elim
  case hc =>
    show m₄.store.callers[0]? = _
    exact prefix_getElem? hg₄.1 (show (CStore.setTaskState ⟨0⟩ .started m₁.store).callers[0]? = _
      from hcl₁)
  case hres =>
    show (m₄.results.find? (·.1 == ⟨0⟩)).map Prod.snd = none
    rw [hres₄, show m₁.results = [] from hres₁.trans hres]
    rfl
  case hq =>
    intro hb
    simp only [Option.some.injEq, List.cons.injEq, Value.Val.bool.injEq, and_true] at hb
    refine ⟨cmap m₄.core, fl.map Silmaril.Wasm.SingleThreaded.ofFlat, Store.mapH (fun _ => 0) y.1,
      f', r, ?_, ?_, liftFlatBool_true hb⟩
    · rw [← hcs₃]
      exact hp₄
    · rw [← hka]
      exact run

/-! ## From the host's invocation -/

/-- The `j`-th lifted function. -/
theorem liftedFuncsL_get? (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance) {j : Nat}
    (hj : j < c.exports.length) :
    (liftedFuncsL P c I)[j]? =
      some (.lifted (c.coreAddr I c.exports[j].core) (liftedFtL c.exports[j]) (optsL P c I)
        ⟨0⟩) := by
  simp only [liftedFuncsL, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]

/-- **The host's invocation** of export `j` from `afterInst` settles `CallGoal`. -/
theorem specQ_invoke {c : ListComp} {I : Silmaril.Wasm.Game.ScalarInstance} (hi : c.Inst I)
    {cs : (core3P P).Store (CanonHost (core3P P))} (hcs : Store.mapH (fun _ => 0) cs = I.store)
    {j : Nat} (hj : j < c.exports.length) (hflat : 2 * c.exports[j].params.length ≤ 16)
    (htop : ∀ t ∈ c.exports[j].params.map (·.2), t.topLevel = true) {vs : List LVal} (hvs : LTy.checkParams (c.exports[j].params.map (·.2)) vs = true) :
    SpecQR prof P (CallGoal P c I c.exports[j] vs) none
      (StepDefs.invokeProg ⟨0⟩ ⟨j⟩ (vs.map LVal.toRef))
      (invokedCfg P cs (liftedFuncsL P c I) j (vs.map LVal.toRef)) (fun _ _ => False) := by
  have hmem : (E3 P).memAddrType? cs (memAt P c.memIdx) = some .i32 := by
    have h := hi.memI32
    rw [← hcs] at h
    exact h
  have hwf : I.WellFormed (Store.mapH (fun _ => 0) cs) := by
    rw [hcs]
    obtain ⟨mt, hmt⟩ := hi.inst
    exact Silmaril.Wasm.Game.IsInstance.ok hmt
  unfold StepDefs.invokeProg
  refine SpecQ.bind (SpecQ.ofSpec (Spec.allocObj _ _ rfl)) fun cl m₁ ⟨hcl, hm⟩ _ _ => ?_
  subst cl m₁
  refine SpecQ.bind (SpecQ.ofSpec (Spec.modify _ rfl)) fun _ m₂ hm _ _ => ?_
  subst m₂
  refine SpecQ.bind (R := fun _ _ => False) (SpecQ.call ?_) fun _ _ h => h.elim
  show SpecQR prof P _ none (funcInstProg Limits.spec Quirks.none HostImpl.none ⟨j⟩ _) _ _
  unfold funcInstProg
  refine SpecQ.bind (SpecQ.ofSpec (Spec.getObj _ _)) fun f m₃ ⟨hf, hm⟩ _ _ => ?_
  subst m₃
  have hf' : (liftedFuncsL P c I)[j]? = some f := hf
  rw [liftedFuncsL_get? c I hj] at hf'
  cases hf'
  dsimp only
  unfold canonLift
  refine SpecQ.bind (SpecQ.ofSpec (Spec.allocObj _ _ rfl)) fun T m₄ ⟨hT, hm⟩ _ _ => ?_
  subst T m₄
  refine SpecQ.bind (SpecQ.ofSpec (Spec.newThread _)) fun t m₅ ⟨ht, hm⟩ _ _ => ?_
  subst m₅
  refine SpecQ.bind (specQ_threadResume (R := fun _ _ => False)
    (Config.cont?_setCont_self _ _ _) fun m' hcore hcall htasks hres' => ?_)
    fun _ _ ⟨_, _, hF, _⟩ _ _ => hF.elim
  show SpecQR prof P _ (some t) (liftThreadBody Limits.spec Quirks.none _ _) _ _
  refine specQ_mainBody hi hj hflat htop hvs ?_ ?_ ?_ ?_ ⟨?_, ?_⟩
  · show (tview m'.store)[0]? = _
    rw [show tview m'.store = _ from congrArg (List.map _) htasks]
    rfl
  · show m'.store.callers[0]? = _
    rw [hcall]
    rfl
  · show m'.results = []
    rw [hres']
    rfl
  · show Store.mapH _ m'.core = _
    rw [hcore]
    exact hcs
  · show (E3 P).memAddrType? m'.core (memAt P c.memIdx) = some .i32
    rw [hcore]
    exact hmem
  · show I.WellFormed (Store.mapH _ m'.core)
    rw [hcore]
    exact hwf

/-- Every accepting run from the host's invocation has the Core-level explanation. -/
theorem acc_invoked {c : ListComp} {I : Silmaril.Wasm.Game.ScalarInstance} (hi : c.Inst I)
    {cs : (core3P P).Store (CanonHost (core3P P))} (hcs : Store.mapH (fun _ => 0) cs = I.store)
    {j : Nat} (hj : j < c.exports.length) (hflat : 2 * c.exports[j].params.length ≤ 16)
    (htop : ∀ t ∈ c.exports[j].params.map (·.2), t.topLevel = true) {vs : List LVal} (hvs : LTy.checkParams (c.exports[j].params.map (·.2)) vs = true) :
    Acc prof (refHost P).hr (D P) (invokedCfg P cs (liftedFuncsL P c I) j (vs.map LVal.toRef))
      (CallGoal P c I c.exports[j] vs) := by
  have h := specQ_invoke (prof := prof) hi hcs hj hflat htop hvs rfl Prog.pure [] []
    fun _ _ hF => hF.elim
  rw [Prog.bind_eq, Prog.bind_pure] at h
  exact h

/-- **The call phase of `ListComp`.** -/
theorem callPhaseL : CallPhaseL := by
  intro P prof c I hc hi cs hcs j hj vs hvs hb
  have hflat := hc.flat _ (List.getElem_mem hj)
  have htop : ∀ t ∈ c.exports[j].params.map (·.2), t.topLevel = true := fun t ht => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
    exact hc.top _ (List.getElem_mem hj) p hp
  rcases hb with ⟨m', out, ⟨tr, hs, -, -, ho⟩, hout⟩ | ⟨h, -⟩
  · cases out with
    | resolved r =>
      simp only [Outcome.ofCall, Outcome.returns.injEq] at hout
      subst hout
      obtain ⟨m₂, s, r'⟩ := Steps.cons_iff.mp hs
      rw [invoke_inv s] at r'
      exact acc_invoked hi hcs hj hflat htop hvs _ _ r' ho
    | trap => cases hout
    | deadlock => cases hout
  · cases h

/-- Accepting calls have a Core-level explanation, given the instantiation phase. -/
theorem acceptSound_of_instPhase (hA : InstPhaseL) (c : ListComp) : AcceptSound c :=
  acceptSound_of_phases hA callPhaseL c

end Silmaril.Proofs.Wasm.Component.Reference.ListLift

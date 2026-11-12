module

public import Silmaril.Proofs.Wasm.Component.Reference.StartIRun
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The instantiation phase of a component with imports and a start function

Under the answering host `answerHostS P g`:

* `start_pathI`: the deterministic parts of the instantiation: a run without observations from
  the instantiation host event to the core activation of the start function, and from its return
  (no values) to `afterStartCfgI`, observing the instance and `exportMapIS c`;
* `start_no_callI`: under `ImpModule.StartNoCall`, the start function's core activation never
  stops at a callout;
* `start_returnsI`, `start_failsI`: the core outcomes as Core 3.0 runs of the start phase of the
  instance (`StartsTo`, `ImpModule.StartFails`), with the store well formed after the start
  function (typing of the start function as an extra export answered by the silent
  environment);
* `instBehaviours_startI`: every instantiation result is an instance at `afterStartCfgI` of a
  core store the start function returns at, a trap where it traps, or divergence.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)

variable {Pf : Profile} {σ : Type}
  {g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
    Option (List Silmaril.Wasm.Component.Value.Val × σ)}
  {prof : ProfileKind}

/-! ## The configuration after the start function -/

/-- The leftovers of the start function, under the answering host. -/
def startGarbA (P : Profile)
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ)) (a : Nat) : Garb P σ where
  tasks := [task₂ startEx [] ⟨0⟩]
  threads := [{ (thread₁ ([] : List (Runtime.Task (E3 P)))).withIndex 1 with status := .exited }]
  callers := [.sub .start]
  conts := Config.setSlot (Config.setSlot [] 0
    (some (threadAct (DA P g) ⟨0⟩ (.liftImplicit ⟨0⟩ a)))) 0 none
  pending := []
  results := []
  cancels := []

/-- The component functions after instantiation with a start function: the host functions of
the imports, the lifted start function, the lifted exports. -/
def fsS (P : Profile) (addr : Nat → Nat) (c : SimpleI) (a : Nat) : List (CFuncInst (core3P P)) :=
  hostList 0 c.imports ++ [startFn a] ++ liftedList addr ⟨0⟩ c.exports

/-- **The configuration after instantiation with a start function**: between calls, with the
start function's leftovers and the functions `fsS`. -/
def afterStartCfgI (P : Profile)
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ))
    (cs' : (core3P P).Store (CanonHost (core3P P))) (a : Nat) (addr : Nat → Nat) (c : SimpleI)
    (h₀ : σ) : Machine.Config (core3P P) σ :=
  readyCfgI cs' instAfterStart (fsS P addr c a) (startGarbA P g a) [] h₀

/-- The configuration after the instantiation host event. -/
def instStartIS (c : SimpleI) (h₀ : σ) : Machine.Config (core3P Pf) σ :=
  { (initIS c h₀ : Machine.Config (core3P Pf) σ) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg c.toRef (importArgs c.imports)))] }

/-- The core activation of the start function in the instantiation, with the deterministic runs
around it. -/
structure StartPathI (prof : ProfileKind) (Pf : Profile)
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ)) (c : SimpleI) (h₀ : σ)
    (cs : (core3P Pf).Store (CanonHost (core3P Pf))) (a : Nat) (addr : Nat → Nat)
    (M₀ : Machine.Config (core3P Pf) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (core3P Pf) σ (Ret (core3P Pf)))
    (segs : List (Seg (core3P Pf) σ)) (rest : List (Activation (core3P Pf) σ)) : Prop where
  pre : ∃ tr, LRun prof (answerHostS Pf g).hr (DA Pf g) (instStartIS c h₀) tr M₀ ∧
    traceObs tr = []
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ y : CoreSt (E3 Pf), ∃ tr, LRun prof (answerHostS Pf g).hr (DA Pf g)
    (retCfg M₀ th K segs rest y []) tr (afterStartCfgI Pf g y.1 a addr c h₀) ∧
    traceObs tr = [instantiatedObs ⟨0⟩ (exportMapIS c)]

/-- **The deterministic parts of the instantiation with a start function and imports.** -/
theorem start_pathI {c : SimpleI} (hc : c.Good) (hi : c.InstS) (har : c.Arity)
    {I : Silmaril.Wasm.Game.ScalarInstance} {cs : (core3P Pf).Store (CanonHost (core3P Pf))}
    {ci : (core3P Pf).Inst} {a : Nat} (hF : CoreFactsIS c I cs ci (some a)) (h₀ : σ) :
    ∃ M₀ th K segs rest,
      StartPathI prof Pf g c h₀ cs a (fun k => I.addrs.getD k 0) M₀ th K segs rest := by
  obtain ⟨tr₁, Post, R, ho₁, hP⟩ := instIS_reaches (prof := prof) (g := g) hc hi har hF h₀
  obtain ⟨K, D₁, hK⟩ := R (fun _ => pure .unit) [] [] rfl
  obtain ⟨M₀, th, Kc, segs, rest, tr₂, D₂, ho₂, hA⟩ := start_atA (g := g) prof
    { (holeCfgI c h₀ cs : Machine.Config (core3P Pf) σ) with
      ctl := [⟨none, .prog (runStart ⟨0⟩ a >>= K), []⟩] } a {} (enterInst {} ⟨0⟩) (th := none)
    (K := K) (segs := []) (rest := []) rfl rfl rfl (addThread?_ok (.inl rfl) _)
    (removeThread?_enter _ _)
  refine ⟨M₀, th, Kc, segs, rest, ⟨_, D₁.trans D₂, by simp [ho₁, ho₂]⟩, hA.ctl, hA.core,
    hA.lock, fun y => ?_⟩
  obtain ⟨tr₃, D₃, ho₃⟩ := hA.ret y
  obtain ⟨tr₄, hP₄, ho₄⟩ := hP (startedCfgA g { (holeCfgI c h₀ cs : Machine.Config (core3P Pf) σ) with
      ctl := [⟨none, .prog (runStart ⟨0⟩ a >>= K), []⟩] } a (enterInst {} ⟨0⟩) y.1)
    (by
      show (hostList 0 c.imports ++ [startFn a]).length = _
      rw [List.length_append, hostList_length]
      rfl)
  obtain ⟨D₄, hl₄⟩ := hK _ _ _ _ hP₄ rfl
  have s : UniqueStep prof (answerHostS Pf g).hr (DA Pf g)
      { endCfgI (startedCfgA g { (holeCfgI c h₀ cs : Machine.Config (core3P Pf) σ) with
          ctl := [⟨none, .prog (runStart ⟨0⟩ a >>= K), []⟩] } a (enterInst {} ⟨0⟩) y.1)
          (fun k => I.addrs.getD k 0) c with
        ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterStartCfgI Pf g y.1 a (fun k => I.addrs.getD k 0) c h₀) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  refine ⟨_, D₃.trans (D₄.trans (.cons ⟨List.cons_ne_nil _ _, hl₄⟩ s (.refl _))), ?_⟩
  simp only [traceObs_append, ho₃, ho₄]
  rfl

/-! ## Typing of the start function with imports -/

section PlusStart

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game

variable {I : ScalarInstance} {s : Store Nat} {a : Nat}

/-- Host-free runs are runs for any host. -/
theorem steps_of_noHostI {P : Profile} {H : Type} (host : HostSemantics H) {c c' : Silmaril.Wasm.Execution.Core.Config H}
    (h : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost c c') : Silmaril.Wasm.Execution.Core.Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact .tail ih (Step.of_noHost host hst)

/-- **Typed start results**, host-free, for an instance with imports: a result of the start
function is `values []`, a trap or an exception. -/
theorem start_resultI {P : Profile} (hw : I.WellFormed s) (ha : StartTyped s a) {c' : Silmaril.Wasm.Execution.Core.Config Nat}
    {r : Result} (run : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s a []) c')
    (final : c'.code = r.toAdmin) : r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x := by
  have run' : Silmaril.Wasm.Execution.Core.Steps P (hostOf (plusStartI I a).imports (Env.silent _))
      (invoke s ((plusStartI I a).addr (startOpI I a).1) (startOpI I a).2.1) c' :=
    steps_of_noHostI _ run
  obtain ⟨w, hw', -⟩ := ScalarInstance.answer_of_run (plusStartI_wellFormed hw ha)
    (throwsBelow_silent _ _) run' final
  exact result_of_startTypeI hw'

/-- **The start function keeps the instance well formed**, host-free, with imports. -/
theorem start_wellFormedI {P : Profile} (hw : I.WellFormed s) (ha : StartTyped s a) {s' : Store Nat}
    {t' : Silmaril.Wasm.SingleThreaded.Thread} {r : Result}
    (run : Reach P (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) (s', t'))
    (final : ResultAt s' t' r) : I.WellFormed s' := by
  have steps : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s a []) (t'.config s') :=
    internalP_steps (H := Nat) run
  have run' : Silmaril.Wasm.Execution.Core.Steps P (hostOf (plusStartI I a).imports (Env.silent _))
      (invoke s ((plusStartI I a).addr (startOpI I a).1) (startOpI I a).2.1) (t'.config s') :=
    steps_of_noHostI _ steps
  obtain ⟨w, hw', -⟩ := ScalarInstance.answer_of_run (plusStartI_wellFormed hw ha)
    (throwsBelow_silent _ _) run' final
  have hpath : (plusStartI I a).Activation P s [.inr (.ask (startOpI I a)),
      .inr (.ans (startOpI I a) w)] s' :=
    .cons (.call s _) (.cons (.oret run final hw') (.nil _))
  refine wellFormed_of_plusStartI (ScalarInstance.WellFormed.activation
    (plusStartI_wellFormed hw ha) ?_ hpath).1
  intro e v hm
  simp at hm

end PlusStart

/-! ## The start function's core activation -/

section Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}

/-- The run of the start function's core activation, renamed. -/
theorem start_runI (hF : CoreFactsIS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y) :
    Silmaril.Wasm.Execution.Core.Steps Pf Silmaril.Wasm.SingleThreaded.Det.noHost (invoke I.store a [])
      (Config.mapH trampIdx (y.2.config y.1)) := by
  have h := invoke_steps_mapH (P := Pf) (xs := []) trampIdx (internalP_steps (coreSteps_internal hy))
  rw [hF.store] at h
  exact h

/-- **Under `StartNoCall`, the start function never calls out.** -/
theorem start_no_callI (hn : c.mod.StartNoCall Pf) (hF : CoreFactsIS c I cs ci (some a))
    {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y)
    {h : CanonHost (E3 Pf)} {args : List FlatValue}
    (hs : (E3 Pf).status y.1 y.2 = .callout h args) : False := by
  obtain ⟨E, a', h', args', hd⟩ := status_callout hs
  obtain ⟨E', hd'⟩ := decompose?_mapH trampIdx hd
  have hn' := hn I (some a) hF.isInst _ (start_runI hF hy)
  have hstore : (Config.mapH trampIdx (y.2.config y.1)).store = Store.mapH trampIdx y.1 :=
    congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  rw [hstore] at hn'
  exact absurd (hd'.symm.trans hn') (by simp)

/-- **The start function returns no values.** -/
theorem start_values_nilI (hF : CoreFactsIS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y)
    {ys : List FlatValue} (hs : (E3 Pf).status y.1 y.2 = .returned (.values ys)) : ys = [] := by
  obtain ⟨cvs, hc, hm⟩ := status_values hs
  rcases start_resultI hF.isInst.ok (hF.isInst.startTyped a rfl) (start_runI hF hy)
    (r := .values cvs) hc with h | h | ⟨x, h⟩
  · cases h
    simpa using hm.symm
  · cases h
  · cases h

/-- **A returning start function**: the start phase of the instance returns at the renamed
store, which is well formed. -/
theorem start_returnsI (hF : CoreFactsIS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y)
    {ys : List FlatValue} (hs : (E3 Pf).status y.1 y.2 = .returned (.values ys)) :
    Silmaril.Wasm.Game.StartsTo Pf Silmaril.Wasm.SingleThreaded.Det.noHost I.store (some a)
      (Store.mapH trampIdx y.1) ∧ I.WellFormed (Store.mapH trampIdx y.1) := by
  have hys := start_values_nilI hF hy hs
  subst hys
  obtain ⟨cvs, hc, hm⟩ := status_values hs
  have hcvs : cvs = [] := by
    rcases start_resultI hF.isInst.ok (hF.isInst.startTyped a rfl) (start_runI hF hy)
      (r := .values cvs) hc with h | h | ⟨x, h⟩
    · cases h
      rfl
    · cases h
    · cases h
  subst hcvs
  refine ⟨⟨_, start_runI hF hy, hc, ?_⟩, ?_⟩
  · exact congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  · have hr : Silmaril.Wasm.Game.Reach Pf (I.store, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a [])
        (Store.mapH trampIdx y.1, y.2) :=
      hF.store ▸ reach_mapH trampIdx (coreSteps_internal hy)
    refine start_wellFormedI hF.isInst.ok (hF.isInst.startTyped a rfl) hr (r := .values []) ?_
    exact (config_code_mapH _ _ _).trans hc

/-- **A trapping start function**: the start phase of the instance may fail. -/
theorem start_failsI (hF : CoreFactsIS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y)
    (hs : (E3 Pf).status y.1 y.2 = .returned .trap) : c.mod.StartFails Pf := by
  obtain ⟨c', res, run, hc, hr⟩ := coreRun_trap (P := Pf) trampIdx (coreSteps_internal hy) hs
  rw [hF.store] at run
  refine ⟨I, some a, hF.isInst, c', res, run, hc, ?_⟩
  rcases start_resultI hF.isInst.ok (hF.isInst.startTyped a rfl) run hc with h | h | h
  · subst h
    simp at hr
  · exact .inl h
  · exact .inr h

end Core

/-! ## Inversion -/

/-- A live run followed by a run to a configuration that is not live, without host events,
from a configuration with the host in control, ends at the live run's end. -/
theorem lrun_endI {hr : HostReady σ}
    {D : Call (core3P Pf) → Canon.P (core3P Pf) σ (Ret (core3P Pf))}
    {m m₂ m' : Machine.Config (core3P Pf) σ} {tr tr' : List (Label (core3P Pf) σ)}
    (d : LRun prof hr D m tr m₂) (hc₂ : m₂.ctl = []) (h : Machine.Steps prof hr D m tr' m')
    (hn : ∀ ev, Label.host ev ∉ tr') (hl : ¬ Live m') : tr' = tr ∧ m' = m₂ := by
  rcases d.inv h with hl' | ⟨tr'', e, h''⟩
  · exact absurd hl' hl
  · have hn'' : ∀ ev, Label.host ev ∉ tr'' := fun ev he => hn ev (e ▸ List.mem_append_right _ he)
    obtain ⟨rfl, rfl⟩ := steps_ctl_nil hc₂ h'' hn''
    exact ⟨by rw [e, List.append_nil], rfl⟩

theorem traceObs_coreI {pre : List (Label (core3P Pf) σ)} (h : ∀ l ∈ pre, l = .core) :
    traceObs pre = [] := by
  induction pre with
  | nil => rfl
  | cons l pre ih =>
    rw [h l List.mem_cons_self]
    exact ih (fun l hl => h l (List.mem_cons_of_mem _ hl))

/-- **Runs of the instantiation with a start function and imports** that end at a configuration
that is not live, without host events: the start function returned and the run is at
`afterStartCfgI`, observing the instance and `exportMapIS c`; or the start function trapped and
the store is locked down. Under `StartNoCall` the start function does not call out. -/
theorem start_runs_invI {c : SimpleI} (hc : c.Good) (hi : c.InstS) (har : c.Arity)
    (hn : c.mod.StartNoCall Pf) {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hF : CoreFactsIS c I cs ci (some a)) (h₀ : σ) {m' : Machine.Config (core3P Pf) σ}
    {tr : List (Label (core3P Pf) σ)}
    (hs : Machine.Steps prof (answerHostS Pf g).hr (DA Pf g) (instStartIS c h₀) tr m')
    (hne : ∀ ev, Label.host ev ∉ tr) (hl : ¬ Live m') :
    (∃ y : CoreSt (E3 Pf), Relation.ReflTransGen (CoreStep (E3 Pf))
        (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y ∧
        (∃ ys, (E3 Pf).status y.1 y.2 = .returned (.values ys)) ∧
        m' = afterStartCfgI Pf g y.1 a (fun k => I.addrs.getD k 0) c h₀ ∧
        traceObs tr = [instantiatedObs ⟨0⟩ (exportMapIS c)]) ∨
    (∃ y : CoreSt (E3 Pf), Relation.ReflTransGen (CoreStep (E3 Pf))
        (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y ∧
        (E3 Pf).status y.1 y.2 = .returned .trap ∧ m'.store.lockdown = true) := by
  obtain ⟨M₀, th, K, segs, rest, SP⟩ := start_pathI (prof := prof) (g := g) hc hi har hF h₀
  obtain ⟨tr₀, D₀, ho₀⟩ := SP.pre
  rcases D₀.inv hs with hlive | ⟨tr'', e, r'⟩
  · exact absurd hlive hl
  have hcore : Machine.Steps prof (answerHostS Pf g).hr (DA Pf g) (coreCfg M₀ th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a [])) tr'' m' := by
    rw [← SP.core, ← eq_coreCfg SP.ctl]
    exact r'
  rcases coreCfg_steps_inv hcore with
    ⟨y, -, hm, -⟩ | ⟨y, pre, l, m₂, tr₂, hy, hpre, e', hx, r''⟩
  · exact absurd (show Live m' from hm ▸ ⟨List.cons_ne_nil _ _, SP.lock⟩) hl
  rcases hx with ⟨ys, hst, hl₂, hm₂⟩ | ⟨hst, -, hm₂⟩ | ⟨h, args, hst⟩
  · show _ ∨ _
    have hys : ys = [] := start_values_nilI hF hy hst
    obtain ⟨tr₃, D₃, ho₃⟩ := SP.ret y
    have r₃ : Machine.Steps prof (answerHostS Pf g).hr (DA Pf g) (retCfg M₀ th K segs rest y [])
        tr₂ m' := hys ▸ hm₂ ▸ r''
    have hn₂ : ∀ ev, Label.host ev ∉ tr₂ := fun ev he => hne ev (by
      rw [e, e']
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ he)))
    obtain ⟨htr, hm'⟩ := lrun_endI D₃ rfl r₃ hn₂ hl
    have hobs : traceObs tr = [instantiatedObs ⟨0⟩ (exportMapIS c)] := by
      rw [e, e', htr, hl₂, traceObs_append, ho₀, traceObs_append, traceObs_coreI hpre]
      exact ho₃
    exact .inl ⟨y, hy, ⟨ys, hst⟩, hm', hobs⟩
  · have hm' : m' = trapCfg (coreCfg M₀ th K segs rest y) := steps_of_locked rfl rfl (hm₂ ▸ r'')
    exact .inr ⟨y, hy, hst, by rw [hm']; rfl⟩
  · exact (start_no_callI hn hF hy hst).elim

/-- **The results of instantiating `c.toRef` with a start function and imports**, under the
answering host and `StartNoCall`: an instance at `afterStartCfgI` of a core store the start
function returns at, a trap where it traps, or divergence. -/
theorem instBehaviours_startI {c : SimpleI} (hc : c.Good) (hi : c.InstS) (har : c.Arity)
    (hn : c.mod.StartNoCall Pf) {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hF : CoreFactsIS c I cs ci (some a)) (prof : ProfileKind) (h₀ : σ) :
    ∀ r ∈ instBehaviours prof (answerHostS Pf g)
        (Machine.Config.init (hostFuncs 0 c.imports CStore.empty) h₀) c.toRef (importArgs c.imports),
      (∃ y : CoreSt (E3 Pf), Relation.ReflTransGen (CoreStep (E3 Pf))
          (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y ∧
          (∃ ys, (E3 Pf).status y.1 y.2 = .returned (.values ys)) ∧
          r = .instance (afterStartCfgI Pf g y.1 a (fun k => I.addrs.getD k 0) c h₀) ⟨0⟩
            (exportMapIS c)) ∨
      (∃ y : CoreSt (E3 Pf), Relation.ReflTransGen (CoreStep (E3 Pf))
          (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y ∧
          (E3 Pf).status y.1 y.2 = .returned .trap ∧ r = .traps) ∨
      r = .diverges := by
  have hinit : (Machine.Config.init (hostFuncs 0 c.imports CStore.empty) h₀ :
      Machine.Config (core3P Pf) σ) = initIS c h₀ := initI_eq c h₀
  intro r hr
  rw [hinit] at hr
  cases r with
  | «instance» m' inst es =>
    show _ ∨ _
    obtain ⟨tr, hs, hne, hc', hlk, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartIS c h₀ := hostRun_inv s₁
    have hs₂ : Machine.Steps prof (answerHostS Pf g).hr (DA Pf g) (instStartIS c h₀) tr m' :=
      he ▸ hs₁
    rcases start_runs_invI hc hi har hn hF h₀ hs₂ hne (fun hl => hl.1 hc') with
      ⟨y, hy, hst, hm', hobs'⟩ | ⟨y, -, -, hlk'⟩
    · have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, exportMapIS c) := by
        rw [hobs', List.findSome?_cons, decodeInstantiated?_instantiatedObs]
      have hie : (inst, es) = ((⟨0⟩ : InstId), exportMapIS c) :=
        Option.some.inj (hobs.symm.trans hdec)
      exact .inl ⟨y, hy, hst, by rw [hm', (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]⟩
    · exact absurd (hlk.symm.trans hlk') (by simp)
  | traps =>
    show _ ∨ _
    obtain ⟨m', tr, hs, hne, -, ht⟩ := hr
    have ht' : m'.store.lockdown = true := ht
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStartIS c h₀ := hostRun_inv s₁
    have hs₂ : Machine.Steps prof (answerHostS Pf g).hr (DA Pf g) (instStartIS c h₀) tr m' :=
      he ▸ hs₁
    rcases start_runs_invI hc hi har hn hF h₀ hs₂ hne
        (fun hl => absurd (hl.2.symm.trans ht') (by simp)) with
      ⟨y, -, -, hm', -⟩ | ⟨y, hy, hst, -⟩
    · exact absurd ((congrArg (·.store.lockdown) hm').symm.trans ht') Bool.false_ne_true
    · exact .inr (.inl ⟨y, hy, hst, rfl⟩)
  | diverges => exact .inr (.inr rfl)

end Silmaril.Proofs.Wasm.Component.Reference

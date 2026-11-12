module

public import Silmaril.Proofs.Wasm.Component.Reference.StartRun
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The instantiation phase of a simple component with a start function

* `start_path`: the deterministic parts of the instantiation: a run without observations from
  the instantiation host event to the core activation of the start function, and from its return
  (no values) to `afterStartCfg`, observing the instance and `exportMapS c`;
* `instBehaviours_start`: every instantiation result is either an instance at `afterStartCfg` of a
  core store the start function returns at, or a trap where the start function traps, or
  divergence;
* `startOutcome_*`: these core outcomes as Core 3.0 runs of the start phase of the instance
  (`StartsTo`, `NumModule.StartFails`), with the store well formed after the start function.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)

variable {Pf : Profile} {prof : ProfileKind}

/-- The core activation of the start function in the instantiation, with the deterministic runs
around it. -/
structure StartPath (prof : ProfileKind) (Pf : Profile) (c : Simple)
    (cs : (core3P Pf).Store (CanonHost (core3P Pf))) (a : Nat) (addr : Nat → Nat)
    (M₀ : Machine.Config (core3P Pf) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (core3P Pf) Unit (Ret (core3P Pf)))
    (segs : List (Seg (core3P Pf) Unit)) (rest : List (Activation (core3P Pf) Unit)) : Prop where
  pre : ∃ tr, LRun prof (refHost Pf).hr (D Pf) (instStart c) tr M₀ ∧ traceObs tr = []
  ctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) K, segs⟩ :: rest
  core : M₀.store.core = cs
  lock : M₀.store.lockdown = false
  ret : ∀ y : CoreSt (E3 Pf), ∃ tr, LRun prof (refHost Pf).hr (D Pf)
    (retCfg M₀ th K segs rest y []) tr (afterStartCfg Pf y.1 a addr c) ∧
    traceObs tr = [instantiatedObs ⟨0⟩ (exportMapS c)]

/-- **The deterministic parts of the instantiation with a start function.** -/
theorem start_path {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hF : CoreFactsS c I cs ci (some a)) :
    ∃ M₀ th K segs rest, StartPath prof Pf c cs a (fun k => I.addrs.getD k 0) M₀ th K segs rest := by
  obtain ⟨tr₁, Post, R, ho₁, hP⟩ := inst_reaches (prof := prof) hF
  obtain ⟨K, D₁, hK⟩ := R (fun _ => pure .unit) [] [] rfl
  obtain ⟨M₀, th, Kc, segs, rest, tr₂, D₂, ho₂, hA⟩ := start_at prof
    { (allocCfg : Machine.Config (core3P Pf) Unit) with
      store := setCoreSt cs (allocCfg : Machine.Config (core3P Pf) Unit).store
      ctl := [⟨none, .prog (runStart ⟨0⟩ a >>= K), []⟩] } a {} (enterInst {} ⟨0⟩) (th := none)
    (K := K) (segs := []) (rest := []) rfl rfl rfl (addThread?_ok (.inl rfl) _)
    (removeThread?_enter _ _)
  refine ⟨M₀, th, Kc, segs, rest, ⟨_, D₁.trans D₂, by simp [ho₁, ho₂]⟩, hA.ctl, hA.core,
    hA.lock, fun y => ?_⟩
  obtain ⟨tr₃, D₃, ho₃⟩ := hA.ret y
  obtain ⟨tr₄, hP₄, ho₄⟩ := hP (startedCfg { (allocCfg : Machine.Config (core3P Pf) Unit) with
      store := setCoreSt cs (allocCfg : Machine.Config (core3P Pf) Unit).store
      ctl := [⟨none, .prog (runStart ⟨0⟩ a >>= K), []⟩] } a (enterInst {} ⟨0⟩) y.1) rfl
  obtain ⟨D₄, hl₄⟩ := hK _ _ _ _ hP₄ rfl
  have s : UniqueStep prof (refHost Pf).hr (D Pf)
      { endCfg (startedCfg { (allocCfg : Machine.Config (core3P Pf) Unit) with
          store := setCoreSt cs (allocCfg : Machine.Config (core3P Pf) Unit).store
          ctl := [⟨none, .prog (runStart ⟨0⟩ a >>= K), []⟩] } a (enterInst {} ⟨0⟩) y.1)
          (fun k => I.addrs.getD k 0) c with
        ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterStartCfg Pf y.1 a (fun k => I.addrs.getD k 0) c) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  refine ⟨_, D₃.trans (D₄.trans (.cons ⟨List.cons_ne_nil _ _, hl₄⟩ s (.refl _))), ?_⟩
  simp only [traceObs_append, ho₃, ho₄]
  rfl

/-! ## The start function's core activation -/

section Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}

/-- The run of the start function's core activation, renamed. -/
theorem start_run (hF : CoreFactsS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y) :
    Silmaril.Wasm.Execution.Core.Steps Pf Silmaril.Wasm.SingleThreaded.Det.noHost (invoke I.store a [])
      (Config.mapH (fun _ => 0) (y.2.config y.1)) := by
  have h := coreSteps_run (P := Pf) (xs := []) hy
  rw [hF.store] at h
  exact h

/-- **The start function returns no values.** -/
theorem start_values_nil (hF : CoreFactsS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y)
    {ys : List FlatValue} (hs : (E3 Pf).status y.1 y.2 = .returned (.values ys)) : ys = [] := by
  obtain ⟨cvs, hc, hm⟩ := status_values hs
  rcases start_result hF.isInst.ok (hF.isInst.startTyped a rfl) hF.isInst.2.1 (start_run hF hy)
    (r := .values cvs) hc with h | h | ⟨x, h⟩
  · cases h
    simpa using hm.symm
  · cases h
  · cases h

/-- **The start function never calls out.** -/
theorem start_no_callout' (hF : CoreFactsS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y)
    {h : CanonHost (E3 Pf)} {args : List FlatValue}
    (hs : (E3 Pf).status y.1 y.2 = .callout h args) : False := by
  obtain ⟨E, a', h', args', hd⟩ := status_callout hs
  obtain ⟨E', hd'⟩ := decompose?_mapH (fun _ => 0) hd
  have hn := start_no_callout hF.isInst.ok (hF.isInst.startTyped a rfl) hF.isInst.2.1
    (start_run hF hy)
  have hstore : (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).store =
      Store.mapH (fun _ => 0) y.1 :=
    congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  rw [hstore] at hn
  exact absurd (hd'.symm.trans hn) (by simp)

/-- **A returning start function**: the start phase of the instance returns at the renamed
store, which is well formed. -/
theorem start_returns (hF : CoreFactsS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y)
    {ys : List FlatValue} (hs : (E3 Pf).status y.1 y.2 = .returned (.values ys)) :
    Silmaril.Wasm.Game.StartsTo Pf Silmaril.Wasm.SingleThreaded.Det.noHost I.store (some a)
      (Store.mapH (fun _ => 0) y.1) ∧ I.WellFormed (Store.mapH (fun _ => 0) y.1) := by
  have hys := start_values_nil hF hy hs
  subst hys
  obtain ⟨cvs, hc, hm⟩ := status_values hs
  have hcvs : cvs = [] := by
    rcases start_result hF.isInst.ok (hF.isInst.startTyped a rfl) hF.isInst.2.1 (start_run hF hy)
      (r := .values cvs) hc with h | h | ⟨x, h⟩
    · cases h
      rfl
    · cases h
    · cases h
  subst hcvs
  refine ⟨⟨_, start_run hF hy, hc, ?_⟩, ?_⟩
  · exact congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  · have hr : Silmaril.Wasm.Game.Reach Pf (I.store, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a [])
        (Store.mapH (fun _ => 0) y.1, y.2) :=
      hF.store ▸ reach_mapH (fun _ => 0) (coreSteps_internal hy)
    refine start_wellFormed hF.isInst.ok (hF.isInst.startTyped a rfl) hF.isInst.2.1
      hr (r := .values []) ?_
    exact (config_code_mapH _ _ _).trans hc

/-- **A trapping start function**: the start phase of the instance may fail. -/
theorem start_fails (hF : CoreFactsS c I cs ci (some a)) {y : CoreSt (E3 Pf)}
    (hy : Relation.ReflTransGen (CoreStep (E3 Pf))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y)
    (hs : (E3 Pf).status y.1 y.2 = .returned .trap) : c.mod.StartFails Pf := by
  obtain ⟨c', res, run, hc, hr⟩ := coreRun_trap (P := Pf) (fun _ => (0 : Nat))
    (coreSteps_internal hy) hs
  rw [hF.store] at run
  refine ⟨I, some a, hF.isInst, c', res, run, hc, ?_⟩
  rcases start_result hF.isInst.ok (hF.isInst.startTyped a rfl) hF.isInst.2.1 run hc with
    h | h | h
  · subst h
    simp at hr
  · exact .inl h
  · exact .inr h

end Core

/-! ## Inversion -/

/-- A live run followed by a run to a configuration that is not live, without host events,
from a configuration with the host in control, ends at the live run's end. -/
theorem lrun_endS {hr : HostReady Unit} {D : Call (core3P Pf) → Canon.P (core3P Pf) Unit (Ret (core3P Pf))}
    {m m₂ m' : Machine.Config (core3P Pf) Unit} {tr tr' : List (Label (core3P Pf) Unit)}
    (d : LRun prof hr D m tr m₂) (hc₂ : m₂.ctl = []) (h : Machine.Steps prof hr D m tr' m')
    (hn : ∀ ev, Label.host ev ∉ tr') (hl : ¬ Live m') : tr' = tr ∧ m' = m₂ := by
  rcases d.inv h with hl' | ⟨tr'', e, h''⟩
  · exact absurd hl' hl
  · have hn'' : ∀ ev, Label.host ev ∉ tr'' := fun ev he => hn ev (e ▸ List.mem_append_right _ he)
    obtain ⟨rfl, rfl⟩ := steps_ctl_nil hc₂ h'' hn''
    exact ⟨by rw [e, List.append_nil], rfl⟩

theorem traceObs_core {pre : List (Label (core3P Pf) Unit)} (h : ∀ l ∈ pre, l = .core) :
    traceObs pre = [] := by
  induction pre with
  | nil => rfl
  | cons l pre ih =>
    rw [h l List.mem_cons_self]
    exact ih (fun l hl => h l (List.mem_cons_of_mem _ hl))

/-- **Runs of the instantiation with a start function** that end at a configuration that is not
live, without host events: the start function returned and the run is at `afterStartCfg`,
observing the instance and `exportMapS c`; or the start function trapped and the store is
locked down. -/
theorem start_runs_inv {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hF : CoreFactsS c I cs ci (some a)) {m' : Machine.Config (core3P Pf) Unit}
    {tr : List (Label (core3P Pf) Unit)}
    (hs : Machine.Steps prof (refHost Pf).hr (D Pf) (instStart c) tr m')
    (hn : ∀ ev, Label.host ev ∉ tr) (hl : ¬ Live m') :
    (∃ y : CoreSt (E3 Pf), Relation.ReflTransGen (CoreStep (E3 Pf))
        (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y ∧
        (∃ ys, (E3 Pf).status y.1 y.2 = .returned (.values ys)) ∧
        m' = afterStartCfg Pf y.1 a (fun k => I.addrs.getD k 0) c ∧
        traceObs tr = [instantiatedObs ⟨0⟩ (exportMapS c)]) ∨
    (∃ y : CoreSt (E3 Pf), Relation.ReflTransGen (CoreStep (E3 Pf))
        (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y ∧
        (E3 Pf).status y.1 y.2 = .returned .trap ∧ m'.store.lockdown = true) := by
  obtain ⟨M₀, th, K, segs, rest, SP⟩ := start_path (prof := prof) hF
  obtain ⟨tr₀, D₀, ho₀⟩ := SP.pre
  rcases D₀.inv hs with hlive | ⟨tr'', e, r'⟩
  · exact absurd hlive hl
  have hcore : Machine.Steps prof (refHost Pf).hr (D Pf) (coreCfg M₀ th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a [])) tr'' m' :=
    eq_core_k SP.ctl SP.core ▸ r'
  rcases coreCfg_steps_inv hcore with
    ⟨y, -, hm, -⟩ | ⟨y, pre, l, m₂, tr₂, hy, hpre, e', hx, r''⟩
  · exact absurd (show Live m' from hm ▸ ⟨List.cons_ne_nil _ _, SP.lock⟩) hl
  rcases hx with ⟨ys, hst, hl₂, hm₂⟩ | ⟨hst, -, hm₂⟩ | ⟨h, args, hst⟩
  · show _ ∨ _
    have hys : ys = [] := start_values_nil hF hy hst
    obtain ⟨tr₃, D₃, ho₃⟩ := SP.ret y
    have r₃ : Machine.Steps prof (refHost Pf).hr (D Pf) (retCfg M₀ th K segs rest y []) tr₂ m' :=
      hys ▸ hm₂ ▸ r''
    have hn₂ : ∀ ev, Label.host ev ∉ tr₂ := fun ev he => hn ev (by
      rw [e, e']
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ he)))
    obtain ⟨htr, hm'⟩ := lrun_endS D₃ rfl r₃ hn₂ hl
    have hobs : traceObs tr = [instantiatedObs ⟨0⟩ (exportMapS c)] := by
      rw [e, e', htr, hl₂, traceObs_append, ho₀, traceObs_append, traceObs_core hpre]
      exact ho₃
    exact .inl ⟨y, hy, ⟨ys, hst⟩, hm', hobs⟩
  · have hm' : m' = trapCfg (coreCfg M₀ th K segs rest y) := steps_of_locked rfl rfl (hm₂ ▸ r'')
    exact .inr ⟨y, hy, hst, by rw [hm']; rfl⟩
  · exact (start_no_callout' hF hy hst).elim

/-- **The results of instantiating `c.toRef` with a start function**: an instance at
`afterStartCfg` of a core store the start function returns at, a trap where it traps, or
divergence. -/
theorem instBehaviours_start {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hF : CoreFactsS c I cs ci (some a)) (prof : ProfileKind) :
    ∀ r ∈ instBehaviours prof (refHost Pf) (initConfig ()) c.toRef [],
      (∃ y : CoreSt (E3 Pf), Relation.ReflTransGen (CoreStep (E3 Pf))
          (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y ∧
          (∃ ys, (E3 Pf).status y.1 y.2 = .returned (.values ys)) ∧
          r = .instance (afterStartCfg Pf y.1 a (fun k => I.addrs.getD k 0) c) ⟨0⟩ (exportMapS c)) ∨
      (∃ y : CoreSt (E3 Pf), Relation.ReflTransGen (CoreStep (E3 Pf))
          (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a []) y ∧
          (E3 Pf).status y.1 y.2 = .returned .trap ∧ r = .traps) ∨
      r = .diverges := by
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show _ ∨ _
    obtain ⟨tr, hs, hn, hc, hlk, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStart c := hostRun_inv s₁
    have hs₂ : Machine.Steps prof (refHost Pf).hr (D Pf) (instStart c) tr m' := he ▸ hs₁
    rcases start_runs_inv hF hs₂ hn (fun hl => hl.1 hc) with ⟨y, hy, hst, hm', hobs'⟩ |
      ⟨y, -, -, hlk'⟩
    · have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, exportMapS c) := by
        rw [hobs', List.findSome?_cons, decodeInstantiated?_instantiatedObs]
      have hie : (inst, es) = ((⟨0⟩ : InstId), exportMapS c) :=
        Option.some.inj (hobs.symm.trans hdec)
      exact .inl ⟨y, hy, hst, by rw [hm', (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]⟩
    · exact absurd (hlk.symm.trans hlk') (by simp)
  | traps =>
    show _ ∨ _
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    have ht' : m'.store.lockdown = true := ht
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStart c := hostRun_inv s₁
    have hs₂ : Machine.Steps prof (refHost Pf).hr (D Pf) (instStart c) tr m' := he ▸ hs₁
    rcases start_runs_inv hF hs₂ hn (fun hl => absurd (hl.2.symm.trans ht') (by simp)) with
      ⟨y, -, -, hm', -⟩ | ⟨y, hy, hst, -⟩
    · exact absurd ((congrArg (·.store.lockdown) hm').symm.trans ht') Bool.false_ne_true
    · exact .inr (.inl ⟨y, hy, hst, rfl⟩)
  | diverges => exact .inr (.inr rfl)

end Silmaril.Proofs.Wasm.Component.Reference

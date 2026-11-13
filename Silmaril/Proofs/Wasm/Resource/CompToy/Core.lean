module

public import Silmaril.Proofs.Wasm.Resource.CompToy.Get

/-!
# The toy resource component: core activations with built-in callouts

The core phase of an export call whose core code calls canon built-ins (`resource.new`,
`resource.drop`) of its own instance. Each callout is run by the machine's dispatcher `D P`
(the built-in's program), not answered by a host. The core code is analysed in the every-run
program logic `Silmaril.Wasm.Logic.Hoare` under a host relation `Hc` on the core store
(for the toy, `Open.specHost` of an import context); the machine is related to it callout by
callout:

* `CalloutsAns Hc Inv`: from every frame satisfying `Inv`, a callout that `Hc` has an outcome
  for is run by the machine either to the resumed activation, in a frame satisfying `Inv` again,
  with flat results that `Hc` allows (keeping the core store), or to a configuration whose only
  step is a trap;
* **`core_inv`**: then every machine run from the activation that ends where call `cid` is
  resolved leaves the core phase by an exit that is not a callout (`CoreExit`), from a frame
  satisfying `Inv` and a core configuration reachable under `Hc` from the start `c₀`. The
  callouts in between are not assumed to be answered in any particular way: their answers are
  whatever the machine computes, constrained only through `CalloutsAns`.

The proof follows `CalloutCore.segs_inv` (`Silmaril.Proofs.Wasm.Component.Reference`) with the
host-answered callouts replaced by machine-run built-ins. New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (HostSemantics Steps)

variable {P : Silmaril.Wasm.Numerics.Profile} {prof : ProfileKind}

/-- The callouts of the core phase (thread `th`, continuation `K`, segments `segs`, rest
`rest`) are run by the machine as `Hc` allows: from a frame `B` satisfying `Inv`, a callout
`h args` (flat `ys`) at core state `x` for which `Hc` has an outcome either runs to the resumed
activation in a frame satisfying `Inv`, on flat results `flat` that `Hc` allows with the core
store unchanged, or to a configuration whose only step is a trap. -/
def CalloutsAns (Hc : HostSemantics (CanonHost (E3 P))) (Inv : Machine.Config (E3 P) Unit → Prop)
    (th : Option ThreadId) (K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P)))
    (segs : List (Seg (E3 P) Unit)) (rest : List (Activation (E3 P) Unit)) : Prop :=
  ∀ (B : Machine.Config (E3 P) Unit) (x : CoreSt (E3 P)) (E : Silmaril.Wasm.SingleThreaded.Ctx)
    (a : ℕ) (h : CanonHost (E3 P)) (args : List Silmaril.Wasm.Execution.Core.Val)
    (ys : List FlatValue) (o : Silmaril.Wasm.Execution.Host.Outcome
      (Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))) Silmaril.Wasm.Execution.Core.Result),
    Inv B → Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, h, args) →
    (E3 P).status x.1 x.2 = .callout h ys → Hc h x.1 args o →
    (∃ B' flat tr, Inv B' ∧
      Hc h x.1 args (.returned x.1 (.values (flat.map Silmaril.Wasm.SingleThreaded.ofFlat))) ∧
      LRun prof (refHost P).hr (D P) (coreCfg B th K segs rest x) (.tau :: tr)
        (coreCfg B' th K segs rest (x.1, (E3 P).resume x.1 x.2 (.values flat)))) ∨
    (∃ tr mT r, LRun prof (refHost P).hr (D P) (coreCfg B th K segs rest x) tr mT ∧ Live mT ∧
      UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT))

/-- Host-free runs are runs under every host relation. -/
theorem steps_noHost {H : Type} (Hc : HostSemantics H) {c c' : Silmaril.Wasm.Execution.Core.Config H}
    (h : Steps P (noHostH H) c c') : Steps P Hc c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact .tail ih (Silmaril.Wasm.Execution.Core.Step.of_noHost Hc hst)

/-- Host-free core runs of the machine are runs under every host relation. -/
theorem coreSteps_host (Hc : HostSemantics (CanonHost (E3 P))) {x y : CoreSt (E3 P)}
    (h : Relation.ReflTransGen (CoreStep (E3 P)) x y) :
    Steps P Hc (x.2.config x.1) (y.2.config y.1) :=
  steps_noHost Hc (internalP_steps (P := P) (coreSteps_internalP h))

/-- The resumption of a callout with flat results is the host step returning their values. -/
theorem step_resume {Hc : HostSemantics (CanonHost (E3 P))} {y : CoreSt (E3 P)}
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : ℕ} {h : CanonHost (E3 P)}
    {args : List Silmaril.Wasm.Execution.Core.Val} {flat : List FlatValue}
    (hd : Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, h, args))
    (hr : Hc h y.1 args (.returned y.1 (.values (flat.map Silmaril.Wasm.SingleThreaded.ofFlat)))) :
    Silmaril.Wasm.Execution.Core.Step P Hc (y.2.config y.1)
      ((y.1, (E3 P).resume y.1 y.2 (.values flat)).2.config y.1) := by
  have e : (y.2.config y.1).store = y.1 := Silmaril.Wasm.SingleThreaded.Thread.config_store y.1 y.2
  have hd' : Silmaril.Wasm.SingleThreaded.decompose? (y.2.config y.1).store
      (y.2.config y.1).code = some (E, a, h, args) := by rw [e]; exact hd
  have hs := Silmaril.Wasm.Logic.Open.redex_step_ret (P := P) hd' (by rw [e]; exact hr)
  show Silmaril.Wasm.Execution.Core.Step P Hc _
    (((E3 P).resume y.1 y.2 (.values flat)).config y.1)
  erw [resume_values, Silmaril.Wasm.SingleThreaded.resumeResult_config hd]
  exact hs

/-- A live configuration followed by a trap does not resolve a call. -/
theorem not_resolved_of_trapRun {M mT m' : Machine.Config (E3 P) Unit}
    {trT tr : List (Label (E3 P) Unit)} {rT : TrapReason} {cid : CallId} {r : Option (List Silmaril.Wasm.Component.Reference.Val)}
    (hrun : LRun prof (refHost P).hr (D P) M trT mT) (hlive : Live mT)
    (hu : UniqueStep prof (refHost P).hr (D P) mT (.trap rT) (trapCfg mT))
    (hs : Steps prof (refHost P).hr (D P) M tr m') :
    ¬ (CallOutcome.resolved r).Holds (refHost P).hr cid m' := by
  intro ho
  rcases hrun.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact hl.not_holds _ _ ho
  cases r' with
  | refl => exact hlive.not_holds _ _ ho
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    rw [steps_of_locked rfl rfl r''] at ho
    exact absurd ho.2.1 (by simp [trapCfg, lockdownSt])

/-- How a run of the core phase ends where a call is resolved: an exit that is not a callout,
from a frame satisfying `Inv` and a core state reachable under `Hc` from `c₀`. -/
def CoreDone (Hc : HostSemantics (CanonHost (E3 P))) (Inv : Machine.Config (E3 P) Unit → Prop)
    (c₀ : Silmaril.Wasm.Execution.Core.Config (CanonHost (E3 P))) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
    (rest : List (Activation (E3 P) Unit)) (tr : List (Label (E3 P) Unit))
    (m' : Machine.Config (E3 P) Unit) : Prop :=
  ∃ B' y l m₁ tr₂, Inv B' ∧ Steps P Hc c₀ (y.2.config y.1) ∧
    (∀ h ys, (E3 P).status y.1 y.2 ≠ .callout h ys) ∧ CoreExit B' th K segs rest y l m₁ ∧
    Steps prof (refHost P).hr (D P) m₁ tr₂ m' ∧ tr₂ <:+ tr

/-- One callout answered: the run continues from the resumed activation. -/
theorem core_inv_callout {Hc : HostSemantics (CanonHost (E3 P))}
    {Inv : Machine.Config (E3 P) Unit → Prop} {c₀ : Silmaril.Wasm.Execution.Core.Config (CanonHost (E3 P))}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)} {cid : CallId}
    {r : Option (List Silmaril.Wasm.Component.Reference.Val)} {n : ℕ}
    (ih : ∀ B x tr m', tr.length ≤ n → Inv B → Steps P Hc c₀ (x.2.config x.1) →
      Steps prof (refHost P).hr (D P) (coreCfg B th K segs rest x) tr m' →
      (CallOutcome.resolved r).Holds (refHost P).hr cid m' →
      CoreDone (prof := prof) Hc Inv c₀ th K segs rest tr m')
    {B B' : Machine.Config (E3 P) Unit} {y : CoreSt (E3 P)} {E : Silmaril.Wasm.SingleThreaded.Ctx}
    {a : ℕ} {h : CanonHost (E3 P)} {args : List Silmaril.Wasm.Execution.Core.Val}
    {flat : List FlatValue} {tr₃ tr : List (Label (E3 P) Unit)} {m' : Machine.Config (E3 P) Unit}
    (hreach : Steps P Hc c₀ (y.2.config y.1))
    (hd : Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, h, args))
    (hB' : Inv B')
    (hans : Hc h y.1 args (.returned y.1 (.values (flat.map Silmaril.Wasm.SingleThreaded.ofFlat))))
    (hrun : LRun prof (refHost P).hr (D P) (coreCfg B th K segs rest y) (.tau :: tr₃)
      (coreCfg B' th K segs rest (y.1, (E3 P).resume y.1 y.2 (.values flat))))
    (hn : tr.length ≤ n + 1)
    (r' : Steps prof (refHost P).hr (D P) (coreCfg B th K segs rest y) tr m')
    (ho : (CallOutcome.resolved r).Holds (refHost P).hr cid m') :
    CoreDone (prof := prof) Hc Inv c₀ th K segs rest tr m' := by
  rcases hrun.inv r' with hl' | ⟨tr'', e, r''⟩
  · exact absurd ho (hl'.not_holds _ _)
  have hlen : tr''.length ≤ n := by
    have h₁ := congrArg List.length e
    simp only [List.length_append, List.length_cons] at h₁
    omega
  obtain ⟨B₁, y₁, l₁, m₁, tr₂, h₁, h₂, h₃, h₄, h₅, hsuf⟩ :=
    ih _ _ tr'' m' hlen hB' (hreach.tail (step_resume hd hans)) r'' ho
  exact ⟨B₁, y₁, l₁, m₁, tr₂, h₁, h₂, h₃, h₄, h₅, hsuf.trans ⟨_, e.symm⟩⟩

/-- **The core phase with built-in callouts.** If the callouts are run as `Hc` allows
(`CalloutsAns`) and the core code is safe under `Hc` from `c₀`, every machine run from the
activation that ends where call `cid` is resolved leaves the core phase by an exit that is not a
callout, from a frame satisfying `Inv` and a core state reachable under `Hc`. -/
theorem core_inv {Hc : HostSemantics (CanonHost (E3 P))} {Inv : Machine.Config (E3 P) Unit → Prop}
    {c₀ : Silmaril.Wasm.Execution.Core.Config (CanonHost (E3 P))} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {cid : CallId} {r : Option (List Silmaril.Wasm.Component.Reference.Val)}
    (hl : ∀ B, Inv B → B.store.lockdown = false)
    (hco : CalloutsAns (prof := prof) Hc Inv th K segs rest)
    (hsafe : ∀ c, Steps P Hc c₀ c →
      (∃ c', Silmaril.Wasm.Execution.Core.Step P Hc c c') ∨
        ∃ o, Silmaril.Wasm.Logic.Hoare.Exits o c.code) :
    ∀ (n : ℕ) (B : Machine.Config (E3 P) Unit) (x : CoreSt (E3 P)) (tr : List (Label (E3 P) Unit))
      (m' : Machine.Config (E3 P) Unit), tr.length ≤ n → Inv B → Steps P Hc c₀ (x.2.config x.1) →
      Steps prof (refHost P).hr (D P) (coreCfg B th K segs rest x) tr m' →
      (CallOutcome.resolved r).Holds (refHost P).hr cid m' →
      CoreDone (prof := prof) Hc Inv c₀ th K segs rest tr m' := by
  intro n
  induction n with
  | zero =>
    intro B x tr m' hn hB _ hs ho
    have htr : tr = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst htr
    cases hs
    exact absurd ho ((show Live (coreCfg B th K segs rest x) from
      ⟨List.cons_ne_nil _ _, hl B hB⟩).not_holds _ _)
  | succ n ih =>
    intro B x tr m' hn hB hreach hs ho
    rcases coreCfg_steps_inv' hs with ⟨y, -, rfl⟩ | ⟨y, pre, l, m₁, tr₂, hy, rfl, st, hx, r⟩
    · exact absurd ho ((show Live (coreCfg B th K segs rest y) from
        ⟨List.cons_ne_nil _ _, hl B hB⟩).not_holds _ _)
    have hreach' : Steps P Hc c₀ (y.2.config y.1) := hreach.trans (coreSteps_host Hc hy)
    by_cases hc : ∃ h ys, (E3 P).status y.1 y.2 = .callout h ys
    swap
    · exact ⟨B, y, l, m₁, tr₂, hB, hreach', fun h ys e => hc ⟨h, ys, e⟩, hx, r,
        ⟨pre ++ [l], by simp⟩⟩
    obtain ⟨h, ys, hst⟩ := hc
    obtain ⟨E, a, args, hd, -⟩ := status_callout_redex hst
    have e : (y.2.config y.1).store = y.1 :=
      Silmaril.Wasm.SingleThreaded.Thread.config_store y.1 y.2
    have hd' : Silmaril.Wasm.SingleThreaded.decompose? (y.2.config y.1).store
        (y.2.config y.1).code = some (E, a, h, args) := by rw [e]; exact hd
    obtain ⟨o, hho⟩ : ∃ o, Hc h y.1 args o := by
      rcases hsafe _ hreach' with ⟨c', hc'⟩ | ⟨o, hex⟩
      · rcases Silmaril.Wasm.Logic.Open.redex_step_inv hd' hc' with ⟨s', r₀, hr₀, -⟩ | ⟨hr₀, -⟩
        · exact ⟨_, e ▸ hr₀⟩
        · exact ⟨_, e ▸ hr₀⟩
      · exact absurd hex (Silmaril.Wasm.Logic.Open.not_exits_of_redex P hd' o)
    have r' : Steps prof (refHost P).hr (D P) (coreCfg B th K segs rest y) (l :: tr₂) m' :=
      .cons st r
    have hn' : (l :: tr₂).length ≤ n + 1 := by
      simp only [List.length_append, List.length_cons] at hn ⊢
      omega
    rcases hco B y E a h args ys o hB hd hst hho with ⟨B', flat, tr₃, hB', hans, hrun⟩ |
      ⟨trT, mT, rT, hrun, hlive, hu⟩
    · obtain ⟨B₁, y₁, l₁, m₂, tr₄, h₁, h₂, h₃, h₄, h₅, hsuf⟩ :=
        core_inv_callout ih hreach' hd hB' hans hrun hn' r' ho
      exact ⟨B₁, y₁, l₁, m₂, tr₄, h₁, h₂, h₃, h₄, h₅, hsuf.trans ⟨pre, rfl⟩⟩
    · exact absurd ho (not_resolved_of_trapRun hrun hlive hu r')

/-! ## One built-in callout on the machine -/

/-- The configuration running the callout program of `h ys` above the parked activation. -/
abbrev calloutCfg (B : Machine.Config (E3 P) Unit) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
    (rest : List (Activation (E3 P) Unit)) (x : CoreSt (E3 P)) (h : CanonHost (E3 P))
    (ys : List FlatValue) : Machine.Config (E3 P) Unit :=
  { coreCfg B th K segs rest x with
    ctl := ⟨th, .prog (D P (.hostCallout h ys)), .core x.2 K :: segs⟩ :: rest }

/-- **A built-in callout run to flat results** by the machine's callout program, ending in a
store with the same core store: a live deterministic run to the resumed activation. -/
theorem builtin_lrun {B : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {x : CoreSt (E3 P)} {h : CanonHost (E3 P)}
    {ys flat : List FlatValue} {tr : List (Label (E3 P) Unit)} {S' : CStore (E3 P)}
    (hl : B.store.lockdown = false) (hs : (E3 P).status x.1 x.2 = .callout h ys)
    (hS' : S'.lockdown = false) (hcore : S'.core = x.1)
    (hrun : RunsQ (D P) th (D P (.hostCallout h ys)) (calloutCfg B th K segs rest x h ys) tr
      (.flat flat) { calloutCfg B th K segs rest x h ys with store := S' }) :
    LRun prof (refHost P).hr (D P) (coreCfg B th K segs rest x) (.tau :: (tr ++ [.tau]))
      (coreCfg { B with store := S' } th K segs rest (x.1, (E3 P).resume x.1 x.2 (.values flat))) := by
  let M := coreCfg B th K segs rest x
  let M₁ := calloutCfg B th K segs rest x h ys
  have s₁ : UniqueStep prof (refHost P).hr (D P) M .tau M₁ :=
    .of_core rfl (callout_status_ne hs) (.coreCallout rfl hs)
  have hc₁ : M₁.ctl =
      ⟨th, .prog (D P (.hostCallout h ys) >>= Prog.pure), .core x.2 K :: segs⟩ :: rest := by
    show _ :: _ = _ :: _
    rw [Prog.bind_eq, Prog.bind_pure]
  have r₁ := hrun.lrun_at (prof := prof) (hr := (refHost P).hr) hl Prog.pure hc₁
  have s₂ : UniqueStep prof (refHost P).hr (D P)
      { M₁ with store := S', ctl := ⟨th, .prog (Prog.pure (.flat flat)), .core x.2 K :: segs⟩ :: rest }
      .tau
      { M₁ with store := S', ctl := ⟨th, .core ((E3 P).resume S'.core x.2 (.values flat)) K,
          segs⟩ :: rest } :=
    .of_prog rfl (fun _ _ e => by cases e) (Step.popCore rfl)
  have e : ({ M₁ with store := S', ctl := ⟨th, .core ((E3 P).resume S'.core x.2 (.values flat)) K,
      segs⟩ :: rest } : Machine.Config (E3 P) Unit) =
      coreCfg { B with store := S' } th K segs rest (x.1, (E3 P).resume x.1 x.2 (.values flat)) := by
    rw [hcore]
    cases S'
    dsimp only at hcore
    subst hcore
    rfl
  exact .cons ⟨List.cons_ne_nil _ _, hl⟩ s₁ (r₁.trans (.cons ⟨List.cons_ne_nil _ _, hS'⟩
    (e ▸ s₂) (.refl _)))

/-- **A built-in callout whose program traps**: a live deterministic run to a configuration
whose only step is a trap. -/
theorem builtin_traps {B : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {x : CoreSt (E3 P)} {h : CanonHost (E3 P)}
    {ys : List FlatValue} {tr : List (Label (E3 P) Unit)} {mT : Machine.Config (E3 P) Unit}
    (hl : B.store.lockdown = false) (hs : (E3 P).status x.1 x.2 = .callout h ys)
    (hT : TrapsQ (D P) th (D P (.hostCallout h ys)) (calloutCfg B th K segs rest x h ys) tr mT) :
    ∃ tr mT r, LRun prof (refHost P).hr (D P) (coreCfg B th K segs rest x) tr mT ∧ Live mT ∧
      UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT) := by
  let M := coreCfg B th K segs rest x
  let M₁ := calloutCfg B th K segs rest x h ys
  have s₁ : UniqueStep prof (refHost P).hr (D P) M .tau M₁ :=
    .of_core rfl (callout_status_ne hs) (.coreCallout rfl hs)
  obtain ⟨q, segs', r, hrun, hlive, hu⟩ := hT.lrun (prof := prof) (hr := (refHost P).hr) hl
    Prog.pure (.core x.2 K :: segs) rest
  have e : ({ M₁ with ctl := ⟨th, .prog (D P (.hostCallout h ys) >>= Prog.pure),
      .core x.2 K :: segs⟩ :: rest } : Machine.Config (E3 P) Unit) = M₁ := by
    rw [Prog.bind_eq, Prog.bind_pure]
  rw [e] at hrun
  exact ⟨_, _, r, .cons ⟨List.cons_ne_nil _ _, hl⟩ s₁ hrun, hlive, hu⟩

end Silmaril.Wasm.Resource.CompToy

module

public import Silmaril.Wasm.Component.FXRes.ContRun.Defs
public import Silmaril.Wasm.Resource.CompToy.Thms
public import Silmaril.Wasm.Component.Reference.Silent.Thms
public import Silmaril.Wasm.Resource.MachineTab.Defs
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Instantiating the `cont` component over the WasmFX engine with a continuation table

* Engine-generic run tools (the `core3P` versions are in
  `Silmaril.Wasm.Component.Reference.Silent`): `hostRun_inv'` (the instantiation host event),
  `steps_ctl_nil'`, `detRunL_end'`;
* `silentRun_contInst` (kernel evaluation, `P` free): the instantiation program of `contComp`
  over `fxCE P` runs silently to `contInst P`, observing instance `0` and the exports `contEs`;
* `contInst_*`: the host is in control, the store is not locked down, the engine's
  continuation table is empty, and the handle table of instance `0` (which holds the `cont`
  handles) is empty;
* `contInst_detRunL`, **`cont_instBehaviours`**, **`cont_instantiates`**: at every profile,
  choice profile and host, instantiating `contComp` has exactly one result, the instance at
  `contInst P` with root instance `0` and exports `contEs` (no trap, no divergence), and that
  result is reached.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContRun

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.FXRes.ContEngine Silmaril.Wasm.Component.FXRes.ContComp
open Silmaril.Wasm.Resource.CompToy (silentRun silentRun_detRunL)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Engine-generic run tools -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {D : Call E → Canon.P E σ (Ret E)}

/-- The instantiation host event goes to the host frame running the program. -/
theorem hostRun_inv' {m m' : Machine.Config E σ} {p : Canon.P E σ (Ret E)}
    (h : Machine.Step prof hr D m (.host (.run p)) m') :
    m' = { m with ctl := [.ofProg none (StepDefs.runProg p)] } := by
  cases h
  rfl

/-- From a host-in-control configuration, runs without host events do nothing. -/
theorem steps_ctl_nil' {m m' : Machine.Config E σ} {tr : List (Label E σ)} (hc : m.ctl = [])
    (h : Machine.Steps prof hr D m tr m') (hn : ∀ ev, Label.host ev ∉ tr) :
    tr = [] ∧ m' = m := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | cons s _ =>
    obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc s
    exact absurd List.mem_cons_self (hn ev)

/-- A quiet deterministic run that ends with the host in control is the only run without host
events from its start to a configuration with the host in control or locked down. -/
theorem detRunL_end' {m m₂ m' : Machine.Config E σ} {tr tr' : List (Label E σ)}
    (d : DetRunL prof hr D m tr m₂) (hq : SRuns.Quiet tr) (hc₂ : m₂.ctl = [])
    (h : Machine.Steps prof hr D m tr' m') (hn : ∀ ev, Label.host ev ∉ tr')
    (hc : m'.ctl = [] ∨ m'.store.lockdown = true) : tr' = tr ∧ m' = m₂ := by
  rcases d.inv h with ⟨tr₂, htr, d₂⟩ | ⟨tr'', htr, h''⟩
  · cases d₂ with
    | refl _ => exact ⟨by rw [htr, List.append_nil], rfl⟩
    | cons hl s _ =>
      have hl' : _ ∈ tr := htr ▸ List.mem_append_right tr' List.mem_cons_self
      rcases hc with hc | hc
      · obtain ⟨ev, he⟩ := Step.host_of_ctl_nil hc s.1
        rcases hq _ hl' with e | ⟨o, e⟩ <;> rw [he] at e <;> cases e
      · rw [hc] at hl
        cases hl
  · have hn'' : ∀ ev, Label.host ev ∉ tr'' :=
      fun ev he => hn ev (htr ▸ List.mem_append_right _ he)
    obtain ⟨rfl, rfl⟩ := steps_ctl_nil' hc₂ h'' hn''
    exact ⟨by rw [htr, List.append_nil], rfl⟩

/-- A quiet trace has no host event. -/
theorem quiet_no_host {tr : List (Label E σ)} (hq : SRuns.Quiet tr) :
    ∀ ev, Label.host ev ∉ tr := by
  intro ev he
  rcases hq _ he with e | ⟨o, e⟩ <;> cases e

end Generic

/-! ## The instantiation of `contComp` -/

variable (P : Profile)

/-- **The instantiation program of `contComp` runs silently** to `contInst P` (kernel
evaluation, `P` free). -/
theorem silentRun_contInst :
    silentRun (instantiateProg (E := fxCE P) (σ := Unit) contComp []) (initConfig ()) =
      some ([instantiatedObs ⟨0⟩ contEs], .unit, contInst P) := by
  kernel_rfl

theorem contInst_ctl : (contInst P).ctl = [] := by kernel_rfl

theorem contInst_lockdown : (contInst P).store.lockdown = false := by kernel_rfl

/-- The engine's continuation table is empty after instantiation. -/
theorem contInst_tab : (contInst P).store.core.tab = Table.empty := by kernel_rfl

/-- The handle table of instance `0` (the `cont` handles) is empty after instantiation. -/
theorem contInst_vtab : Silmaril.Wasm.Resource.vtab (contInst P).store ⟨0⟩ = Table.empty := by
  kernel_rfl

theorem contInst_nesting : (contInst P).store.nestingDepth = 0 := by kernel_rfl

variable {P}

/-- **The instantiation is one deterministic run** from the host event to `contInst P`. -/
theorem contInst_detRunL {prof : ProfileKind} {hr : HostReady Unit}
    {D : Call (fxCE P) → Canon.P (fxCE P) Unit (Ret (fxCE P))} :
    ∃ tr, SRuns.Quiet tr ∧ traceObs tr = [instantiatedObs ⟨0⟩ contEs] ∧
      DetRunL prof hr D (contStart P) tr (contInst P) := by
  obtain ⟨tr, hq, ho, d⟩ := silentRun_detRunL (prof := prof) (hr := hr) (dispatch := D) _
    (silentRun_contInst P) rfl none (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { contInst P with ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      { contInst P with ctl := [] } :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  have e : ({ contInst P with ctl := [] } : Machine.Config (fxCE P) Unit) = contInst P := by
    kernel_rfl
  refine ⟨tr ++ [.tau], fun l hl => ?_, ?_, ?_⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hq l hl
    · exact .inl (List.mem_singleton.1 hl)
  · rw [traceObs_append, ho]
    rfl
  · rw [← e]
    exact d.trans (.cons (contInst_lockdown P) s (.refl (contInst_lockdown P)))

/-- **The results of instantiating `contComp`**, at every profile, choice profile and host:
the only one is the instance at `contInst P` with root instance `0` and exports `contEs`. -/
theorem cont_instBehaviours (prof : ProfileKind) (h : Host (fxCE P) Unit) :
    ∀ r ∈ instBehaviours prof h (initConfig ()) (contProg P).comp (contProg P).args,
      r = .instance (contInst P) ⟨0⟩ contEs := by
  obtain ⟨trD, hq, ho, d⟩ := contInst_detRunL (P := P) (prof := prof) (hr := h.hr)
    (D := h.dispatch)
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn, hc, -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = contStart P := hostRun_inv' s₁
    obtain ⟨htr, hm⟩ := detRunL_end' d hq (contInst_ctl P) (he ▸ hs₁) hn (.inl hc)
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, contEs) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), contEs) := Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = contStart P := hostRun_inv' s₁
    obtain ⟨-, rfl⟩ := detRunL_end' d hq (contInst_ctl P) (he ▸ hs₁) hn (.inr ht)
    have hl : (contInst P).store.lockdown = true := ht
    rw [contInst_lockdown] at hl
    cases hl
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = contStart P := hostRun_inv' s₁
    exact absurd (d.toDetRun.diverges (he ▸ dv)) (not_diverges_of_ctl_nil (contInst_ctl P))

/-- **Instantiating `contComp` succeeds**: the instance at `contInst P` is a result. -/
theorem cont_instantiates (prof : ProfileKind) (h : Host (fxCE P) Unit) :
    InstResult.instance (contInst P) ⟨0⟩ contEs ∈
      instBehaviours prof h (initConfig ()) (contProg P).comp (contProg P).args := by
  obtain ⟨tr, hq, ho, d⟩ := contInst_detRunL (P := P) (prof := prof) (hr := h.hr)
    (D := h.dispatch)
  have hready : HostReadyCfg (initConfig () : Machine.Config (fxCE P) Unit) := by
    refine ⟨rfl, rfl, rfl⟩
  have s₀ : Machine.Step prof h.hr h.dispatch (initConfig ())
      (.host (instantiateTop (contProg P).comp (contProg P).args)) (contStart P) :=
    .hostRun hready
  refine ⟨tr, .cons s₀ d.toDetRun.steps, quiet_no_host hq, contInst_ctl P,
    contInst_lockdown P, ?_⟩
  rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]

end Silmaril.Wasm.Component.FXRes.ContRun

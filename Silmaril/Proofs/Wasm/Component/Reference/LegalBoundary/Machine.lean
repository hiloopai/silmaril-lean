module

public import Silmaril.Wasm.Component.Reference.LegalBoundary.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Thms
public import Silmaril.Wasm.Component.Reference.SessionObs.Defs

/-!
# A core activation whose status is a trap, on the reference machine (proofs)

For any engine `E`, a configuration `m` whose running activation is a core activation `ct` with
`E.status m.core ct = .returned .trap`:

* `step_iff_of_status_trap`: its only step is `coreTrap`, with label `.trap .coreTrap` and
  successor `trapCfg m` (no other rule applies: the program rules need a program head, the
  fault rules a program head, the host rules an empty control chain, and the other core rules
  another status);
* `not_step_trapCfg`: `trapCfg m` has no step at all (empty control chain and `lockdown`);
* `steps_iff_of_status_trap`: so its runs are the empty run and the one trap step;
* `not_diverges_of_status_trap`: it does not diverge;
* `step_iff_step_of_status_trap`: two such configurations with the same `trapCfg` have the
  same steps;
* `calls_trap_of_status_trap`, `calls_outcome_of_status_trap`: a top-level call that reaches it
  traps there, and every outcome of a run through it is a trap whose configuration has `m`'s
  core store and host state;
* `sessStep_trap_of_status_trap`, `sessCalls_trap_of_status_trap`: the session call traps and
  the session resumes from `resumeCfg m₀ (trapCfg m)`, whose core store is `m`'s.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Machine.StepDefs Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Reference

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

theorem step_iff_of_status_trap {m m' : Config E σ} {l : Label E σ} {th ct k segs rest}
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .returned .trap) :
    Step prof hr dispatch m l m' ↔ l = .trap .coreTrap ∧ m' = trapCfg m := by
  constructor
  · intro h
    cases h with
    | coreTrap => exact ⟨rfl, rfl⟩
    | fault f => cases f <;> simp_all
    | hostInvoke h => simp_all [HostReadyCfg]
    | hostTick h => simp_all [HostReadyCfg]
    | hostCancel h => simp_all [HostReadyCfg]
    | hostRun h => simp_all [HostReadyCfg]
    | coreInternal h1 h2 =>
      rw [hc] at h1
      simp only [List.cons.injEq, Activation.mk.injEq, Focus.core.injEq] at h1
      obtain ⟨⟨-, ⟨rfl, -⟩, -⟩, -⟩ := h1
      rw [hs] at h2
      rcases h2 with h2 | h2 <;> cases h2
    | coreReturned h1 h2 =>
      rw [hc] at h1
      simp only [List.cons.injEq, Activation.mk.injEq, Focus.core.injEq] at h1
      obtain ⟨⟨-, ⟨rfl, -⟩, -⟩, -⟩ := h1
      rw [hs] at h2
      cases h2
    | coreCallout h1 h2 =>
      rw [hc] at h1
      simp only [List.cons.injEq, Activation.mk.injEq, Focus.core.injEq] at h1
      obtain ⟨⟨-, ⟨rfl, -⟩, -⟩, -⟩ := h1
      rw [hs] at h2
      cases h2
    | _ => simp_all
  · rintro ⟨rfl, rfl⟩
    exact .coreTrap hc hs

theorem not_step_trapCfg {m m' : Config E σ} {l : Label E σ} :
    ¬ Step prof hr dispatch (trapCfg m) l m' := by
  intro h
  obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil (trapCfg_ctl m) h
  have := (Step.host_ready h).2.1
  simp at this

theorem steps_iff_of_status_trap {m m' : Config E σ} {tr : List (Label E σ)} {th ct k segs rest}
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .returned .trap) :
    Steps prof hr dispatch m tr m' ↔
      (tr = [] ∧ m' = m) ∨ (tr = [.trap .coreTrap] ∧ m' = trapCfg m) := by
  constructor
  · intro h
    cases h with
    | refl => exact .inl ⟨rfl, rfl⟩
    | cons s r =>
      obtain ⟨rfl, rfl⟩ := (step_iff_of_status_trap hc hs).1 s
      cases r with
      | refl => exact .inr ⟨rfl, rfl⟩
      | cons s' _ => exact absurd s' not_step_trapCfg
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .refl _
    · exact .cons (.coreTrap hc hs) (.refl _)

theorem not_diverges_of_status_trap {m : Config E σ} {th ct k segs rest}
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .returned .trap) :
    ¬ Diverges prof hr dispatch m := by
  intro d
  obtain ⟨b, ⟨l, -, s⟩, d'⟩ := d.unfold
  obtain ⟨-, rfl⟩ := (step_iff_of_status_trap hc hs).1 s
  exact not_diverges_of_ctl_nil (trapCfg_ctl m) d'

theorem step_iff_step_of_status_trap {m₁ m₂ m' : Config E σ} {l : Label E σ}
    {th₁ ct₁ k₁ segs₁ rest₁ th₂ ct₂ k₂ segs₂ rest₂}
    (hc₁ : m₁.ctl = ⟨th₁, .core ct₁ k₁, segs₁⟩ :: rest₁)
    (hs₁ : E.status m₁.core ct₁ = .returned .trap)
    (hc₂ : m₂.ctl = ⟨th₂, .core ct₂ k₂, segs₂⟩ :: rest₂)
    (hs₂ : E.status m₂.core ct₂ = .returned .trap) (ht : trapCfg m₁ = trapCfg m₂) :
    Step prof hr dispatch m₁ l m' ↔ Step prof hr dispatch m₂ l m' := by
  rw [step_iff_of_status_trap hc₁ hs₁, step_iff_of_status_trap hc₂ hs₂, ht]

theorem steps_snoc {m m₁ m₂ : Config E σ} {tr : List (Label E σ)} {l : Label E σ}
    (h : Steps prof hr dispatch m tr m₁) (s : Step prof hr dispatch m₁ l m₂) :
    Steps prof hr dispatch m (tr ++ [l]) m₂ := by
  induction h with
  | refl => exact .cons s (.refl _)
  | cons s' _ ih => exact .cons s' (ih s)

theorem calls_trap_of_status_trap {m₀ m : Config E σ} {c : CallId} {f : FuncId}
    {args : List Value.Val} {tr : List (Label E σ)} {th ct k segs rest}
    (h₁ : Steps prof hr dispatch m₀ (.host (invokeTop c f args) :: tr) m)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent c ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr)
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .returned .trap) :
    Calls prof hr dispatch m₀ c f args (trapCfg m) .trap := by
  refine ⟨tr ++ [.trap .coreTrap], ?_, ?_, ?_, trapCfg_lockdown m⟩
  · exact steps_snoc h₁ (.coreTrap hc hs)
  · intro ev hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hev ev hm
    · simp at hm
  · intro _ msg hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hint msg hm
    · simp at hm

theorem calls_outcome_of_status_trap {m m' : Config E σ} {tr : List (Label E σ)} {c : CallId}
    {out : CallOutcome} {th ct k segs rest}
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .returned .trap)
    (h : Steps prof hr dispatch m tr m') (hout : out.Holds hr c m') :
    out = .trap ∧ m'.core = m.core ∧ m'.host = m.host := by
  rcases (steps_iff_of_status_trap hc hs).1 h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨?_, rfl, rfl⟩
    cases out with
    | trap => rfl
    | resolved r => simp_all [CallOutcome.Holds]
    | deadlock => simp_all [CallOutcome.Holds, Deadlocked]
  · refine ⟨?_, rfl, rfl⟩
    cases out with
    | trap => rfl
    | resolved r => simp [CallOutcome.Holds] at hout
    | deadlock => simp [CallOutcome.Holds, Deadlocked] at hout

theorem sessStep_trap_of_status_trap [∀ a b, Decidable (E.ExternSub a b)]
    {h : Host E σ} {m₀ m : Config E σ} {n : Nat} {f : FuncId}
    {args : List Value.Val} {tr : List (Label E σ)} {th ct k segs rest}
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ f args) :: tr) m)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr)
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .returned .trap) :
    SessStep prof h m₀ n f args none (resumeCfg m₀ (trapCfg m)) ∧
      (resumeCfg m₀ (trapCfg m)).core = m.core ∧
      (resumeCfg m₀ (trapCfg m)).host = m.host :=
  ⟨.trap (calls_trap_of_status_trap h₁ hev hint hc hs), rfl, rfl⟩

theorem sessCalls_trap_of_status_trap [∀ a b, Decidable (E.ExternSub a b)]
    {h : Host E σ} {m₀ m : Config E σ} {n : Nat} {f : FuncId}
    {args : List Value.Val} {tr : List (Label E σ)} {th ct k segs rest}
    {cs : List (FuncId × List Value.Val)} {outs : List (Option (List Value.Val))}
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ f args) :: tr) m)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr)
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .returned .trap)
    (hrest : SessCalls prof h (resumeCfg m₀ (trapCfg m)) (n + 1) cs outs) :
    SessCalls prof h m₀ n ((f, args) :: cs) (none :: outs) :=
  .trap (calls_trap_of_status_trap h₁ hev hint hc hs) hrest

end Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary

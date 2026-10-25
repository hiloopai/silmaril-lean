module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Obs

@[expose] public section

/-! Observation simulation restricted to an explicit set of export names.
The source module is the original module, before export projection. -/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

def ScriptOn (allowed : String → Prop) (script : List Call) : Prop :=
  ∀ call ∈ script, allowed call.1

structure ExportsRelOn (allowed : String → Prop) (X : SimCtx) : Prop where
  fwd : ∀ x, allowed x → ∀ a, exportFunc? X.MA x = some a →
    ∃ b, exportFunc? X.MB x = some b ∧ X.F a b
  bwd : ∀ x, allowed x → ∀ b, exportFunc? X.MB x = some b →
    ∃ a, exportFunc? X.MA x = some a

theorem session_sim_on {allowed : String → Prop} {X : SimCtx} (hX : X.WF)
    (hE : ExportsRelOn allowed X) {S T : Store H} (hS : StoreRel X S T)
    {script : List Call} {bs : List (Behaviour Val)}
    (on : ScriptOn allowed script) (h : Session P closedHost X.MA S script bs) :
    Session P closedHost X.MB T script bs := by
  induction h generalizing T with
  | nil => exact .nil
  | @stop s x vs rest hno =>
    have hx := on (x, vs) (by simp)
    refine .stop fun b hb hinv => ?_
    obtain ⟨a, ha⟩ := hE.bwd _ hx _ hb
    obtain ⟨b', hb', hab⟩ := hE.fwd _ hx _ ha
    rw [hb] at hb'
    cases hb'
    exact hno a ha (invokeOk_bwd hS hab hinv)
  | @done s x vs rest a c r bs ha hok run hr tail ih =>
    have hx := on (x, vs) (by simp)
    obtain ⟨b, hb, hab⟩ := hE.fwd _ hx _ ha
    obtain ⟨hok', hvs⟩ := invokeOk_fwd hS hab hok
    obtain ⟨d', hrun', hrel⟩ := sim_steps hX run (invoke_rel hS hab hvs)
    exact .done hb hok' hrun' (hrel.result hr)
      (ih hrel.1 (fun call hc => on call (by simp [hc])))
  | @diverge s x vs rest a ha hok hd =>
    have hx := on (x, vs) (by simp)
    obtain ⟨b, hb, hab⟩ := hE.fwd _ hx _ ha
    obtain ⟨hok', hvs⟩ := invokeOk_fwd hS hab hok
    exact .diverge hb hok' (sim_diverges hX hd (invoke_rel hS hab hvs))

theorem obs_sim_on {allowed : String → Prop} {s : Store H} {xas : List ExternAddr}
    {MA MB : Module} {script : List Call} (on : ScriptOn allowed script)
    (hinst : ∀ c, Instantiate P closedHost s MA xas c → ∃ (X : SimCtx) (c' : Config H), X.WF ∧
      ExportsRelOn allowed X ∧ Instantiate P closedHost s MB xas c' ∧
      ConfRel X .ours c c' ∧ c.frame.module = X.MA ∧ c'.frame.module = X.MB) :
    ∀ bs ∈ moduleObs P closedHost s xas MA script,
      bs ∈ moduleObs P closedHost s xas MB script := by
  rintro bs ⟨c, hc, hcase⟩
  obtain ⟨X, c', hX, hE, hc', hrel, hmA, hmB⟩ := hinst c hc
  refine ⟨c', hc', ?_⟩
  rcases hcase with ⟨c₁, bs', hst, hcode, hses, rfl⟩ |
    ⟨c₁, r, hst, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
  · obtain ⟨d, hst', hrel'⟩ := sim_steps hX hst hrel
    refine .inl ⟨d, bs', hst', hrel'.result (r := .values []) hcode, ?_, rfl⟩
    rw [hmB]
    rw [hmA] at hses
    exact session_sim_on hX hE hrel'.1 on hses
  · obtain ⟨d, hst', hrel'⟩ := sim_steps hX hst hrel
    exact .inr (.inl ⟨d, r, hst', hrel'.result hcode, hr, rfl⟩)
  · exact .inr (.inr ⟨sim_diverges hX hd hrel, rfl⟩)

end Silmaril.Wasm.Binaryen.RUMESim

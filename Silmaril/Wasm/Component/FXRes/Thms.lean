module

public import Silmaril.Wasm.Component.FXRes.Defs
public import Silmaril.Proofs.Wasm.Component.FXRes.Basic

/-!
# Continuations as resources: the continuation store as a handle protocol (results)

Proofs in `Silmaril.Proofs.Wasm.Component.FXRes.Basic` (`kstep_of_stepFX'`, `ksteps_run`,
`ksteps_consumed`, `ksteps_count_free`, ...).

* `stepsFX'_store_protocol`, `stepsFX_store_protocol`: **the continuation store of every run
  respects the handle protocol**: the store history of a run from a configuration with no
  continuations is accepted by `handleProto ℕ r` for both roles: every new continuation gets a
  fresh index (provider), and only live continuations are consumed (client).
* `stepsFX'_consumed`, `stepsFX_consumed`: a consumed continuation stays consumed.
* `stepsFX'_one_shot`, `stepsFX_one_shot`: **one-shot continuations**: along every run, each
  continuation index is consumed (by `resume`, `resume_throw`, `cont.bind` or `switch`) at most
  once.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Resource
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : Silmaril.Wasm.Execution.Core.HostSemantics H}
  {fx : H → Option FuncFX}

/-- **The store history of a `StepFX'` run respects the handle protocol**, in both roles. -/
theorem stepsFX'_store_protocol {c d : ConfigFX H} (h : StepsFX' P host fx c d)
    (h0 : c.conts = []) :
    ∃ evs, KSteps c.conts d.conts evs ∧ ∀ r, (handleProto ℕ r).Accepts evs := by
  obtain ⟨evs, hs⟩ := ksteps_of_stepsFX' h
  refine ⟨evs, hs, fun r => ?_⟩
  rw [h0] at hs
  obtain ⟨L, hL, -⟩ := ksteps_run hs r kRel_nil
  show ((handleProto ℕ r).run (some []) evs).isSome
  rw [hL]
  rfl

/-- **The store history of a `StepFX` run respects the handle protocol**, in both roles. -/
theorem stepsFX_store_protocol {c d : ConfigFX H} (h : StepsFX P host fx c d)
    (h0 : c.conts = []) :
    ∃ evs, KSteps c.conts d.conts evs ∧ ∀ r, (handleProto ℕ r).Accepts evs := by
  obtain ⟨evs, hs⟩ := ksteps_of_stepsFX h
  refine ⟨evs, hs, fun r => ?_⟩
  rw [h0] at hs
  obtain ⟨L, hL, -⟩ := ksteps_run hs r kRel_nil
  show ((handleProto ℕ r).run (some []) evs).isSome
  rw [hL]
  rfl

/-- A consumed continuation stays consumed along a `StepFX'` run. -/
theorem stepsFX'_consumed {c d : ConfigFX H} (h : StepsFX' P host fx c d) {k : ℕ}
    (hk : Consumed c.conts k) : Consumed d.conts k := by
  obtain ⟨_, hs⟩ := ksteps_of_stepsFX' h
  exact ksteps_consumed hs hk

/-- A consumed continuation stays consumed along a `StepFX` run. -/
theorem stepsFX_consumed {c d : ConfigFX H} (h : StepsFX P host fx c d) {k : ℕ}
    (hk : Consumed c.conts k) : Consumed d.conts k := by
  obtain ⟨_, hs⟩ := ksteps_of_stepsFX h
  exact ksteps_consumed hs hk

/-- **One-shot continuations (`StepFX'`)**: every run's store history consumes each index at
most once. -/
theorem stepsFX'_one_shot {c d : ConfigFX H} (h : StepsFX' P host fx c d) :
    ∃ evs, KSteps c.conts d.conts evs ∧ ∀ k, evs.count (.free k) ≤ 1 := by
  obtain ⟨evs, hs⟩ := ksteps_of_stepsFX' h
  exact ⟨evs, hs, ksteps_count_free hs⟩

/-- **One-shot continuations (`StepFX`)**. -/
theorem stepsFX_one_shot {c d : ConfigFX H} (h : StepsFX P host fx c d) :
    ∃ evs, KSteps c.conts d.conts evs ∧ ∀ k, evs.count (.free k) ≤ 1 := by
  obtain ⟨evs, hs⟩ := ksteps_of_stepsFX h
  exact ⟨evs, hs, ksteps_count_free hs⟩

end Silmaril.Wasm.Component.FXRes

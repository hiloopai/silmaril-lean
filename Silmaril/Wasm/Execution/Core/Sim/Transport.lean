module

public import Silmaril.Wasm.Execution.Core.Sim.Closure
public import Silmaril.Wasm.Execution.Core.Sim.DeadSuffix

@[expose] public section

/-! # Store-returning transport of runs along the closure simulation

`ConfigSim.behavioursOf_subset` forgets the final store. A session of export
invocations (`Binaryen/Behaviour.lean`, `Session`) runs each invocation in the
store the previous one returned, so transporting a session needs the final stores
to stay related. This file keeps them: a terminal left configuration is matched by
a right run to the same result **with `StoreRel F`-related stores**
(`Closure.terminal_case_store`, the store-keeping form of `Closure.terminal_case`),
and hence every completed left run is matched by a completed right run with related
final stores (`closure_run_transport`). Divergence transports as before
(`closure_diverges_transport`). `dce_run_transport` and `dce_diverges_transport`
are the instances for dead-suffix deletion (`DeadSuffix.lean`), operational simulation development item 3.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

variable {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

omit [LawfulCodeRank rank] in
/-- `terminal_case`, keeping the store relation that `run_vals` and `exit_lift`
provide (and that the final `trap-instrs`/`throw_ref-instrs` discard preserves). -/
theorem terminal_case_store (hB : BaseFacts P host F BI B rank) {c d : Config H} {r : Result}
    (h : CfgRel F (AdminsRel BI (WithCuts B)) c d) (hc : c.code = r.toAdmin) :
    ∃ d', Steps P host d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c.store d'.store := by
  obtain ⟨s, f, x⟩ := c
  obtain ⟨t, g, y⟩ := d
  obtain ⟨hst, hfg, hxy⟩ := h
  dsimp only at hst hfg hxy hc ⊢
  subst g hc
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hxy
  cases r with
  | values vs =>
    obtain ⟨t', h', hst'⟩ := run_vals hB hsegs (by simp [Result.toAdmin]) [] hst
    exact ⟨⟨t', f, vals vs⟩, steps_congr h' (by simp [vals_nil'])
      (by simp [vals_nil', Result.toAdmin]), rfl, hst'⟩
  | trap =>
    obtain ⟨t', us', j', h', hst', -⟩ := exit_lift hB hsegs hst [] Exit.trap (us := [])
      (j := []) (by simp [Result.toAdmin, vals_nil'])
    have h'' : Steps P host ⟨t, f, y⟩ ⟨t', f, vals us' ++ [.trap] ++ j'⟩ :=
      steps_congr h' (by simp [vals_nil']) (by simp [vals_nil'])
    refine ⟨⟨t', f, [.trap]⟩, ?_, rfl, hst'⟩
    by_cases hne : us' ≠ [] ∨ j' ≠ []
    · exact h''.tail (Step.trapInstrs hne)
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa [vals_nil'] using h''
  | throw a =>
    obtain ⟨t', us', j', h', hst', -⟩ := exit_lift hB hsegs hst [] (Exit.throw a) (us := [])
      (j := []) (by simp [Result.toAdmin, vals_nil', throwing])
    have h'' : Steps P host ⟨t, f, y⟩ ⟨t', f, vals us' ++ throwing a ++ j'⟩ :=
      steps_congr h' (by simp [vals_nil']) (by simp [vals_nil'])
    refine ⟨⟨t', f, throwing a⟩, ?_, rfl, hst'⟩
    by_cases hne : us' ≠ [] ∨ j' ≠ []
    · exact h''.tail (Step.throwRefInstrs hne)
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa [vals_nil'] using h''

end Closure

/-- **Store-returning run transport.** A completed left run from closure-related
configurations is matched by a completed right run to the same result, with
related final stores. -/
theorem closure_run_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseSim P host F BI B rank) {c d c' : Config H} {r : Result}
    (h : CfgRel F (AdminsRel BI B) c d) (hs : Steps P host c c') (hc : c'.code = r.toAdmin) :
    ∃ d', Steps P host d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c'.store d'.store := by
  obtain ⟨sim, -⟩ := closure_configSim hF hhost hB
  obtain ⟨d₁, hd, hr⟩ :=
    sim.toForwardSim.steps hs (h.mono fun _ _ => AdminsRel.mono fun _ _ => Or.inl)
  obtain ⟨d', hd', hc', hst⟩ := Closure.terminal_case_store hB.toBaseFacts hr hc
  exact ⟨d', hd.trans hd', hc', hst⟩

/-- Divergence transports along the closure. -/
theorem closure_diverges_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseSim P host F BI B rank) {c d : Config H}
    (h : CfgRel F (AdminsRel BI B) c d) (hd : Diverges P host c) : Diverges P host d := by
  obtain ⟨sim, -⟩ := closure_configSim hF hhost hB
  exact sim.toForwardSim.diverges hd (h.mono fun _ _ => AdminsRel.mono fun _ _ => Or.inl)

/-! ## Dead-suffix deletion -/

/-- **DCE run transport**: for a code-parametric host, a completed run from a
configuration is matched by a completed run from any dead-suffix-related one, with
related final stores. -/
theorem dce_run_transport (hhost : HostParametric host) {c d c' : Config H} {r : Result}
    (h : CfgRel (FuncRel dceBI) (AdminsRel dceBI dceB) c d) (hs : Steps P host c c')
    (hc : c'.code = r.toAdmin) :
    ∃ d', Steps P host d d' ∧ d'.code = r.toAdmin ∧
      StoreRel (FuncRel dceBI) c'.store d'.store :=
  have hhost₀ : HostRespects (FuncRel dceBI) host := hhost.respects (fun f => FuncRel.refl f)
  closure_run_transport (fun _ _ h => h) hhost₀ (dceBaseSim (fun _ _ h => h) hhost₀) h hs hc

/-- **DCE divergence transport.** -/
theorem dce_diverges_transport (hhost : HostParametric host) {c d : Config H}
    (h : CfgRel (FuncRel dceBI) (AdminsRel dceBI dceB) c d) (hd : Diverges P host c) :
    Diverges P host d :=
  have hhost₀ : HostRespects (FuncRel dceBI) host := hhost.respects (fun f => FuncRel.refl f)
  closure_diverges_transport (fun _ _ h => h) hhost₀ (dceBaseSim (fun _ _ h => h) hhost₀) h hd

/-- Dead-suffix-related configurations, swapped, are dead-suffix related. -/
theorem CfgRel.dce_symm {c d : Config H} (h : CfgRel (FuncRel dceBI) (AdminsRel dceBI dceB) c d) :
    CfgRel (FuncRel dceBI) (AdminsRel dceBI dceB) d c := by
  have h' := CfgRel.flip h
  rw [dceBI_flip, dceB_flip] at h'
  exact ⟨h'.store.mono fun _ _ hf => FuncRel.dce_symm hf, h'.frame, h'.code⟩

end Silmaril.Wasm.Execution.Core.Sim

module

public import Silmaril.Wasm.Binaryen.MergeBackReference

@[expose] public section

/-! # Exact state-rule matching for module merging

Locals and relocated global addresses select the same values and cells. Memory
and table instructions only occur in unchanged ambient code in the current
linker fragment; their exact target mutations and profile-dependent growth
outcomes can be replayed while retaining the source function definitions.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Execution.Core Numerics SingleThreaded.Det
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type}

private theorem related_retain_funcs {source target target' : Store H}
    (related : StoreRelation.Related source target) (funcs : target'.funcs = target.funcs) :
    StoreRelation.Related { target' with funcs := source.funcs } target' := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  simpa only [funcs] using related.functions

/-- Variables reproduce the target's exact local or global read/write. -/
theorem variable_back_matching {P : Profile} {host : HostSemantics H} {mode : Mode}
    {source target target' : Config H} (step : VariableStep target target')
    (matching : Simulation.Matching mode source target)
    (scope : XAs source.frame.module source.code) :
    ∃ source', Step P host source source' ∧ Simulation.Matching mode source' target' := by
  obtain ⟨s₀, f₀, X⟩ := source
  obtain ⟨s, f, Y⟩ := target
  obtain ⟨s', f', Y'⟩ := target'
  have funcs : s'.funcs = s.funcs := by cases step <;> rfl
  have stores : StoreRelation.Related s₀ s := matching.stores
  have hco := matching.code
  have locals : f₀.locals = f.locals := matching.frames.locals
  cases mode with
  | same =>
    obtain rfl := frames_same matching.frames
    obtain ⟨args, e, rfl, hev, hfam⟩ := VariableStep.shape step
    obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
    change i = j at hr
    subst hr
    refine ⟨⟨{ s' with funcs := s₀.funcs }, f', Y'⟩, ?_, ?_, .same _, Control.same _ _⟩
    · apply Step.variable
      rw [store_eta stores.toState]
      exact variable_funcs step _
    · exact related_retain_funcs stores funcs
  | relocated r =>
    have view := matching.frames.view
    cases step with
    | localGet hloc =>
      obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .variable (.localGet (by simpa only [Frame.local?, locals] using hloc)),
        matching.stores, matching.frames, .val .nil⟩
    | localSet hx =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .variable (.localSet (by simpa only [locals] using hx)),
        matching.stores, matching.frames.setLocal _ _, .nil⟩
    | localTee =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .variable .localTee, matching.stores, matching.frames,
        .val (.val (.plain (by simp only [Instruction, instruction?]) .nil))⟩
    | globalGet hg =>
      obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
      obtain ⟨x, rfl, hx⟩ := inv_global (fun y => .globalGet y) view hr (fun _ h => h)
        (fun x h => by simp only [XI, XE] at h; exact h.2) (xi_of_mem scope (by simp))
      exact ⟨_, .variable (.globalGet (global_back hg hx matching.stores.globals)),
        matching.stores, matching.frames, .val .nil⟩
    | globalSet hg =>
      inv_head hco i hr
      obtain ⟨x₀, rfl, hx⟩ := inv_global (fun y => .globalSet y) view hr (fun _ h => h)
        (fun x h => by simp only [XI, XE] at h; exact h.2) (xi_of_mem scope (by simp))
      exact ⟨_, .variable (.globalSet (global_back hg hx matching.stores.globals)),
        matching.stores.setGlobal _ _, matching.frames, .nil⟩

theorem table_back_matching {P : Profile} {host : HostSemantics H} {mode : Mode}
    {source target target' : Config H} (step : TableStep P target target')
    (matching : Simulation.Matching mode source target) :
    ∃ source', Step P host source source' ∧ Simulation.Matching mode source' target' := by
  obtain ⟨s₀, f₀, X⟩ := source
  obtain ⟨s, f, Y⟩ := target
  obtain ⟨s', f', Y'⟩ := target'
  have funcs : s'.funcs = s.funcs := by cases step <;> rfl
  have stores : StoreRelation.Related s₀ s := matching.stores
  have hco := matching.code
  obtain ⟨args, e, rfl, hev, hfam⟩ := TableStep.shape step
  obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
  obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
  cases mode with
  | same =>
    obtain rfl := frames_same matching.frames
    change i = j at hr
    subst hr
    refine ⟨⟨{ s' with funcs := s₀.funcs }, f', Y'⟩, ?_, ?_, .same _, Control.same _ _⟩
    · apply Step.table
      rw [store_eta stores.toState]
      exact table_funcs step _
    · exact related_retain_funcs stores funcs
  | relocated r => exact (inv_none hr (fixed_table hfam r i) (none_table hfam r)).elim

theorem memory_back_matching {P : Profile} {host : HostSemantics H} {mode : Mode}
    {source target target' : Config H} (step : MemoryStep P target target')
    (matching : Simulation.Matching mode source target) :
    ∃ source', Step P host source source' ∧ Simulation.Matching mode source' target' := by
  obtain ⟨s₀, f₀, X⟩ := source
  obtain ⟨s, f, Y⟩ := target
  obtain ⟨s', f', Y'⟩ := target'
  have funcs : s'.funcs = s.funcs := by cases step <;> rfl
  have stores : StoreRelation.Related s₀ s := matching.stores
  have hco := matching.code
  obtain ⟨args, e, rfl, hev, hfam⟩ := MemoryStep.shape step
  obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
  obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
  cases mode with
  | same =>
    obtain rfl := frames_same matching.frames
    change i = j at hr
    subst hr
    refine ⟨⟨{ s' with funcs := s₀.funcs }, f', Y'⟩, ?_, ?_, .same _, Control.same _ _⟩
    · apply Step.memory
      rw [store_eta stores.toState]
      exact memory_funcs step _
    · exact related_retain_funcs stores funcs
  | relocated r => exact (inv_none hr (fixed_memory hfam r i) (none_memory hfam r)).elim

theorem BackwardStep.variable {P : Profile} {host : HostSemantics H}
    {target target' : Config H} (step : VariableStep target target') :
    BackwardStep P host target target' := by
  intro mode source matching scope
  exact variable_back_matching step matching scope

theorem BackwardStep.table {P : Profile} {host : HostSemantics H}
    {target target' : Config H} (step : TableStep P target target') :
    BackwardStep P host target target' := by
  intro mode source matching _
  exact table_back_matching step matching

theorem BackwardStep.memory {P : Profile} {host : HostSemantics H}
    {target target' : Config H} (step : MemoryStep P target target') :
    BackwardStep P host target target' := by
  intro mode source matching _
  exact memory_back_matching step matching

end Silmaril.Wasm.Binaryen.MergeUntyped

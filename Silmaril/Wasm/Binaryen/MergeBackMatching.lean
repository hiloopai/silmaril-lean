module

public import Silmaril.Wasm.Binaryen.MergeBack

@[expose] public section

/-! # Exact backward matching for pure merge steps

`MergeBack.back` reconstructs source progress but does not retain a relation to
the chosen target result. Numeric redexes admit a stronger statement: linking
does not change their code, so the source can take the very same profile-dependent
step, including its chosen NaN payload. The output configurations remain related.

Parametric rules retain their exact selected value, allowing relocated `select`
annotations. Vector redexes have the same property in unchanged ambient code. The linker's
current fragment still rejects vector operators in relocated module bodies.
These are leaf-family lemmas, not a backward simulation for all Core steps.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Execution.Core Numerics SingleThreaded.Det
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type}

/-- Parametric instructions preserve the exact selected result even when a
`select` annotation is relocated. -/
theorem parametric_back_matching {P : Profile} {host : HostSemantics H} {mode : Mode}
    {source target : Config H} {out : List Admin}
    (step : ParametricStep target.code out) (matching : Simulation.Matching mode source target) :
    Step P host source ⟨source.store, source.frame, out⟩ ∧
      Simulation.Matching mode ⟨source.store, source.frame, out⟩
        ⟨target.store, target.frame, out⟩ := by
  obtain ⟨s₀, f₀, X⟩ := source
  obtain ⟨s, f, Y⟩ := target
  have hco := matching.code
  cases step with
  | unreachable =>
    obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨.parametric .unreachable, matching.stores, matching.frames, .trap .nil⟩
  | nop =>
    obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨.parametric .nop, matching.stores, matching.frames, .nil⟩
  | drop v =>
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨.parametric (.drop v), matching.stores, matching.frames, .nil⟩
  | selectTrue hc =>
    inv_head hco i hr
    obtain ⟨ts₀, rfl⟩ := inv_select hr
    exact ⟨.parametric (.selectTrue (ts := ts₀) hc),
      matching.stores, matching.frames, .val .nil⟩
  | selectFalse v₁ v₂ ts =>
    inv_head hco i hr
    obtain ⟨ts₀, rfl⟩ := inv_select hr
    exact ⟨.parametric (.selectFalse v₁ v₂ ts₀),
      matching.stores, matching.frames, .val .nil⟩

/-- A scalar numeric target redex has exactly the same source redex. -/
theorem numeric_source_eq {P : Profile} {mode : Mode} {left right : ModuleInst}
    {source target out : List Admin} (step : NumericStep P target out)
    (control : Control mode left right source target) : source = target := by
  obtain ⟨args, e, rfl, hev, hfam⟩ := NumericStep.shape step
  obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
  obtain ⟨i, rfl, hr⟩ := control.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
  obtain rfl := inv_fixed hr (fun r => fixed_numeric hfam r _)
  rfl

/-- Reconstruct the particular scalar numeric step chosen by the target and keep
the resulting configuration relation. No numerical determinism, typing or
host restriction is needed. -/
theorem numeric_back_matching {P : Profile} {host : HostSemantics H} {mode : Mode}
    {source target : Config H} {out : List Admin}
    (step : NumericStep P target.code out) (matching : Simulation.Matching mode source target) :
    Step P host source ⟨source.store, source.frame, out⟩ ∧
      Simulation.Matching mode ⟨source.store, source.frame, out⟩
        ⟨target.store, target.frame, out⟩ := by
  have sourceStep : NumericStep P source.code out := by
    rw [numeric_source_eq step matching.code]
    exact step
  exact ⟨.numeric sourceStep, matching.stores, matching.frames,
    (LeafControlSimulation.numeric_control sourceStep matching.code).2⟩

/-- A vector target redex, when related by the existing linking relation, has
exactly the same source redex. -/
theorem vector_source_eq {P : Profile} {mode : Mode} {left right : ModuleInst}
    {source target out : List Admin} (step : VectorStep P target out)
    (control : Control mode left right source target) : source = target := by
  obtain ⟨args, e, rfl, hev, hfam⟩ := VectorStep.shape step
  obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
  obtain ⟨i, rfl, hr⟩ := control.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
  obtain rfl := inv_fixed hr (fun r => fixed_vector hfam r _)
  rfl

/-- Match the target's exact vector outcome, retaining the store/control relation.
This does not enlarge the executable linker's admitted instruction fragment. -/
theorem vector_back_matching {P : Profile} {host : HostSemantics H} {mode : Mode}
    {source target : Config H} {out : List Admin}
    (step : VectorStep P target.code out) (matching : Simulation.Matching mode source target) :
    Step P host source ⟨source.store, source.frame, out⟩ ∧
      Simulation.Matching mode ⟨source.store, source.frame, out⟩
        ⟨target.store, target.frame, out⟩ := by
  have sourceStep : VectorStep P source.code out := by
    rw [vector_source_eq step matching.code]
    exact step
  exact ⟨.vector sourceStep, matching.stores, matching.frames,
    (LeafControlSimulation.vector_control sourceStep matching.code).2⟩

end Silmaril.Wasm.Binaryen.MergeUntyped

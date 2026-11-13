module

public import Silmaril.Wasm.Jco.Styles.Lime.Defs
public import Silmaril.Wasm.LimeCompile.Direct.Thms

/-!
# Feature sets: the wrappers stay in the Lime fragment

* `adaptor_lime`: the adaptor's core module is the Core image of a Lime1 module (by
  construction, `adaptorLime md`).
* **`wrapCore_lime`**: the wrapper of the Core image of a Lime1 module is in the Lime fragment.
* **`limePipeline_eq`**: the Lime-preserving pipeline compiles the wrapped module with the 3.0 →
  Lime compiler of #861 and keeps the adaptor, which the compiler maps to itself.
  `limePipeline_lime`: on a Lime1 module the pipeline returns the module and the adaptor
  unchanged.
* `limePipeline_correct`: for a valid Core 3.0 module that compiles, the wrapped module of the
  pipeline's output is export-equivalent to the input (`Direct.compile_correct`), and the adaptor
  is the same.

These are statements about the syntax of the core modules. The behaviour of the wrapper over a
Lime1 instance, through the semantics of `XInstr` and `canonCallE`, is the subject of
`wrapE_correct`. The two are not connected (see `Silmaril.Wasm.Jco.Styles.Lime.Defs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm
open Silmaril.Wasm.LimeCompile.Direct (compile compile_lime compile_correct)

theorem adaptor_lime (md : Meta) : ∃ l : Lime1.Module, l.toCore = (adaptorLime md).toCore :=
  ⟨_, rfl⟩

/-- **The wrapper of a Lime module is in the Lime fragment.** -/
theorem wrapCore_lime {m : Module} (h : ∃ l : Lime1.Module, l.toCore = m) (md : Meta) :
    LimeFrag (wrapCore m md) := by
  intro m' hm'
  simp only [wrapCore, List.mem_cons, List.not_mem_nil, or_false] at hm'
  rcases hm' with rfl | rfl
  · exact h
  · exact adaptor_lime md

/-- **The pipeline compiles the wrapped module and keeps the adaptor.** -/
theorem limePipeline_eq (m : Module) (md : Meta) :
    limePipeline m md = (compile m).map fun l => [l, adaptorLime md] := by
  simp only [limePipeline, wrapCore, List.mapM_cons, List.mapM_nil, compile_lime]
  cases compile m <;> rfl

theorem limePipeline_lime (l : Lime1.Module) (md : Meta) :
    limePipeline l.toCore md = some [l, adaptorLime md] := by
  rw [limePipeline_eq, compile_lime]
  rfl

/-- The pipeline's outputs are Lime1 modules whose Core images are a wrapper in the Lime fragment. -/
theorem limePipeline_frag {m : Module} {md : Meta} {ls : List Lime1.Module}
    (h : limePipeline m md = some ls) : ∃ l, compile m = some l ∧ ls = [l, adaptorLime md] ∧
      LimeFrag (wrapCore l.toCore md) := by
  rw [limePipeline_eq] at h
  cases hc : compile m with
  | none => rw [hc] at h; cases h
  | some l =>
    rw [hc] at h
    exact ⟨l, rfl, (Option.some.inj h).symm, wrapCore_lime ⟨l, rfl⟩ md⟩

/-- **Correctness of the pipeline**, from the correctness of the 3.0 → Lime compiler. -/
theorem limePipeline_correct {H : Type} {P : Numerics.Profile}
    {host : Execution.Core.HostSemantics H} (hhost : Execution.Core.Sim.HostParametric host) {m : Module} {md : Meta}
    {l : Lime1.Module} (h : compile m = some l) (hm : ∃ mt, Validation.ModuleOk m mt) :
    limePipeline m md = some [l, adaptorLime md] ∧
      Binaryen.ExportEquiv (· = ·) P host m l.toCore :=
  ⟨by rw [limePipeline_eq, h]; rfl, compile_correct hhost h hm⟩

end Silmaril.Wasm.Jco

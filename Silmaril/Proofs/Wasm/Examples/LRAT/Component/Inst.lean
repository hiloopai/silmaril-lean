module

public import Silmaril.Wasm.Examples.LRAT.Component.Defs
public import Silmaril.Wasm.Examples.LRAT.Thms
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Component.Reference.Sound.Thms

@[expose] public section

/-!
# The LRAT component: the fragment conditions

`lratC` is in the fragment of `seq_refToSpec`: `lratC_good`, `lratC_floatFree`, `lratC_arity`
(by `decide`), and `lratC_inst`: the module's instance is `lratI` (`lratNum_isInst`, from the
kernel check `lrat_instance` and `isInstance_instOf`). Conversely every instance of the module
is `lratI` (`isInst_eq`: validation and instantiation are functions). The reference validator
accepts the translation (`lratC_valid`, `decide +kernel`).

`lratI` is irreducible (`Silmaril.Proofs.Wasm.Examples.LRAT.Shape`): its facts here come from the
kernel checks there (`lrat_exports`, `lrat_exports_eq`) and from unfolding it once.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Verify

theorem mem_exports {x : SimpleExport} (hx : x ∈ lratC.exports) :
    x = ⟨"add-lit", ⟨[.s32], []⟩, 0⟩ ∨ x = ⟨"end-clause", ⟨[], []⟩, 1⟩ ∨
      x = ⟨"step-begin", ⟨[.u32], []⟩, 2⟩ ∨ x = ⟨"step-lit", ⟨[.s32], []⟩, 3⟩ ∨
      x = ⟨"step-hint", ⟨[.u32], []⟩, 4⟩ ∨ x = ⟨"step-end", ⟨[], []⟩, 5⟩ ∨
      x = ⟨"delete", ⟨[.u32], []⟩, 6⟩ ∨ x = ⟨"is-unsat", ⟨[], [.bool]⟩, 7⟩ ∨
      x = ⟨"rat-begin", ⟨[.u32], []⟩, 8⟩ ∨ x = ⟨"rat-end", ⟨[], []⟩, 9⟩ := by
  simpa only [lratC, List.mem_cons, List.not_mem_nil, or_false] using hx

theorem lratC_good : lratC.Good :=
  ⟨by decide, by
    intro x hx
    rcases mem_exports hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨"add_lit", rfl⟩
    · exact ⟨"end_clause", rfl⟩
    · exact ⟨"step_begin", rfl⟩
    · exact ⟨"step_lit", rfl⟩
    · exact ⟨"step_hint", rfl⟩
    · exact ⟨"step_end", rfl⟩
    · exact ⟨"delete", rfl⟩
    · exact ⟨"unsat", rfl⟩
    · exact ⟨"rat_begin", rfl⟩
    · exact ⟨"rat_end", rfl⟩⟩

theorem lratC_floatFree : lratC.FloatFree := by
  intro x hx
  rcases mem_exports hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem lratC_arity : lratC.Arity := by
  intro x hx
  rcases mem_exports hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The computed instance, unfolded once. -/
theorem lratI_eq : lratI = instOf lratModule := by
  unfold lratI
  rfl

/-- **`lratI` is the instance of the checker module.** -/
theorem lratNum_isInst : lratNum.IsInst lratI := by
  obtain ⟨mt, hmt⟩ := isInstance_instOf lrat_instance
  refine ⟨⟨mt, lratI_eq ▸ hmt⟩, lrat_exports.2, ?_⟩
  rw [lrat_exports_eq]
  rfl

theorem lratC_inst : lratC.Inst := ⟨⟨lratI, lratNum_isInst⟩, rfl⟩

/-- Scalar instances with the same fields are equal. -/
theorem ScalarInstance.eq_of {I J : ScalarInstance} (h₁ : I.imports = J.imports)
    (h₂ : I.exports = J.exports) (h₃ : I.addrs = J.addrs) (h₄ : I.store = J.store) : I = J := by
  cases I
  cases J
  simp only at h₁ h₂ h₃ h₄
  subst h₁ h₂ h₃ h₄
  rfl

/-- Two instances of one module at one type have the same store and export addresses. -/
theorem IsInstance.store_addrs {m : Module} {mt mt' : CModuleType} {I J : ScalarInstance}
    (hI : IsInstance m mt I) (hJ : IsInstance m mt' J) : I.store = J.store ∧ I.addrs = J.addrs := by
  have hmt : mt = mt' := Option.some.inj (hI.valid.symm.trans hJ.valid)
  subst hmt
  obtain ⟨f, hf, hfa⟩ := hI.instantiated
  obtain ⟨g, hg, hga⟩ := hJ.instantiated
  have hfg : (I.store, f, (none : Option FuncIdx)) = (J.store, g, none) :=
    Option.some.inj (hf.symm.trans hg)
  simp only [Prod.mk.injEq, and_true] at hfg
  obtain ⟨hs, rfl⟩ := hfg
  exact ⟨hs, hfa.symm.trans hga⟩

/-- **Every instance of the checker module is `lratI`.** -/
theorem isInst_eq {I : ScalarInstance} (h : lratNum.IsInst I) : I = lratI := by
  obtain ⟨⟨mt, hI⟩, himp, hexp⟩ := h
  obtain ⟨⟨mt₀, hI₀⟩, himp₀, hexp₀⟩ := lratNum_isInst
  obtain ⟨hs, ha⟩ := IsInstance.store_addrs hI hI₀
  exact ScalarInstance.eq_of (himp.trans himp₀.symm) (hexp.trans hexp₀.symm) ha hs

/-- The validator accepts. -/
def accepts (c : Core3Component) : Bool :=
  match check? Silmaril.Wasm.Component.Features.p2 c with
  | .ok _ => true
  | .error _ => false

theorem exists_of_accepts {c : Core3Component} (h : accepts c = true) :
    ∃ ct, check? Silmaril.Wasm.Component.Features.p2 c = .ok ct := by
  unfold accepts at h
  split at h
  next ct hc => exact ⟨ct, hc⟩
  next => cases h

/-- **The reference validator accepts the component.** -/
theorem lratC_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 lratC.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

end Silmaril.Wasm.Examples.LRAT

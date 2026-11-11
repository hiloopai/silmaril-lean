module

public import Silmaril.Wasm.SSA.Checked.Defs
public import Silmaril.Wasm.SSA.Pipeline.Thms

/-!
# Validated optimisation: guarantees

* `validates_ok`: a module accepted by `validates` is valid (`BModule.Ok`,
  i.e. its lowering satisfies Core 3.0 `ModuleOk`), by silmaril's
  `validate_sound`.
* `optimizeFuncChecked_ok`: the module with the checked replacement is valid;
  `optimizeFuncChecked_spec`: the replacement is what `optimizeFuncIn?`
  returned, so it inherits the optimiser's semantic theorems.
* `optimizeModuleChecked_ok`: if the input validates, so does the output
  (either the optimised module, which was checked, or the input).
* `optimizeFuncChecked_equiv`: the checked replacement is valid in the
  module and, read back at the function's type, has exactly the original
  function's terminating outcomes (`optimizeFunc?_equiv`).
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen

theorem validates_ok {m : BModule} (h : validates m = true) : m.Ok :=
  Validation.validate_sound h

theorem optimizeFuncChecked_spec {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncChecked m g = some bf') :
    ∃ bf, m.funcs[g]? = some bf ∧ optimizeFuncIn? m bf = some bf' := by
  unfold optimizeFuncChecked at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bf, hbf, bf'', ho, hv⟩ := h
  split at hv
  · cases hv; exact ⟨bf, hbf, ho⟩
  · cases hv

theorem optimizeFuncChecked_ok {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncChecked m g = some bf') : (m.setFunc g bf').Ok := by
  unfold optimizeFuncChecked at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bf, -, bf'', -, hv⟩ := h
  split at hv
  · cases hv; exact validates_ok ‹_›
  · cases hv

theorem optimizeModuleChecked_ok {m : BModule} (h : validates m = true) :
    (optimizeModuleChecked m).Ok := by
  simp only [optimizeModuleChecked]
  split
  · exact validates_ok ‹_›
  · exact validates_ok h

theorem optimizeModuleChecked_cases (m : BModule) :
    optimizeModuleChecked m = m ∨
      (optimizeModuleChecked m = optimizeModule m ∧ (optimizeModule m).Ok) := by
  simp only [optimizeModuleChecked]
  split
  · exact .inr ⟨rfl, validates_ok ‹_›⟩
  · exact .inl rfl

theorem optimizeFunc?_recognised {ft : FuncType} {bf bf' : BFunc}
    (h : optimizeFunc? ft bf = some bf') : ∃ f, ofBFunc? ft bf = some f := by
  unfold optimizeFunc? at h
  cases hf : ofBFunc? ft bf with
  | none => simp [hf] at h
  | some f => exact ⟨f, rfl⟩

/-- **Validated, equivalent replacement.** -/
theorem optimizeFuncChecked_equiv {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncChecked m g = some bf') :
    (m.setFunc g bf').Ok ∧ ∃ bf ft f f', m.funcs[g]? = some bf ∧ m.funcType? bf.type = some ft ∧
      ofBFunc? ft bf = some f ∧ ofBFunc? ft bf' = some f' ∧
      ∀ args o, f.Run args o ↔ f'.Run args o := by
  refine ⟨optimizeFuncChecked_ok h, ?_⟩
  obtain ⟨bf, hbf, ho⟩ := optimizeFuncChecked_spec h
  unfold optimizeFuncIn? at ho
  cases hft : m.funcType? bf.type with
  | none => simp [hft] at ho
  | some ft =>
      simp only [hft, Option.bind_eq_bind, Option.bind_some] at ho
      obtain ⟨f, hf⟩ := optimizeFunc?_recognised ho
      obtain ⟨f', hf', heq⟩ := optimizeFunc?_equiv hf ho
      exact ⟨bf, ft, f, f', hbf, hft, hf, hf', heq⟩

end Silmaril.Wasm.SSA

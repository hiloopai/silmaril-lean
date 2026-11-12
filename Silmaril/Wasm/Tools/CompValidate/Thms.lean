module

public import Silmaril.Wasm.Tools.CompValidate.Defs
public import Silmaril.Wasm.Tools.Validate.Thms
public import Silmaril.Wasm.Tools.FastPaths.Thms

/-!
# What an accepted component guarantees

`check_core`: when `CompValidate.check F b` accepts, the bytes parse as a component in the
grammar of `Binary.md` at component-model `d095e2f` (`BinaryP3.parse`), and every core module
embedded in it (nested components included) is accepted by the core validator, hence
(`Validate.check_sound`) encodes a module that is valid in the specification's sense and uses
only what `F` grants (`Validate.Accepts`).

The component-level checks of `walk` are a tested transcription of wasmparser
(`tools/wasm-tools/tests/comp-diff.sh`), with no theorem.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.CompValidate

open Silmaril.Wasm.Tools.Features

theorem coreOk_iff {F : WFeatures} {m : ByteArray} :
    coreOk F m = true ↔ Validate.check F m = .ok () := by
  unfold coreOk
  rw [FastPaths.checkFast_eq]
  split <;> simp_all

/-- **An accepted component parses, and its core modules are valid.** -/
theorem check_core {F : WFeatures} {b : ByteArray} (h : check F b = .ok ()) :
    ∃ c, Silmaril.Wasm.Component.BinaryP3.parse b = .ok c ∧
      ∀ m ∈ coreModules c, Validate.Accepts F m.data.toList := by
  unfold check at h
  by_cases hcm : F.hasFlag "component-model" = true
  swap
  · simp [hcm] at h
  simp only [hcm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · simp at h
  · rename_i c hc
    refine ⟨c, hc, fun m hm => ?_⟩
    cases hf : (coreModules c).find? (fun m => !coreOk F m) with
    | some m' =>
      rw [hf] at h
      by_cases h1 : (Silmaril.Wasm.Component.BinaryP3.Check.strict c).1 <;>
        by_cases h2 : (Silmaril.Wasm.Component.BinaryP3.Check.strict c).2.1 <;> simp_all
    | none =>
      have hn := List.find?_eq_none.mp hf m hm
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hn
      exact Validate.check_sound (coreOk_iff.mp (by simpa using hn))

end Silmaril.Wasm.Tools.CompValidate

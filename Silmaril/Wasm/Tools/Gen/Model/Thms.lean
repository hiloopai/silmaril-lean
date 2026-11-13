module

public import Silmaril.Wasm.Tools.Gen.Model.Defs
public import Silmaril.Wasm.Tools.Gen.API.Thms
public import Silmaril.Wasm.Tools.Gen.Core.Thms
public import Silmaril.Wasm.Tools.Gen.Typed3.Thms

/-!
# Fuzzing kits of the Wasm models

* `Kit.shrink_spec`: checked shrinking in a kit keeps validity and the predicate, does not grow
  and ends in a local minimum;
* `coreKit P H S : Kit (coreModel P H S)`: the kit of Core 3.0 restricted to a feature set `S`:
  the checker `featCheck S`, the checked generator `featGen S`, the checked mutator `featMut S`
  and `featShrinker` (`Gen.Core`); what it runs is `featGenRun S` and `featMutRun S`
  (`coreKit_generator_run`, `coreKit_mutator_run`);
* the named models: **Wasm 1.0** `kit10`, **Wasm 2.0** `kit20`, **Wasm 3.0** `kit30`, **Lime1**
  `kitLime1` (the feature sets `v10`, `v20`, `v30`, `lime1` of `Silmaril.Wasm.Models`) and
  **WasmFX** `kitFX` (CoreFX, `Silmaril.Wasm.Models.FX.fxModel`, whose module language is
  `featLang wasmFX`);
* `coreKitT P H S h`: the same kit with the generator that needs no checker
  (`Typed3.typedGenAll`: the typed Core 3.0 generator when `S` has Wasm 3.0, else the typed
  Lime1 one), for every `S ≥ v10`; `kitFXT`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen

open Silmaril.Wasm.Models
open Silmaril.Wasm.Numerics (Profile)

namespace Kit

variable {M : WasmModel}

/-- **Checked shrinking in a kit**: validity and the predicate are kept, the size does not grow,
and no strictly smaller candidate of the result is valid and satisfies the predicate. -/
theorem shrink_spec (k : Kit M) (p : M.Module → Bool) {m : M.Module} (hv : M.Valid m)
    (hp : p m = true) :
    M.Valid (k.shrink p m) ∧ p (k.shrink p m) = true ∧
      k.shrinker.size (k.shrink p m) ≤ k.shrinker.size m ∧
      ∀ c ∈ k.shrinker.cands (k.shrink p m), k.shrinker.size c < k.shrinker.size (k.shrink p m) →
        (k.check c && p c) = false := by
  obtain ⟨h₁, h₂⟩ := Shrinker.shrink_valid k.lang k.shrinker p hv hp
  exact ⟨h₁, h₂, k.shrinker.shrink_size_le _ m, k.shrinker.shrink_local_min _ m⟩

end Kit

/-- **The kit of Core 3.0 at the feature set `S`.** -/
def coreKit (P : Profile) (H : Type) (S : FeatureSet) : Kit (coreModel P H S) where
  check := Core.featCheck S
  check_iff := Core.featCheck_iff S
  generator := Core.featGen S
  mutator := Core.featMut S
  shrinker := Core.featShrinker

theorem coreKit_generator_run (P : Profile) (H : Type) (S : FeatureSet) :
    (coreKit P H S).generator.run = Core.featGenRun S := rfl

theorem coreKit_mutator_run (P : Profile) (H : Type) (S : FeatureSet) :
    (coreKit P H S).mutator.run = Core.featMutRun S := rfl

theorem coreKit_shrink (P : Profile) (H : Type) (S : FeatureSet) :
    (coreKit P H S).shrink = Core.featShrink S := rfl

/-- **Wasm 1.0.** -/
def kit10 (P : Profile) (H : Type) : Kit (coreModel P H v10) := coreKit P H v10

/-- **Wasm 2.0.** -/
def kit20 (P : Profile) (H : Type) : Kit (coreModel P H v20) := coreKit P H v20

/-- **Wasm 3.0.** -/
def kit30 (P : Profile) (H : Type) : Kit (coreModel P H v30) := coreKit P H v30

/-- **Lime1.** -/
def kitLime1 (P : Profile) (H : Type) : Kit (coreModel P H lime1) := coreKit P H lime1

/-- **WasmFX** (CoreFX): its modules and validity are those of `featLang wasmFX`. -/
def kitFX (P : Profile) (H : Type) : Kit (Silmaril.Wasm.Models.FX.fxModel P H) where
  check := Core.featCheck wasmFX
  check_iff := Core.featCheck_iff wasmFX
  generator := Core.fxGen P H
  mutator := Core.fxMut P H
  shrinker := Core.featShrinker

/-- The kit of `S ≥ v10` with the generator that needs no checker (`Typed3.typedGenAll`). -/
def coreKitT (P : Profile) (H : Type) (S : FeatureSet) (h : v10 ≤ S) : Kit (coreModel P H S) :=
  (coreKit P H S).withGen (Typed3.typedGenAll S h)

/-- WasmFX with the typed Core 3.0 generator. -/
def kitFXT (P : Profile) (H : Type) : Kit (Silmaril.Wasm.Models.FX.fxModel P H) :=
  (kitFX P H).withGen (Typed3.fxGenT3 P H)

end Silmaril.Wasm.Tools.Gen

module

public import Silmaril.Wasm.Tools.Gen.Typed3.Defs
public import Silmaril.Wasm.Tools.Gen.Core.Thms
public import Silmaril.Proofs.Wasm.Tools.Gen.Typed3
public import Silmaril.Wasm.Tools.Gen.Typed.Thms

/-!
# The Core 3.0 typed generator: every output is valid, with no checker

* `module_valid`: every module of the generator is Core 3.0 valid (`ModuleValid`): the fixed
  type section, tags, globals and memories are valid, and every function body has a Core 3.0
  typing derivation (`Silmaril.Proofs.Wasm.Tools.Gen.Typed3.te_typed`);
* **`module_validIn`**: for every feature set `S ≥ v30`, every module is valid in `S`
  (`ValidIn S`);
* `typed3Gen S h`: the generator of the API (`Generator (Core.featLang S).toLang`) whose
  validity field is that theorem (no checker, no fallback); `coreGenT3 P H S h` for
  `coreModel P H S`, the named instances `v30GenT3` and `fxGenT3` (WasmFX);
* `typedGenAll S h`: **one checker-free generator for every `S ≥ v10`**: the Core 3.0 typed
  generator when `v30 ≤ S`, the Lime1 typed generator (`Gen.Typed.typedGen`) otherwise.

New statements over the proofs in `Silmaril.Proofs.Wasm.Tools.Gen.Typed3`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Typed3

open Silmaril.Wasm Silmaril.Wasm.Models
open Silmaril.Wasm.Numerics (Profile)

/-- **Every module of the generator is Core 3.0 valid.** -/
theorem module_valid (size : Nat) (r : Rng) :
    Silmaril.Wasm.Validation.ModuleValid (Rand.run (module size) r) :=
  Silmaril.Proofs.Wasm.Tools.Gen.Typed3.module_valid _ _

/-- **Every module of the generator is valid in `S`**, for every `S ≥ v30`. -/
theorem module_validIn {S : FeatureSet} (h : v30 ≤ S) (size : Nat) (r : Rng) :
    ValidIn S (Rand.run (module size) r) :=
  validIn_mono h ⟨module_valid size r, Silmaril.Proofs.Wasm.Tools.Gen.Typed3.module_inFeat _ _⟩

/-- **The typed Core 3.0 generator of `S`**: valid by construction. -/
def typed3Gen (S : FeatureSet) (h : v30 ≤ S) : Generator (Core.featLang S).toLang where
  run r n := Rand.run (module n) r
  valid r n := module_validIn h n r

/-- The typed Core 3.0 generator of `coreModel P H S`. -/
def coreGenT3 (P : Profile) (H : Type) (S : FeatureSet) (h : v30 ≤ S) :
    Generator (coreModel P H S).toLang :=
  typed3Gen S h

def v30GenT3 : Generator (Core.featLang v30).toLang := typed3Gen v30 le_rfl

/-- The WasmFX instance. -/
def fxGenT3 (P : Profile) (H : Type) : Generator (Silmaril.Wasm.Models.FX.fxModel P H).toLang :=
  typed3Gen wasmFX v30_le_wasmFX

/-- **A checker-free generator for every `S ≥ v10`**: the Core 3.0 one (GC, exceptions,
multi-memory, memory64, typed function references) when `S` has Wasm 3.0, else the Lime1 one. -/
def typedGenAll (S : FeatureSet) (h : v10 ≤ S) : Generator (Core.featLang S).toLang :=
  if h3 : v30.leB S = true then typed3Gen S (leB_iff.mp h3)
  else Silmaril.Wasm.Tools.Gen.Typed.typedGen S h

theorem typedGenAll_v30 {S : FeatureSet} (h : v10 ≤ S) (h3 : v30 ≤ S) :
    (typedGenAll S h).run = (typed3Gen S h3).run := by
  unfold typedGenAll
  split
  · rfl
  · next hn => exact absurd (leB_iff.mpr h3) hn

end Silmaril.Wasm.Tools.Gen.Typed3

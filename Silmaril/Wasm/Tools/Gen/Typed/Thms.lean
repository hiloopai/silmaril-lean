module

public import Silmaril.Wasm.Tools.Gen.Typed.Defs
public import Silmaril.Wasm.Tools.Gen.Core.Thms
public import Silmaril.Proofs.Wasm.Tools.Gen.Typed

/-!
# The typed generator: every output is valid, with no checker

* `lmodule_valid`: every Lime1 module of the typed generator is valid
  (`Silmaril.Wasm.Lime1.Validation.ModuleValid`): the erasure of a typed term is well typed
  (`Silmaril.Proofs.Wasm.Tools.Gen.Typed.te_typed`), and the skeleton's facts give the module
  rules;
* **`module_validIn`**: for every feature set `S ≥ v10`, every Core 3.0 module of the typed
  generator is valid in `S` (`ValidIn S`: Core 3.0 `ModuleValid`, by
  `Lime1.Validation.ModuleValid.toCore`, and inside `S`);
* `typedGen S h`: the generator of the API (`Generator (Core.featLang S).toLang`) whose validity
  field is that theorem: no checker and no fallback; `coreGenT P H S h` for `coreModel P H S`;
  the named instances `v10GenT`, `v20GenT`, `v30GenT`, `lime1GenT`, `fxGenT` (WasmFX), related
  along the feature lattice by `Generator.mapEmb` (`featGen_mono`) as every generator is.

New statements over the proofs in `Silmaril.Proofs.Wasm.Tools.Gen.Typed`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Typed

open Silmaril.Wasm Silmaril.Wasm.Models
open Silmaril.Wasm.Numerics (Profile)

/-- **Every Lime1 module of the typed generator is valid.** -/
theorem lmodule_valid (S : FeatureSet) (size : Nat) (r : Rng) :
    Silmaril.Wasm.Lime1.Validation.ModuleValid (Rand.run (lmodule S size) r) :=
  Silmaril.Proofs.Wasm.Tools.Gen.Typed.module_valid _ _ _

/-- **Every module of the typed generator is valid in `S`**, for every `S ≥ v10`. -/
theorem module_validIn {S : FeatureSet} (h : v10 ≤ S) (size : Nat) (r : Rng) :
    ValidIn S (Rand.run (module S size) r) :=
  Silmaril.Proofs.Wasm.Tools.Gen.Typed.module_validIn h _ _ _

/-- **The typed generator of `S`**: valid by construction. -/
def typedGen (S : FeatureSet) (h : v10 ≤ S) : Generator (Core.featLang S).toLang where
  run r n := Rand.run (module S n) r
  valid r n := module_validIn h n r

/-- The typed generator of `coreModel P H S`. -/
def coreGenT (P : Profile) (H : Type) (S : FeatureSet) (h : v10 ≤ S) :
    Generator (coreModel P H S).toLang :=
  typedGen S h

theorem v10_le_lime1 : v10 ≤ lime1 := leB_iff.mp (by decide)

def v10GenT : Generator (Core.featLang v10).toLang := typedGen v10 le_rfl
def v20GenT : Generator (Core.featLang v20).toLang := typedGen v20 v10_le_v20
def v30GenT : Generator (Core.featLang v30).toLang :=
  typedGen v30 (le_trans v10_le_v20 v20_le_v30)
def lime1GenT : Generator (Core.featLang lime1).toLang := typedGen lime1 v10_le_lime1

/-- The WasmFX instance: CoreFX's module language is `featLang wasmFX`. -/
def fxGenT (P : Profile) (H : Type) : Generator (Silmaril.Wasm.Models.FX.fxModel P H).toLang :=
  typedGen wasmFX (le_trans (le_trans v10_le_v20 v20_le_v30) v30_le_wasmFX)

end Silmaril.Wasm.Tools.Gen.Typed

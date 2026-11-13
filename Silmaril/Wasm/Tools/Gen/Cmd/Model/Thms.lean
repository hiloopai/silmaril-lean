module

public import Silmaril.Wasm.Tools.Gen.Cmd.Model.Defs

/-!
# The flag-selected models, located in the lattice

* `default_le_v30`: the default model of `smith` is below Wasm 3.0;
* `mvp_le_v10`: with every 2.0 and 3.0 flag off, the model is below Wasm 1.0;
* `v10_le_mvp`: and above it, so these flags select exactly Wasm 1.0.

Kernel-checked by `decide` over the capability list (`FeatureSet.leB`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Model

open Silmaril.Wasm.Models

theorem default_le_v30 : FeatureSet.leB default v30 = true := by decide

theorem mvp_le_v10 : FeatureSet.leB (model mvpFlags 1) v10 = true := by decide

theorem v10_le_mvp : FeatureSet.leB v10 (model mvpFlags 1) = true := by decide

end Silmaril.Wasm.Tools.Gen.Cmd.Model

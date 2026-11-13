module

public import Silmaril.Wasm.Tools.Component.Features.Defs

/-!
# `--features` for components: theorems

* `toCFlags_default`, `toCFlags_all`: the projection of wasmparser's default set and of
  `all` are the validator's `CFlags.default` and `CFlags.all`;
* `parseFeatures` itself is tested (`tools/wasm-tools/tests/compval/args.sh`): string
  splitting does not reduce in the kernel;
* `applyAll_nil`: without `--features` the set is the default;
* `applyAll_all`: `--features all` gives every flag, so the validator runs at `CFlags.all`;
* `wasm1_no_component`: `--features wasm1` turns the component model off (`toCFlags` is
  `none`; upstream then rejects every component);
* `disable_cm_async`: `-f -cm-async` gives the default without 🔀.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Features

open Silmaril.Wasm.Tools.Component.Validate (CFlags)

theorem toCFlags_default : toCFlags default = some CFlags.default := by decide

theorem toCFlags_all : toCFlags all = some CFlags.all := by decide


theorem applyAll_nil : applyAll [] = default := rfl

theorem applyAll_all : toCFlags (applyAll [[.enable all]]) = some CFlags.all := by decide

theorem wasm1_no_component : toCFlags (applyAll [[.reset wasm1]]) = none := by decide

theorem disable_cm_async :
    toCFlags (applyAll [[.disable (bitsOf "cm_async")]]) =
      some ⟨{ Silmaril.Wasm.Component.Features.p3 with async_ := false }, false⟩ := by decide

end Silmaril.Wasm.Tools.Component.Features

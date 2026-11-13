module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Proofs.Wasm.Resource.Handle.Basic

@[expose] public section

/-!
# Handle protocols: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Handle.Basic`.

* Blame: `handleStep_client_alloc`, `handleStep_provider_use`, `handleStep_provider_free`
  (environment events are never rejected), `clientSpec_oTotal`, `providerSpec_oTotal`.
* `providerSpec_importNeutral`; **`provider_models`**: the provider verification condition gives
  `Models (protoLogic …) (wasmSem P) p (providerSpec ja ju jf)`, every profile.
* **`clientSpec_of_neverCall`**: a program that never calls `use` and `free` satisfies the client
  sentence, in any semantics.
-/

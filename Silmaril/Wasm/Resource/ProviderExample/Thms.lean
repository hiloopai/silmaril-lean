module

public import Silmaril.Wasm.Resource.ProviderExample.Defs
public import Silmaril.Proofs.Wasm.Resource.ProviderExample.Basic

@[expose] public section

/-!
# A verified handle provider: results

Proofs in `Silmaril.Proofs.Wasm.Resource.ProviderExample.Basic`. Every profile.

* `slot_alloc_valid`, `slot_use_valid`, `slot_free_valid`: the three exports of a single-slot
  provider meet their provider specifications (`provSpec`) in every protocol state, through the
  every-run program logic (`FSpecAt.of_body`, `HWP.if_`, `HWP.block`, `Wp.unreachable`,
  `Wp.globalGet`, `Wp.globalSet`), under every host.
* `slot_provSat`: the provider verification condition `ProvSat` with the invariant `slotInv`,
  for every instance of the shape `SlotShape`; `slot_models`: the provider handle sentence
  for every such instance (`provider_models`).
* `slotI_shape`: the instance of the real Core 3.0 module `provSlot`, computed by kernel
  evaluation of silmaril-lean's validation and instantiation, has the slot shape.
* **`provSlot_provider`**: `provSlot` meets the provider handle sentence
  `providerSpec slotAlloc slotUse slotFree` over `wasmSem P`, for every profile `P`: `alloc`
  never hands out a live handle.
-/

module

public import Silmaril.Raw.Wasm.Versions.V2.ToCore.InstantiationOnce

/-!
# Wasm 2.0 instantiation against Core 3.0 single allocation

The public header of `Silmaril/Raw/Wasm/Versions/V2/ToCore/InstantiationOnce.lean` (new, not
copied): `Silmaril.Wasm.V2.Execution.Once.instantiate_sim_once` is the copied `instantiate_sim`
without `InstantiationBounds.noGlobals`, against `CoreInstantiateOnce`, the relational form of
silmaril-lean's `instantiateOnce?` (each global allocated once). `coreInstantiateOnce_of_nil`
identifies it with the spec's `$instantiate` on modules without globals.
-/

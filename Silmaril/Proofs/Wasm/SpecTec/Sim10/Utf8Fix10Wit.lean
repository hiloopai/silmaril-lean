module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Name

/-!
# The 1.0 `$utf8` erratum at round 6's observation: the invocation of `"add"` is typed

Round 6 observed that the kernel's typing check of the invocation of silmaril's
`addModule`, which exports its function under `"add"`, fails, and round 7 proved that no
configuration over its store is typed in `simEnv10 B` or `simEnv10T B`
(`Name10.not_typed10_add_invoke`). With the erratum the same configuration is typed:

* **`typed10U_add`**: the invocation of `add` on `1, 2`, over the store `prepare?` allocates for
  `addModule` in the empty store, is `Typed10` in `utf8Env10T B` for every `B` (kernel
  evaluation of the type checker, as round 6's `typed10_addE` for the empty name);
* **`add_typed_iff_erratum`**: it is typed in `utf8Env10T B` and not in `simEnv10T B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Valid (invokeCfg10)
open Silmaril.Wasm.SpecTec.Sim10.Name10 (addStoreN not_typed10_add_invoke)
open Silmaril.Wasm.SpecTec.Sim10.InstWitness10 (addArgs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The invocation of the export `"add"` is typed with the erratum** (kernel evaluation). -/
theorem typed10U_add (B : Builtins) :
    Typed10 (utf8Env10T B) Empty.elim (invokeCfg10 addStoreN addArgs ⟨0⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

/-- **The erratum is what makes it typed.** -/
theorem add_typed_iff_erratum (B : Builtins) :
    Typed10 (utf8Env10T B) Empty.elim (invokeCfg10 addStoreN addArgs ⟨0⟩) ∧
      ¬ Typed10 (simEnv10T B) Empty.elim (invokeCfg10 addStoreN addArgs ⟨0⟩) :=
  ⟨typed10U_add B, (not_typed10_add_invoke B).2⟩

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

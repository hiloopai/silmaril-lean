module

public import Silmaril.Wasm.Jco.Real.Valid.Thms
public import Silmaril.Wasm.Versions.Thms
public import Silmaril.Proofs.Wasm.Jco.Real.ValidAllW

/-!
# Validation of the adaptor module for every world

`Silmaril.Wasm.Jco.Real.Valid` checks `adaptorLime md` on litmus worlds by kernel evaluation and
freezes the general statement as `AdaptorLimeValid`. This module proves the general
statement with a corrected index bound, through Lime1 validation:

* **`adaptorLime_limeValid`**: `adaptorLime md` is a valid Lime1 module
  (`Silmaril.Wasm.Lime1.Validation.ModuleValid`) when the imported names are distinct, no world
  function is named `cabi_realloc`, every world function has at most `2^32 - 3` flat parameters,
  and `2 * |world| + 2 < 2^32`.
* **`adaptorLime_valid_of_bound`**: under the same hypotheses its Core 3.0 image validates
  (`Lime1.Validation.ModuleValid.toCore`, the copied Lime1 → Core 3.0 validation theorem).
* **`adaptorLimeW_limeValid`**, **`adaptorLimeW_valid`**: the same for `adaptorLimeW md`, the
  multi-value adaptor with typed locals, when moreover every wide result has fewer than
  `2^32 - 2 - |flat params|` fields. This is the general form of `adaptorLimeW_exWide_valid` and
  settles the `i64` wide-result encoding issue: with locals typed by `mvShimT` every `local.set`
  of a field and every store (packed `i32` stores, `i64.store`, float stores) is well typed,
  for every record of scalars. The untyped encoding stays refuted
  (`adaptorLimeWUntyped_exWide_invalid`).
* `adaptorLime_valid_restricted`: hence `AdaptorLimeValid` holds on every world with
  `2 * |world| + 2 < 2^32`.

**The bound.** The shim of world function `i` has type index and function index
`|world| + 2 + i`, up to `2 * |world| + 1`. `mkIdx` reduces indices modulo `2^32`, so the
hypothesis `|world| + 2 < 2^32` of `AdaptorLimeValid` does not keep these indices in
range: for `2^31 - 1 ≤ |world| < 2^32 - 2` the last shims point at the wrong types. The frozen
statement is not refuted here (that needs a world of `2^31` functions); it is restated with
`2 * |world| + 2 < 2^32`, under which it is proved. No other hypothesis changed.

The proof (`Silmaril.Proofs.Wasm.Jco.Real.ValidAll`) types each function body with backward
typing steps of Lime1's instruction judgment, after showing that the function types of the
module context are the module's types (`funcs_eq`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm

/-- **`adaptorLime md` is a valid Lime1 module** (corrected index bound). -/
theorem adaptorLime_limeValid (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    Lime1.Validation.ModuleValid (adaptorLime md) :=
  Silmaril.Proofs.Wasm.Jco.Real.ValidAll.adaptorLime_limeValid md hn hr hp hw

/-- **The Core 3.0 image of `adaptorLime md` validates** for every world with distinct names
and the corrected index bound. -/
theorem adaptorLime_valid_of_bound (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    Validation.ModuleValid (adaptorLime md).toCore :=
  Lime1.Validation.ModuleValid.toCore (adaptorLime_limeValid md hn hr hp hw)

/-- The conclusion of `AdaptorLimeValid` for every world that also has
`2 * |world| + 2 < 2^32`. -/
theorem adaptorLime_valid_restricted (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (_ : md.world.length + 2 < 2 ^ 32) (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    Validation.ModuleValid (adaptorLime md).toCore :=
  adaptorLime_valid_of_bound md hn hr hp hw


/-- **`adaptorLimeW md` (multi-value style, typed locals) is a valid Lime1 module.** -/
theorem adaptorLimeW_limeValid (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hq : ∀ s ∈ md.world, ∀ ts ns, wideOf s.result = some (ts, ns) →
      (flatParams s.params).length + ts.length + 2 < 2 ^ 32)
    (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    Lime1.Validation.ModuleValid (adaptorLimeW md) :=
  Silmaril.Proofs.Wasm.Jco.Real.ValidAll.adaptorLimeW_limeValid md hn hr hp hq hw

/-- **The Core 3.0 image of `adaptorLimeW md` validates**: the `i64` wide-result encoding issue
is fixed by the typed locals, for every world. -/
theorem adaptorLimeW_valid (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hq : ∀ s ∈ md.world, ∀ ts ns, wideOf s.result = some (ts, ns) →
      (flatParams s.params).length + ts.length + 2 < 2 ^ 32)
    (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    Validation.ModuleValid (adaptorLimeW md).toCore :=
  Lime1.Validation.ModuleValid.toCore (adaptorLimeW_limeValid md hn hr hp hq hw)

end Silmaril.Wasm.Jco.Real

/--
info: 'Silmaril.Wasm.Jco.Real.adaptorLime_valid_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Real.adaptorLime_valid_of_bound

/--
info: 'Silmaril.Wasm.Jco.Real.adaptorLimeW_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Jco.Real.adaptorLimeW_valid

module

public import Silmaril.Wasm.Jco.Real.Typed.Defs
public import Silmaril.Wasm.Jco.Example.Defs
public import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# Validation of the adaptor modules

The adaptor modules `adaptorLime md` (first FFI style, every string encoding) and
`adaptorLimeW md` (multi-value style, typed locals) are Lime1 modules; their Core 3.0 images are
checked here with silmaril's Core 3.0 validator `Validation.validate?`, which is sound
(`validate_sound`) and complete (`validate?_isSome_iff`) for `Validation.ModuleValid`. The checks
are kernel evaluations (`decide +kernel`; no native evaluation).

* **`adaptorLime_exMeta_valid`**: the adaptor of the litmus world (`add`, `echo`; a moving
  `cabi_realloc` with `if`, `select` and `memory.copy`) validates.
* `adaptorLime_exMeta2_valid`, `adaptorLimeW_exMeta2_valid`: a world with `f64`, `s64`,
  `string`, `list<u8>` parameters, a record parameter, a variant result, a `list<u8>` result and
  a function without results; both adaptors validate.
* **`adaptorLimeW_exWide_valid`**: the multi-value adaptor of a function returning a record
  `{s64, u32}` validates (typed locals).
* **`adaptorLimeWUntyped_exWide_invalid`**: the same adaptor with all extra locals declared
  `i32` (the encoding of `XFn.toLime`, as `adaptorLime` encodes its functions) does **not**
  validate. This refutes the untyped encoding for wide results with `i64` fields.
* **`adaptorLime_name_alloc_invalid`**, `adaptorLime_name_realloc_invalid`: `adaptorLime md`
  does not validate for every `md`. A world function named like the allocator is called at the
  allocator's index (`funcIdxOf` takes the first match), and one named `cabi_realloc` duplicates
  an export. So the general statement needs distinct names; it is frozen as
  `AdaptorLimeValid` (open).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm

/-- **The litmus adaptor validates** (Core 3.0). -/
theorem adaptorLime_exMeta_valid : Validation.ModuleValid (adaptorLime Example.exMeta).toCore :=
  Validation.validate_sound (by decide +kernel)

/-- A world exercising more parameter and result types. -/
def exMeta2 : Meta where
  world := [⟨"f", [.val .f64, .val .s64, .string, .bytes], some .bytes⟩,
    ⟨"g", [.val (.record [.u8, .f32])], some (.val (.variant [some .u32, none]))⟩,
    ⟨"h", [], none⟩]

theorem adaptorLime_exMeta2_valid : Validation.ModuleValid (adaptorLime exMeta2).toCore :=
  Validation.validate_sound (by decide +kernel)

theorem adaptorLimeW_exMeta2_valid : Validation.ModuleValid (adaptorLimeW exMeta2).toCore :=
  Validation.validate_sound (by decide +kernel)

/-- A function returning a record `{s64, u32}` (a wide result with an `i64` field). -/
def exMetaWide : Meta where
  world := [⟨"pair", [.val .u32], some (.val (.record [.s64, .u32]))⟩]

/-- **The multi-value adaptor with typed locals validates.** -/
theorem adaptorLimeW_exWide_valid : Validation.ModuleValid (adaptorLimeW exMetaWide).toCore :=
  Validation.validate_sound (by decide +kernel)

/-- The multi-value adaptor with all extra locals declared `i32` (`XFn.toLime`). -/
def adaptorLimeWUntyped (md : Meta) : Lime1.Module :=
  { adaptorLimeW md with
    funcs := (XFnT.ofX (reallocShim md.alloc).toX).toLime (funcIdxOf md) (md.world.length + 1) ::
      (md.world.zipIdx.map fun (s, i) =>
        (exportShimW md s).toLime (funcIdxOf md) (md.world.length + 2 + i)) }

/-- **The untyped encoding of the multi-value shim does not validate.** -/
theorem adaptorLimeWUntyped_exWide_invalid :
    ¬ Validation.ModuleValid (adaptorLimeWUntyped exMetaWide).toCore := by
  rw [← Validation.validate?_isSome_iff]
  decide +kernel

/-- **`adaptorLime` of a world function named like the allocator does not validate.** -/
theorem adaptorLime_name_alloc_invalid :
    ¬ Validation.ModuleValid (adaptorLime ⟨[⟨"alloc", [], none⟩], "alloc"⟩).toCore := by
  rw [← Validation.validate?_isSome_iff]
  decide +kernel

/-- `adaptorLime` of a world function named `cabi_realloc` does not validate. -/
theorem adaptorLime_name_realloc_invalid :
    ¬ Validation.ModuleValid (adaptorLime ⟨[⟨"cabi_realloc", [], none⟩], "alloc"⟩).toCore := by
  rw [← Validation.validate?_isSome_iff]
  decide +kernel

/-- **Statement, refuted** (`not_adaptorLime_valid`; `Silmaril.Wasm.Jco.Real.ValidRange.Thms` proves it below `2^31` functions): `adaptorLime md` validates whenever the imported names (the allocator and
the world's functions) are distinct, no world function is named `cabi_realloc`, and every
function's flat parameters fit in the index space. Evidence: the instances above. -/
def AdaptorLimeValid : Prop :=
  ∀ md : Meta, (importNames md).Nodup → "cabi_realloc" ∉ md.world.map (·.name) →
    (∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32) →
    md.world.length + 2 < 2 ^ 32 →
    Validation.ModuleValid (adaptorLime md).toCore

end Silmaril.Wasm.Jco.Real

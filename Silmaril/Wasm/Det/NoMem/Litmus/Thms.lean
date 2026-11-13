module

public import Silmaril.Wasm.Det.NoMem.Litmus.Defs
public import Silmaril.Wasm.Det.NoMem.Thms
public import Silmaril.Wasm.Det.NoMem.Module.Thms
public import Silmaril.Wasm.Det.Core.Litmus.Thms

/-!
# Litmus tests for the memory-free, float-free subset

Per-function determinism (modulo traps and imports, at **every** profile) where the module is
not in the subset, or not deterministic. Every check is kernel evaluation (`wasm_det`,
`decide +kernel`); no native evaluation.

**`gcMod`** (`Silmaril.Wasm.Det.NoMem.Litmus.Defs`: a GC function `box` calling an import, a
function `twice` calling `box`, a float function `nan`):

* `gcPrep_isSome`: the module validates and instantiates (non-vacuity);
* `box_det`, `twice_det`: `box` and `twice` are deterministic at every profile, although
  `twice` makes nested calls and `box` allocates and calls the import;
* `gc_detModule`: the module restricted to the entries `{0, 1, 3}` is deterministic at every
  profile, at every call state;
* `gc_not_subset`, `nan_not_checked`: the module is not in the subset (`storeB` fails), and the
  per-function check rejects `nan`.

**`startMod`** (a start function computes a global): `startMod_det` (`wasm_det_module`): the
instance, instantiation phase included, is deterministic at every profile; `gc_not_moduleB`:
`gcMod` fails the module check.

**`litMod`** of `Silmaril.Wasm.Det.Core.Litmus` (`one`, `nan`, `set`/`get` on a mutable global):

* `lit_set_det`, `lit_get_det`: the global-writing and global-reading functions are
  deterministic at every profile (they are not store-free, so `det_leaf` does not apply);
* `lit_contrast`: at every profile with the specification's NaN semantics, the module restricted
  to `{one, set, get}` is deterministic, while the whole module is not
  (`Silmaril.Wasm.Det.Core.Litmus.not_detModule`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NoMem.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.NoMem
open Silmaril.Wasm.Numerics (Profile)

/-! ## `gcMod` -/

/-- `gcMod` validates and instantiates. -/
theorem gcPrep_isSome : gcPrep.isSome = true := by decide +kernel

/-- The instance has four functions: the import and the three defined functions. -/
theorem gcStore_funcs : gcStore.funcs.length = 4 := by decide +kernel

/-- The import is a host function. -/
theorem gcStore_import : (gcStore.funcs[0]?.map fun fi => match fi.code with
    | .host _ => true | .wasm _ => false) = some true := by decide +kernel

/-- **`box` is deterministic**, every profile: it allocates a struct and calls the import. -/
theorem box_det (P : Profile) : DetFn P gcStore 1 := by wasm_det

/-- **`twice` is deterministic**, every profile: it calls `box` twice. -/
theorem twice_det (P : Profile) : DetFn P gcStore 3 := by wasm_det

/-- Every invocation of `box`, typed or not. -/
theorem box_detCall (P : Profile) (vs : List Val) : DetCall P gcStore 1 vs := by wasm_det

/-- **The module restricted to `{0, 1, 3}` is deterministic** at every call state. -/
theorem gc_detModule (P : Profile) : DetModule P (· ∈ [0, 1, 3]) gcStore := by wasm_det

/-- **The module is not in the subset**: `nan` uses a float instruction. -/
theorem gc_not_subset : storeB gcStore = false := by decide +kernel

/-- The per-function check rejects `nan`. -/
theorem nan_not_checked : detFnB gcStore 2 = false := by decide +kernel

/-- The direct-call closure of `twice`. -/
theorem twice_clos : clos gcStore 3 = [3, 1, 0] := by decide +kernel

/-! ## Instances -/

/-- **`startMod` is a deterministic instance**, start function included, every profile. -/
theorem startMod_det (P : Profile) (Entry : Nat → Prop) : DetInst P (instC₀ startMod) Entry := by
  wasm_det_module

/-- The start function is part of the instantiation configuration (non-vacuity). -/
theorem startMod_start : (instC₀ startMod).code.length = 1 := by decide +kernel

/-- `gcMod` fails the module check (its function `nan` uses floats). -/
theorem gc_not_moduleB : moduleB gcMod = false := by decide +kernel

/-! ## `litMod` -/

open Silmaril.Wasm.Det.Core.Litmus in
/-- **`set` (`global.set`) is deterministic**, every profile. -/
theorem lit_set_det (P : Profile) : DetFn P litStore 2 := by wasm_det

open Silmaril.Wasm.Det.Core.Litmus in
/-- **`get` (`global.get`) is deterministic**, every profile. -/
theorem lit_get_det (P : Profile) : DetFn P litStore 3 := by wasm_det

open Silmaril.Wasm.Det.Core.Litmus in
/-- **A deterministic sub-module of a nondeterministic module**: with the specification's NaN
semantics, `litMod` restricted to `{one, set, get}` is deterministic, the whole module is not. -/
theorem lit_contrast {P : Profile} (hP : P.nan = .spec) :
    DetModule P (· ∈ [0, 2, 3]) litStore ∧ ¬ DetModule P litEntry litStore :=
  ⟨by wasm_det, not_detModule hP⟩

end Silmaril.Wasm.Det.NoMem.Litmus

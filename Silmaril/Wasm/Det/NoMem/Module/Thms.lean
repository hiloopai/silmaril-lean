module

public import Silmaril.Wasm.Det.NoMem.Module.Defs
public import Silmaril.Wasm.Det.NoMem.Thms
public import Silmaril.Proofs.Wasm.Det.NoMem.Module

/-!
# The memory-free, float-free subset: soundness of the module check

* `detInst_of_moduleB`: a module passing `moduleB` is a **deterministic instance** modulo traps
  and imports at every profile: its instantiation configuration `instC₀ m` (segment
  initialisation and start function) is deterministic, and the module is deterministic for every
  set of entries from every store at which instantiation finishes without trapping;
* `detModule_of_moduleB`: the allocated store is a deterministic module (every entry set);
* `detFn_of_moduleFnB`: the per-function check in the allocated store.

Tactic `wasm_det_module`: closes `DetInst P (instC₀ m) Entry` and `DetFn P (instStore m) a` for a
concrete module by kernel evaluation of `moduleB` / `moduleFnB`.

Proofs: `Silmaril.Proofs.Wasm.Det.NoMem.Module`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **A module passing `moduleB` is a deterministic instance**, at every profile. -/
theorem detInst_of_moduleB {P : Profile} {m : Module} {Entry : Nat → Prop}
    (h : moduleB m = true) : DetInst P (instC₀ m) Entry :=
  Silmaril.Proofs.Wasm.Det.NoMem.detInst_of_moduleB h

/-- The allocated store of a module passing `moduleB` is a deterministic module. -/
theorem detModule_of_moduleB {P : Profile} {m : Module} {Entry : Nat → Prop}
    (h : moduleB m = true) : DetModule P Entry (instStore m) := by
  simp only [moduleB, Bool.and_eq_true] at h
  exact detModule_of_storeB h.1.2

/-- **The per-function check in a module.** -/
theorem detFn_of_moduleFnB {P : Profile} {m : Module} {a : Nat} (h : moduleFnB m a = true) :
    DetFn P (instStore m) a :=
  detFn_of_detFnB h

/-- Closes `DetInst P (instC₀ m) Entry`, `DetModule P Entry (instStore m)` or
`DetFn P (instStore m) a` for a concrete module by kernel evaluation. -/
macro "wasm_det_module" : tactic => `(tactic| first
  | exact Silmaril.Wasm.Det.NoMem.detInst_of_moduleB (by decide +kernel)
  | exact Silmaril.Wasm.Det.NoMem.detModule_of_moduleB (by decide +kernel)
  | exact Silmaril.Wasm.Det.NoMem.detFn_of_moduleFnB (by decide +kernel))

end Silmaril.Wasm.Det.NoMem

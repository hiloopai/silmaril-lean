module

public import Silmaril.Wasm.Jco.Meta.Defs
public import Silmaril.Wasm.Jco.Adaptor.Defs

/-!
# Thin-wrapper recognition over the canonical ABI with memory

The monadic construction `Silmaril.Wasm.Jco.wrap` adds an adaptor for two
reasons. Under the C convention a string or `list<u8>` result is written to a
caller-allocated out-pointer, and the allocator is `alloc(size, align)`
rather than the canonical `realloc(old, old_size, align, size)`. A module
needs no adaptor code when neither reason applies. That is the case when no
world function returns through memory and the module exports a
canonical-ABI `realloc`. The wrapper is then *thin*: `canon lift`s of the
module's own exports, with the module's `realloc`.

* `thinComp md r`: the thin wrapper, with no adaptor functions and only
  `core` references. The `realloc` is the export `r` of the module.
* `Meta.thinOk md`: no world function returns through memory.
  `recognizeThin md r` is the partial recognizer.
* `Meta.memFree md`: no parameter or result goes through memory, so the
  `realloc` is never called. This is a stricter variant.
* `ReallocAgrees M md r`: the module's `r` answers the canonical ABI's calls
  `realloc(0, 0, 1, n)` as the C allocator answers `alloc(n, 1)`. This is a
  semantic condition. It cannot be recognized from the metadata.
* `canonSpec M world r`: FFI style 2, the canonical convention. The module
  exports canonical-ABI functions and a `realloc` itself.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

/-- **The thin wrapper**: the `canon lift` of the module's export of each
world function, with the module's `realloc` export `r`; no adaptor. -/
def thinComp (md : Meta) (r : String) : Comp :=
  { lifts := md.world.map fun s => ⟨s, .core s.name, .core r⟩ }

/-- No world function returns through memory (no out-pointer to adapt). -/
def Meta.thinOk (md : Meta) : Bool := md.world.all fun s => !inMem s.result

/-- A parameter type passed flat (not through memory). -/
def PTy.memFree : PTy → Bool
  | .val _ => true
  | _ => false

/-- No parameter or result goes through memory: `realloc` is never called. -/
def Meta.memFree (md : Meta) : Bool :=
  md.world.all fun s => s.params.all PTy.memFree && !inMem s.result

/-- **Thin-wrapper recognition** (partial): the thin wrapper when no world
function returns through memory. -/
def recognizeThin (md : Meta) (r : String := "cabi_realloc") : Option Comp :=
  if md.thinOk then some (thinComp md r) else none

/-- The module's `realloc` export `r` answers the canonical ABI's allocation
calls as the C convention's allocator. -/
def ReallocAgrees (M : CoreInst) (md : Meta) (r : String) : Prop :=
  ∀ n : Nat, M.call r [i32n 0, i32n 0, i32n 1, i32n n] = M.call md.alloc [i32n n, i32n 1]

/-- **The canonical convention** (FFI style 2): the module exports each world
function at the canonical ABI, and a `realloc` export `r`. -/
def canonSpec (M : CoreInst) (world : List Sig) (r : String) (name : String)
    (vs : List PVal) : RM M.St (Option PVal) :=
  match world.find? (·.name == name) with
  | some s => canonCall M (M.call r) (M.call s.name) s vs
  | none => RM.fail

end Silmaril.Wasm.Jco

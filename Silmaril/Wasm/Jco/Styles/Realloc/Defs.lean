module

public import Silmaril.Wasm.Jco.Styles.XAdaptor.Defs

/-!
# `realloc` with a nonzero old pointer

The `cabi_realloc` shim of `wrap` (`reallocShim`) is `alloc(size, align)`. It ignores the old
pointer, which is correct only for the calls `realloc(0, 0, align, size)` of the first fragment.
Transcoding strings (`utf16`, `latin1+utf16`; `Silmaril.Wasm.Jco.Styles.Enc`) also shrinks and
grows blocks: `realloc(ptr, old_size, align, new_size)` with `ptr ≠ 0` must return a block whose
first `min(old_size, new_size)` bytes are those of the old block.

* `reallocShimX alloc`: the adaptor's `cabi_realloc` for a module with only a C allocator
  `alloc(size, align)` (no `free`, no `realloc`):

  ```
  local.get 0  i32.eqz
  if   local.get 3  local.get 2  call alloc
  else local.get 3  local.get 2  call alloc  local.set 4
       local.get 4  local.get 0
       local.get 1  local.get 3  local.get 1  local.get 3  i32.lt_u  select   ;; min
       memory.copy  local.get 4
  end
  ```

  The old block is not freed (the C convention has no `free`); it leaks.
* `reallocEmu M alloc`: what the shim computes, as a core function: `alloc(size, align)` when
  the old pointer is 0, and otherwise `alloc(size, align)` followed by a copy (`memmove`) of
  `min(old_size, size)` bytes from the old block.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

/-- The `cabi_realloc` shim with a nonzero old pointer: allocate and copy. -/
def reallocShimX (alloc : String) : XFn :=
  { params := 4, locals := 1,
    body := [.base (.localGet 0), .i32Eqz, .ifElse (some (.int .i32))
      [.base (.localGet 3), .base (.localGet 2), .base (.call alloc 2)]
      [.base (.localGet 3), .base (.localGet 2), .base (.call alloc 2), .base (.localSet 4),
        .base (.localGet 4), .base (.localGet 0),
        .base (.localGet 1), .base (.localGet 3), .base (.localGet 1), .base (.localGet 3),
        .i32LtU, .select, .memCopy, .base (.localGet 4)]] }

variable (M : CoreInst)

/-- Copy `n` bytes from `src` to `dst` (`memory.copy`). -/
def copyBytes (dst src n : Nat) : RM M.St Unit := do
  let bs ← M.load src n
  M.store dst bs

/-- **The emulated `realloc`** of a C allocator, on `i32` arguments. -/
def reallocEmu (alloc : String) (old os al ns : BitVec 32) : RM M.St (List Flat) :=
  if old == 0 then M.call alloc [Flat.i32 ns, Flat.i32 al]
  else do
    let r ← M.call alloc [Flat.i32 ns, Flat.i32 al]
    let p ← RM.ofOption (single32? r)
    copyBytes M p.toNat old.toNat (min os.toNat ns.toNat)
    pure [Flat.i32 p]

/-- The emulated `realloc` as a core function (other arguments trap). -/
def reallocEmuF (alloc : String) : List Flat → RM M.St (List Flat)
  | [⟨.int .i32, old⟩, ⟨.int .i32, os⟩, ⟨.int .i32, al⟩, ⟨.int .i32, ns⟩] =>
    reallocEmu M alloc old os al ns
  | _ => RM.fail

end Silmaril.Wasm.Jco

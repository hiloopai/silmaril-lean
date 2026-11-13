module

public import Silmaril.Wasm.Jco.Adaptor.Defs
public import Silmaril.Wasm.Jco.Meta.Defs

/-!
# The monadic construction: core module + metadata → wrapper component with an adaptor

`wrap md` is the component a jco-style toolchain builds from a core module that follows the C
convention of `Silmaril.Wasm.Jco.Meta`, **for every metadata `md`** (the construction is total):

* the generated **adaptor module** `adaptorOf md` has
  * function 0, `cabi_realloc`: the canonical ABI's `realloc(old, old_size, align, size)`, which
    the lifts call as `realloc(0, 0, 1, len)`, implemented by `M`'s `alloc(size, align)`
    (`reallocShim`). It ignores `old`/`old_size`: the fragment never reallocates (only UTF-8 to
    UTF-8 copies and `list<u8>`).
  * function `i + 1`, the export shim of world function `i` (`exportShim`): it forwards the flat
    parameters to `M`'s export; for a string or `list<u8>` result it first allocates an out-pointer
    with `alloc(8, 4)`, passes it as the last argument, and returns it as the canonical ABI's
    result pointer.
* the lifts: world function `i` is `canon lift` of adaptor function `i + 1`, with `M`'s memory and
  the adaptor's `cabi_realloc`.

`Silmaril.Wasm.Jco.Wrap.Thms` proves that the component's behaviour at its world is `md.spec M`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

/-- `local.get 0`, …, `local.get (n - 1)`. -/
def gets (n : Nat) : List AInstr := (List.range n).map .localGet

/-- The adaptor's `cabi_realloc(old, old_size, align, size)`: `alloc(size, align)`. -/
def reallocShim (alloc : String) : AFn :=
  { params := 4, body := [.localGet 3, .localGet 2, .call alloc 2] }

/-- The body of the export shim of a function with an out-pointer: `n` flat parameters, local
`n` holds the out-pointer. -/
def outShimBody (alloc name : String) (n : Nat) : List AInstr :=
  [.i32Const 8, .i32Const 4, .call alloc 2, .localSet n] ++ gets (n + 1) ++
    [.call name (n + 1), .localGet n]

/-- The export shim of a world function. -/
def exportShim (md : Meta) (s : Sig) : AFn :=
  let n := (flatParams s.params).length
  if inMem s.result then { params := n, locals := 1, body := outShimBody md.alloc s.name n }
  else { params := n, body := gets n ++ [.call s.name n] }

/-- The generated adaptor module. -/
def adaptorOf (md : Meta) : AMod :=
  ⟨("cabi_realloc", reallocShim md.alloc) :: md.world.map fun s => (s.name, exportShim md s)⟩

/-- The lifts of world functions `k, k + 1, …`. -/
def liftsFrom : Nat → List Sig → List Lift
  | _, [] => []
  | k, s :: ss => ⟨s, .adapt (k + 1), .adapt 0⟩ :: liftsFrom (k + 1) ss

/-- **The monadic construction**: the wrapper component of a core module with metadata `md`. -/
def wrap (md : Meta) : Comp := { adaptor := adaptorOf md, lifts := liftsFrom 0 md.world }

end Silmaril.Wasm.Jco

module

public import Silmaril.Wasm.Jco.Basic.Defs

/-!
# The canonical ABI of the first fragment, over a core instance's memory

`canon lift` of a core function with the options `(memory m) (realloc r)
string-encoding=utf8`, for signatures of the fragment of `Silmaril.Wasm.Jco.Basic` (memory-free
types, `string`, `list<u8>`), following the component-model reference `definitions.py`
(`a25fc0b`; the transcription of `Silmaril/Raw/Wasm/Component/**`):

* `lowerParam`: a memory-free value is type checked and lowered flat (`ValTy.lower`; ill-typed
  values trap). A string (`store_string_copy`, UTF-8 to UTF-8) or a `list<u8>`
  (`store_list_into_range`) traps if too long (`MAX_STRING_BYTE_LENGTH = 2^31 - 1` bytes; a list
  below `2^32` bytes), calls `realloc(0, 0, 1, len)`, stores the bytes at the returned pointer
  (trapping out of bounds) and passes `(ptr, len)`. The alignment check of the pointer is
  vacuous at alignment 1.
* `liftResult`: no result needs no core values; a memory-free result is lifted flat
  (`ValTy.lift`, which also checks the core types and consumes all values); a string or list
  result arrives as one `i32` pointer `rp` (more than `MAX_FLAT_RESULTS = 1` flat values): it
  traps unless `rp` is 4-aligned, reads the `(ptr, len)` pair at `rp` (trapping out of bounds),
  reads the `len` bytes at `ptr` and, for a string, decodes them as UTF-8 (trapping on invalid
  UTF-8).
* `canonCall realloc callee sig vs`: lower the arguments, call the callee, lift the result.

The memory is the instance `M`'s; `realloc` and `callee` are arbitrary computations over `M`'s
state (a core export of `M`, or an adaptor function that calls `M`). Not modelled: spilling of
more than `MAX_FLAT_PARAMS` parameters (see `Sig.Ok`), `post-return`, NaN canonicalisation of
floats (the ABI layer carries bit patterns), other string encodings, and the task/thread
machinery of the reference (a synchronous lift of a function without imports runs straight
through; `Silmaril.Wasm.Component.Reference.Sound` proves this for the scalar fragment).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy Val)

variable (M : CoreInst)

/-- Store a byte string through a realloc-style allocator: `realloc(0, 0, 1, len)`, then the
bytes at the returned pointer; the flat result is `(ptr, len)`. -/
def lowerBytes (realloc : List Flat → RM M.St (List Flat)) (limit : Nat) (bs : List UInt8) :
    RM M.St (List Flat) := do
  RM.check (decide (bs.length ≤ limit))
  let r ← realloc [i32n 0, i32n 0, i32n 1, i32n bs.length]
  let p ← RM.ofOption (single32? r)
  M.store p.toNat bs
  pure [Flat.i32 p, i32n bs.length]

/-- Canonical lowering of one parameter. -/
def lowerParam (realloc : List Flat → RM M.St (List Flat)) : PTy → PVal → RM M.St (List Flat)
  | .val t, .val v => do
    RM.check (t.check v)
    pure (t.lower v)
  | .string, .string s => lowerBytes M realloc maxStringBytes (utf8 s)
  | .bytes, .bytes bs => lowerBytes M realloc maxListBytes bs
  | _, _ => RM.fail

/-- Canonical lowering of a parameter list (arity mismatches trap). -/
def lowerParams (realloc : List Flat → RM M.St (List Flat)) :
    List PTy → List PVal → RM M.St (List Flat)
  | [], [] => pure []
  | t :: ts, v :: vs => do
    let a ← lowerParam M realloc t v
    let b ← lowerParams realloc ts vs
    pure (a ++ b)
  | _, _ => RM.fail

/-- The bytes a `(ptr, len)` pair at the 4-aligned address `rp` points to. -/
def readPair (rp : BitVec 32) : RM M.St (List UInt8) := do
  RM.check (rp.toNat % 4 == 0)
  let w ← M.load rp.toNat 8
  let p ← RM.ofOption (ofLe32 (w.take 4))
  let l ← RM.ofOption (ofLe32 (w.drop 4))
  M.load p.toNat l.toNat

/-- Decode UTF-8 bytes (trap if invalid). -/
def decodeUtf8 (bs : List UInt8) : Option String := String.fromUTF8? ⟨bs.toArray⟩

/-- Canonical lifting of a function's result from its flat core results. -/
def liftResult : Option PTy → List Flat → RM M.St (Option PVal)
  | none, [] => pure none
  | some (.val t), xs =>
    match t.lift xs with
    | some (v, []) => pure (some (.val v))
    | _ => RM.fail
  | some .string, [x] => do
    let rp ← RM.ofOption (asI32? x)
    let bs ← readPair M rp
    let s ← RM.ofOption (decodeUtf8 bs)
    pure (some (.string s))
  | some .bytes, [x] => do
    let rp ← RM.ofOption (asI32? x)
    let bs ← readPair M rp
    pure (some (.bytes bs))
  | _, _ => RM.fail

/-- `canon lift` of `callee` at `sig`, with `realloc` and `M`'s memory: lower, call, lift. -/
def canonCall (realloc callee : List Flat → RM M.St (List Flat)) (sig : Sig) (vs : List PVal) :
    RM M.St (Option PVal) := do
  let xs ← lowerParams M realloc sig.params vs
  let rs ← callee xs
  liftResult M sig.result rs

end Silmaril.Wasm.Jco

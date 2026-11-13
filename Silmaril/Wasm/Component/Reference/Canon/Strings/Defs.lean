module

public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs
public import Silmaril.Wasm.Component.Reference.ABI.String.Defs

/-!
# Canonical ABI string load and store as specification programs

The string functions of REF `design/mvp/canonical-abi/definitions.py` at component-model
commit `a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1` (github.com/WebAssembly/component-model),
written in `P E σ` over the memory helpers of `Canon/Context.lean`:

| Lean | REF |
| --- | --- |
| `loadStringFromRange lim q cx ptr tagged` | `load_string_from_range` (L1338-1366) |
| `loadString lim q cx ptr` | `load_string` (L1326-1329) |
| `storeStringIntoRange lim q cx v` | `store_string_into_range` (L1538-1571), L1573-1675 |
| `storeString lim q cx v ptr` | `store_string` (L1533-1536) |

**No string algorithm is re-transcribed here.** The length / alignment / codec choice of
`load_string_from_range` is `ABI.loadRange`, decoding is `ABI.Codec.decode?`, and the store
algorithms are the straight-line `ABI.StorePlan`s built by `ABI.storeStringIntoRange`.
`storeStringIntoRange` only *interprets* the plan's `ABI.StoreStep`s left to right with a current
pointer (`runStoreStep`):

| `ABI.StoreStep` | effect here |
| --- | --- |
| `allocate al n` | `ptr ← allocate cx al.bytes n` (REF `cx.allocate`, late-bound realloc) |
| `reallocate old al n` | `ptr ← reallocate cx ptr old al.bytes n` (REF `cx.reallocate`) |
| `trapIfMisaligned al` | `trap_if(ptr != align_to(ptr, al))`, reason `unalignedPointer` |
| `trapIfOutOfBounds n` | `trap_if(ptr + n > len(memory))` (`checkInBounds`), reason `outOfBounds` |
| `write off bs` | `writeMem cx (ptr + off) bs` |
| `inflateLatin1 n` | read `[ptr, ptr + 2n)`, apply `ABI.memInflateLatin1 · 0 n`, write it back |
| `deflateUtf16 n` | read `[ptr, ptr + 2n)`, apply `ABI.memDeflateUtf16 · 0 n`, write it back |

The in-place loops are performed on the block `[ptr, ptr + 2n)` with the pure loop
functions, so their memory effect is byte for byte that of `ABI.StoreStep.run` whenever the
block is in bounds (it always is after the plan's preceding `trapIfOutOfBounds`;
`Canon/Properties/Strings.lean` proves the agreement with `ABI.StorePlan.run`). REF's single-byte
Python writes are merged into `write` steps by the plan builders, as documented in
`ABI/String.lean`.

## Deviations and non-claims

* D-a: a lifted string is a `Value.StrVal` (the REF tuple plus the pointer width `srcAddr` of
  the memory it was lifted from). Before storing, a UTF-16-tagged `latin1+utf16` count is
  re-tagged for the destination pointer width (`StrVal.retag`); with `q.refUtf16TagBug` the
  raw REF tuple `v.v` is used instead, reproducing REF's decoding of the source tag with the
  destination width (the raw behaviour of `store_string_into_range`).
* D-f: REF asserts the realloc request sizes are `<= REALLOC_I32_MAX` and (in
  `store_string_copy`, and implicitly in the in-place loops) that a string's code-unit hint
  agrees with its text (`ABI.StringValue.Consistent` for the destination width). Both are
  preconditions (`StoreStringPre`), not traps; the programs are total and run the plan regardless.
  `StoreStringPre.of_consistent` (from the lemma
  `ABI.storeStringIntoRange_requestSize_le_reallocI32Max`) discharges `StoreStringPre` for
  consistent strings within `maxStringByteLength`.
* `loadStringFromRange` bounds the byte length by `lim.maxStringBytes` (`Limits.spec` is REF
  `MAX_STRING_BYTE_LENGTH`; `Limits.wasmtime` is wasmtime's larger bound). The quirk argument
  `q` of the load functions is currently unused (no load-side quirk); it is kept for a uniform
  calling convention.
* A decoding failure traps `invalidUtf8` (UTF-8 codec) or `invalidUtf16` (UTF-16 codec); the
  Latin-1 codec never fails. REF has one `trap()` for both.
* `loadString`/`storeString` read/write the `(ptr, len)` pair with `readMem`/`writeMem` of
  pointer-sized little-endian words (REF `load_int`/`store_int`, which perform no checks: the
  enclosing `load`/`store` has bounds-checked the slot). An out-of-range slot traps
  `outOfBounds` here instead of raising a Python exception; unreachable for checked callers.
* Nothing about the result of these programs is proved here; see
  `Canon/Properties/Strings.lean` for the agreement with the pure plans.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type}

/-! ## Pointer-sized words -/

/-- Little-endian unsigned value of a byte string (REF `int.from_bytes(.., 'little')`). -/
def strWordOfBytes (bs : ByteArray) : Nat :=
  bs.toList.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The `n` little-endian bytes of `v mod 2^(8n)` (REF `int.to_bytes(v, n, 'little')`). -/
def strWordBytes (n v : Nat) : ByteArray :=
  ((List.range n).map fun i => UInt8.ofNat (v / 256 ^ i)).toByteArray

/-! ## Loading -/

/-- The trap reason of a failed decode with codec `c` (the Latin-1 codec never fails). -/
def decodeTrap : ABI.Codec → TrapReason
  | .utf8 => .invalidUtf8
  | .utf16 | .latin1 => .invalidUtf16

/-- REF `load_string_from_range(cx, ptr, tagged_code_units)` (L1338-1366): the byte length,
alignment and codec are `ABI.loadRange`; then `trap_if(byte_length > MAX_STRING_BYTE_LENGTH)`
(bound `lim.maxStringBytes`), `trap_if(ptr != align_to(ptr, alignment))`,
`trap_if(ptr + byte_length > len(memory))`, and decode with `ABI.Codec.decode?` (trap on
failure). The result carries the REF tuple `(s, cx.opts.string_encoding, tagged_code_units)`
and the memory's pointer width (D-a). -/
def loadStringFromRange (lim : Limits) (_q : Quirks) (cx : LiftLowerContext E)
    (ptr tagged : Nat) : P E σ StrVal := do
  let a ← ptrType cx
  let r := ABI.loadRange cx.opts.encoding a tagged
  trapIf (decide (r.byteLength > lim.maxStringBytes)) .stringTooLong
  trapIf (decide (ptr ≠ ABI.alignTo ptr r.alignment)) .unalignedPointer
  checkInBounds cx ptr r.byteLength
  let bytes ← readMem cx ptr r.byteLength
  match r.codec.decode? bytes.toList with
  | none => trap (decodeTrap r.codec)
  | some s => pure ⟨⟨s, cx.opts.encoding, tagged⟩, a⟩

/-- REF `load_string(cx, ptr)` (L1326-1329): load the pointer-sized `begin` and
`tagged_code_units` words at `ptr` and `ptr + ptr_size`, then `load_string_from_range`. -/
def loadString (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (ptr : Nat) :
    P E σ StrVal := do
  let sz ← ptrSize cx
  let begin ← strWordOfBytes <$> readMem cx ptr sz
  let tagged ← strWordOfBytes <$> readMem cx (ptr + sz) sz
  loadStringFromRange lim q cx begin tagged

/-! ## Storing -/

/-- The REF value stored by `store_string_into_range` into a memory of pointer width `dst`:
the D-a re-tagged value, or under `q.refUtf16TagBug` the raw REF tuple. -/
def storeSource (q : Quirks) (dst : AddrType) (v : StrVal) : ABI.StringValue :=
  if q.refUtf16TagBug then v.v else v.retag dst

/-- The plan executed by `storeStringIntoRange` for destination width `dst`. -/
def storePlanFor (q : Quirks) (enc : ABI.StringEncoding) (dst : AddrType) (v : StrVal) :
    ABI.StorePlan :=
  ABI.storeStringIntoRange enc dst (storeSource q dst v)

/-- The REF assertions of the store algorithms (D-f): the stored value's code-unit hint agrees
with its text for the destination width (REF `assert(dst_byte_length == len(encoded))`, and
the hint the in-place loops rely on), and every realloc request size of the plan is at most
`REALLOC_I32_MAX`. A precondition of `storeStringIntoRange`, not a trap. -/
def StoreStringPre (q : Quirks) (enc : ABI.StringEncoding) (dst : AddrType) (v : StrVal) :
    Prop :=
  (storeSource q dst v).Consistent dst ∧
    ∀ n ∈ (storePlanFor q enc dst v).requestSizes, n ≤ ABI.reallocI32Max

instance (q : Quirks) (enc : ABI.StringEncoding) (dst : AddrType) (v : StrVal) :
    Decidable (StoreStringPre q enc dst v) := by
  unfold StoreStringPre; infer_instance

/-- One `ABI.StoreStep` executed against the memory of `cx` from current pointer `ptr`,
returning the new current pointer (see the module docstring table). Realloc calls pass REF's
exact arguments: `allocate` is `cx.allocate(alignment, size)`, `reallocate` is
`cx.reallocate(ptr, old_size, alignment, new_size)`. -/
def runStoreStep (cx : LiftLowerContext E) (ptr : Nat) : ABI.StoreStep → P E σ Nat
  | .allocate al size => allocate cx al.bytes size
  | .reallocate old al size => reallocate cx ptr old al.bytes size
  | .trapIfMisaligned al => do
    trapIf (decide (ptr ≠ ABI.alignTo ptr al)) .unalignedPointer
    pure ptr
  | .trapIfOutOfBounds size => do
    checkInBounds cx ptr size
    pure ptr
  | .write off bs => do
    writeMem cx (ptr + off) bs.toByteArray
    pure ptr
  | .inflateLatin1 n => do
    let blk ← readMem cx ptr (2 * n)
    writeMem cx ptr (ABI.memInflateLatin1 blk.toList 0 n).toByteArray
    pure ptr
  | .deflateUtf16 n => do
    let blk ← readMem cx ptr (2 * n)
    writeMem cx ptr (ABI.memDeflateUtf16 blk.toList 0 n).toByteArray
    pure ptr

/-- Run a list of steps from pointer `ptr`, returning the final pointer. -/
def runStoreSteps (cx : LiftLowerContext E) (ptr : Nat) (steps : List ABI.StoreStep) :
    P E σ Nat :=
  Prog.foldlM (runStoreStep cx) ptr steps

/-- REF `store_string_into_range(cx, v)` (L1538-1571, with `store_string_copy`,
`store_utf16_to_utf8`, `store_latin1_to_utf8`, `store_string_to_utf8`,
`store_utf8_to_utf16`, `store_string_to_latin1_or_utf16` and
`store_probably_utf16_to_latin1_or_utf16`, L1573-1675): interpret the plan
`ABI.storeStringIntoRange cx.opts.string_encoding dst source` (`storePlanFor`), where `dst` is
the memory's pointer width and `source` is the D-a re-tagged value (`storeSource`). Returns
`(ptr, tagged_code_units)`. Precondition (REF assert, D-f): `StoreStringPre`. -/
def storeStringIntoRange (_lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (v : StrVal) :
    P E σ (Nat × Nat) := do
  let dst ← ptrType cx
  let plan := storePlanFor q cx.opts.encoding dst v
  let ptr ← runStoreSteps cx 0 plan.steps
  pure (ptr, plan.taggedCodeUnits)

/-- REF `store_string(cx, v, ptr)` (L1533-1536): `store_string_into_range`, then store the
pointer-sized `begin` and `tagged_code_units` words at `ptr` and `ptr + ptr_size`. -/
def storeString (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (v : StrVal)
    (ptr : Nat) : P E σ Unit := do
  let (begin, tagged) ← storeStringIntoRange lim q cx v
  let sz ← ptrSize cx
  writeMem cx ptr (strWordBytes sz begin)
  writeMem cx (ptr + sz) (strWordBytes sz tagged)

/-! ## Unfolding lemmas -/

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon

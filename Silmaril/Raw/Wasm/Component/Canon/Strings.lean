module

public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Context
public import Silmaril.Raw.Wasm.Component.Features
public import Silmaril.Raw.Wasm.Component.ABI.String
public import Silmaril.Raw.Wasm.Component.ABI.String.Properties

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

example : (strWordBytes 4 0x01020304).toList = [4, 3, 2, 1] := by decide +kernel
example : strWordOfBytes (strWordBytes 8 (2 ^ 63 + 5)) = 2 ^ 63 + 5 := by decide +kernel

/-! ## Loading -/

/-! ## Storing -/

/-- `StoreStringPre` holds for a stored value that is consistent for the destination width and whose
code-unit count is within `maxStringByteLength`
(`ABI.storeStringIntoRange_requestSize_le_reallocI32Max`). -/
theorem StoreStringPre.of_consistent {q : Quirks} {enc : ABI.StringEncoding} {dst : AddrType}
    {v : StrVal} (h : (storeSource q dst v).Consistent dst)
    (hmax : (storeSource q dst v).codeUnits dst ≤ ABI.maxStringByteLength) :
    StoreStringPre q enc dst v :=
  ⟨h, ABI.storeStringIntoRange_requestSize_le_reallocI32Max enc h hmax⟩

/-! ## Unfolding lemmas -/

theorem runStoreSteps_nil (cx : LiftLowerContext E) (ptr : Nat) :
    (runStoreSteps cx ptr [] : P E σ Nat) = pure ptr := rfl

/-- Without the quirk, the stored value is the D-a re-tag; for a string lifted from a memory
of the same width this is the REF tuple itself. -/
theorem storeSource_none_self (v : StrVal) : storeSource Quirks.none v.srcAddr v = v.v :=
  StrVal.retag_self v

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

section Examples

/-- Lift a string from one context and lower it into another (a string copy between
components), as `canon lift`/`canon lower` will. -/
example (cx cx' : LiftLowerContext E) (ptr tagged : Nat) : P E σ (Nat × Nat) := do
  let v ← loadStringFromRange Limits.spec Quirks.none cx ptr tagged
  storeStringIntoRange Limits.spec Quirks.none cx' v

/-- A UTF-8 to UTF-8 copy is the `store_string_copy` plan: one allocate, two checks,
one write, and the code-unit count is unchanged. -/
example : storePlanFor Quirks.none .utf8 .i32 ⟨⟨"hi", .utf8, 2⟩, .i32⟩ =
    ⟨[.allocate .one 2, .trapIfMisaligned .one, .trapIfOutOfBounds 2, .write 0 [104, 105]],
      2⟩ := by decide

/-- D-a: a UTF-16-tagged `latin1+utf16` string lifted from an `i32` memory is re-tagged for
an `i64` destination (so it is stored as UTF-16 with 1 code unit), while the raw REF tuple
under `refUtf16TagBug` is read as a (huge) Latin-1 count. -/
example : storeSource Quirks.none .i64 ⟨⟨"€", .latin1Utf16, 1 + 2 ^ 31⟩, .i32⟩ =
    ⟨"€", .latin1Utf16, 1 + 2 ^ 63⟩ := by decide
example :
    storeSource { refUtf16TagBug := true } .i64 ⟨⟨"€", .latin1Utf16, 1 + 2 ^ 31⟩, .i32⟩ =
    ⟨"€", .latin1Utf16, 1 + 2 ^ 31⟩ := by decide

example : StoreStringPre Quirks.none .utf16 .i32 ⟨⟨"héllo", .utf8, 6⟩, .i32⟩ := by decide

example : decodeTrap .utf16 = .invalidUtf16 := rfl

end Examples

end Silmaril.Wasm.Component.Canon

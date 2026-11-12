module

public import Silmaril.Wasm.Component.Reference.ABI.String.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Layout

/-!
# Canonical ABI strings: codecs, tagged lengths and store plans

This file transcribes the memory-independent part of the canonical ABI string
algorithms of the Python reference `design/mvp/canonical-abi/definitions.py`
(component-model revision `a25fc0b`; prose in `CanonicalABI.md`, sections
"Loading" → `load_string`, and "Storing" → `store_string`):

* `CanonicalOptions.string_encoding` (`'utf8' | 'utf16' | 'latin1+utf16'`) is
  `StringEncoding`, and the Python `String = tuple[str, str, int]` is `StringValue`.
* `utf16_tag`, `REALLOC_I32_MAX` and `MAX_STRING_BYTE_LENGTH` are `utf16Tag`,
  `reallocI32Max` and `maxStringByteLength`. At `a25fc0b` the maximum string byte
  length is `(1 << 28) - 1` (not `(1 << 31) - 1` as in older revisions).
* The Python codecs `'utf-8'`, `'utf-16-le'` and `'latin-1'` (strict mode) are
  `utf8Encode`/`utf8Decode?`, `utf16Encode`/`utf16Decode?` and
  `latin1Encode`/`latin1Decode`. Decoding failures are `none`, which the callers
  turn into traps. The UTF-8 decoder is Lean's `String.fromUTF8?`, whose validity
  notion (`ByteArray.IsValidUTF8`: "is the encoding of some list of scalar
  values") is exactly well-formed UTF-8, as for Python's strict codec.
* `load_string_from_range` is `loadStringFromRange?` over a byte-list image of
  memory (`loadRange` exposes its length/alignment/decoder choice separately).
* `store_string_into_range`, `store_string_copy`, `store_string_to_utf8`,
  `store_utf16_to_utf8`, `store_latin1_to_utf8`, `store_utf8_to_utf16`,
  `store_string_to_latin1_or_utf16` and `store_probably_utf16_to_latin1_or_utf16`
  are `storeStringIntoRange` and the `store*` plan builders. They do not touch
  memory: they return a `StorePlan`, a straight-line program of `StoreStep`s
  (realloc requests relative to the current pointer, trap checks, writes and the
  in-place latin1 inflation / utf16 deflation loops) plus the returned (tagged)
  code-unit count. The Python control flow never depends on realloc results
  except through traps, so this program is exact; `StorePlan.run` replays it over
  a byte-list memory with a caller-supplied realloc. Consecutive single-byte
  Python writes with no realloc or check in between are merged into one `write`.

Deviations and non-claims. Python `assert`s (such as `REALLOC_I32_MAX` bounds and
`dst_byte_length == len(encoded)`) are not traps; the plan builders are total and
their behaviour on inputs violating those assertions (a `StringValue` whose
code-unit hint disagrees with its text, see `StringValue.Consistent`) is
unspecified by the reference. `storeStringIntoRange` untags a `latin1+utf16`
source with the *destination* memory's tag, as the Python does. Memory is a
`List UInt8` here; realloc is an arbitrary function in `StorePlan.run`, and the
memory-backed canonical ABI is expected to replay `StorePlan.steps` itself.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

/-! ## UTF-8 -/

/-! ## UTF-16LE -/

/-! ## Latin-1 -/

/-! ## Values and loading -/

/-! ## Store plans -/

/-! ## Replaying a plan -/

section
variable {σ : Type}

end

end Silmaril.Wasm.Component.ABI

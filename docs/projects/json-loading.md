# Loading JSON in Lean

Use `Silmaril.Formats.Json.Fast` for runtime loading and path queries. Use
`Silmaril.Formats.Json.Fast.Elab` for JSON inputs and proofs in Lean source.
The existing `JsonWire`, `Json`, and `Lean.Json` APIs are unchanged.

```lean
module
import Silmaril.Formats.Json.Fast.Elab
open Silmaril.Formats.Json.Fast

def config : Except Error Value := json% r#"{"service":{"enabled":true}}"#

example : (config.toOption.bind fun value =>
    (value.at? [.key "service", .key "enabled"]).bind Value.bool?) = some true := by json_decide
```

In an executable, use `let result ← Fast.load path`: file IO errors are IO exceptions; invalid
input is `Except.error` with an error kind and UTF-8 byte offset. Use `parseBytes` or `parseText`
if you already have the input. `member?`, `index?` and `at?` return `none` for missing fields,
out-of-range indexes or the wrong container kind. `entries?` exposes the ordered sequence;
call `.toList` only if you need all its entries. See [the regression and file example][examples].

## Semantics

- This is the **scalar-Unicode** profile of [RFC 8259], not its full wire grammar. Invalid
  UTF-8, a leading BOM, raw control characters, and unpaired surrogate escapes are rejected.
  Escaped pairs and the equivalent literal scalar compare the same; there is no Unicode
  normalization. Invalid UTF-8 reports offset 0. Use `JsonWire` for lone surrogate escapes,
  JSONC, JSON5 or trivia/token spans.
- Order and duplicates are retained, including duplicate names written with different escapes.
  Lookup selects the **first** occurrence. It does not silently overwrite or reject duplicates.
  Convert to a uniqueness-enforcing schema explicitly if the application requires it.
- Numbers have the same `JsonWire.Decimal` contract: sign (including negative zero),
  arbitrary-precision coefficient, and signed decimal exponent. There is no rounding,
  exponent expansion or normalization at load time; `1` and `1.0` need not be structurally
  equal. This is not a lexeme-preserving representation. Avoid eager `Decimal.toInt?` on
  untrusted, huge positive exponents unless you bound them first.
- One complete value is required, including scalar roots; comments, trailing commas and
  trailing values are errors. The default limits are 128 nested containers and 4,096 bytes
  per numeric lexeme; callers of the pure/runtime reader can supply `Limits`. This is a
  buffered reader, not a streaming parser or a complete resource limiter.

## Files and trust

| Interface | What the kernel checks | When JSON is parsed |
| --- | --- | --- |
| `json% "…"` / `json_file doc from "path.json"` | The term applies the logical parser to the embedded input. Checking a positive claim about the result requires reduction. | On evaluation/reduction, not at elaboration. |
| `json_precomputed% "…"` / `json_file_precomputed doc from "path.json"` | The emitted term has the declared type. This alone certifies neither the parser output nor the relationship to the bytes. | During elaboration, with the compiled parser. Invalid JSON is an elaboration error. |

The precomputed forms require a local opt-in, `set_option silmaril.json.allowPrecomputed true in`.
There is no switch to native proof evaluation, and no automatic fallback. Importing a module
with precomputed definitions does not rerun or validate its generator or consult the option.
Both file commands read relative to the `.lean` file and emit a noncomputable `doc` and
`doc.source : String`. Invalid UTF-8 prevents the command from embedding a `String` in either
mode. Make the JSON file an explicit build input in your own workflow: Lake does not track reads
by these elaborators. Rebuild after input changes.

`json_decide` runs `decide +kernel`. On precomputed data a field claim is about the resulting
Lean term, not the source file. To certify agreement, prove a separate closed goal:

```lean
example : SourceMatches doc.source.toUTF8 doc := by json_source
```

`json_source` asks the kernel to check equality to `parseBytes` of the bytes in the goal; it
does not use the evaluator or a digest. It can also compare against independently supplied
bytes. For the source form, this may prove equality of parser applications without proving
that parsing succeeds. For precomputed data it generally requires a full logical parse and
comparison, and may exhaust the kernel budget on large inputs. In neither case does a theorem
authenticate the external filesystem or prove that a path still contains the embedded bytes.

## Representation and proofs

`ChunkSeq` adapts `KBytes`'s length-guided routing to arbitrary array elements, storing at most
32 in a leaf. It is used both for arrays and ordered object members. Wider objects get a separate
balanced search tree of UTF-8 hashes and source positions. It hashes the query once, compares
integers while routing, and then compares strings exactly within the matching bucket. This is
not a cryptographic hash: collision-heavy lookups can still be linear. Small objects avoid the
index entirely. Selective queries of precomputed constructor terms do not build a full value
or read its source, unlike queries that start with a parser call.

Theorems in `ChunkSeq.Thms` cover array order, well-sized construction, and indexed lookup.
`Fast.Thms` relates UTF-8 text parsing to byte parsing and proves that successful object
lookups return a member with the requested key. The tests check collision handling and
first-occurrence behavior; there is no general first-occurrence proof for the generated hash
index, or general equivalence theorem for the new parser and the wire grammar. `Value.toWire?`
forgets the index, preserving order, duplicates, decimals and UTF-16 string semantics, subject
to an explicit conversion-depth budget. This gives a place to express a future DASL JSON
schema/representation relation, independently of the index and of source loading. It does not
implement or validate DASL.

Run `make json-loading-check` for the regression and [the benchmark harness][benchmark] for
measurements and reproduction commands.

[RFC 8259]: https://www.rfc-editor.org/rfc/rfc8259
[examples]: ../../tests/json-loading/Regression.lean
[benchmark]: ../../benchmarks/json-loading/README.md

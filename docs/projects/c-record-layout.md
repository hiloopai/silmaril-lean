# C record layouts from source text, checked against Clang

A small vertical slice on top of [`Silmaril.Data.Layout`](data.md): C `struct` and `union`
definitions written as text are parsed into the existing declaration model, laid out under a
chosen target data model, and compared with record layouts that Clang reports for the same
text and target. One command turns C text into named Lean declarations with kernel-checked
certificates.

```lean
@[expose] public section
open Silmaril.Data.Layout.Record

c_layout Demo for Target.x86_64 Target.i386 := include_str "clang/message.c"
c_layout_import Demo.i386 from "clang/message.i386.json"

example : Demo.i386.Message.entries.map (·.offset) = [0, 36, 48] := by decide
#check (Demo.i386.observed.crossChecked :
  Interchange.CrossChecked Demo.source Demo.i386.target Demo.i386.observed.report)
```

The worked example is
[`Silmaril/Data/Layout/Examples/Clang.lean`](../../Silmaril/Data/Layout/Examples/Clang.lean)
(five targets, five Clang fixtures); the rejection tests are in
[`Examples/Rejections.lean`](../../Silmaril/Data/Layout/Examples/Rejections.lean).

## Three descriptions of one record

| | Lean | units | where it comes from |
| --- | --- | --- | --- |
| source description | `Decl` / `Env` (existing) | none | `Source.parse` of the C text |
| ABI-resolved layout | `Record.RecordLayout` | bytes | `Record.resolveEnv dm env`: a `DataModel` (scalar sizes and alignments) and the psABI placement rule of `declLayout` |
| observed layout | `Record.ObservedRecord` | bits | a compiler's report, imported as JSON |

`RecordLayout` forgets C types: a record is a kind, a size, an alignment and named,
aligned byte ranges. That is the vocabulary an FFI layer or a compiled-layout dump shares,
and the place a later producer (for instance compiled C++ records seen through a
C-compatible ABI) would extend with entry kinds of its own. This slice models no C++: there
is no C++ parser, `kind` is `struct` or `union`, and `dataSize` (size without tail padding)
is predicted equal to `size`, as it is for C.

## Modules

| Module | Contents |
| --- | --- |
| `Layout.Source.Defs` | lexer `lex`, grammar relations (`Spec`, `Suffix`, `Declarator`, `DeclList`, `Members`, `RecordDef`, `TransUnit`), static checks `checkScope`, `Parses`, the parser `parse` and its error messages |
| `Layout.Source.Thms` | `parse_sound : parse src = .ok env → Parses src env` |
| `Layout.Record.Defs` | `RecordLayout`, `RecordLayout.WF`, `resolveEnv`, `ObservedRecord`, `RecordLayout.observe`, `Agrees`, `Target` |
| `Layout.Record.Thms` | `resolveEnv_wf`, `resolveEnv_names`, `Agrees.field`; the targets `Target.x86_64`, `i386`, `aarch64`, `riscv64`, `wasm32` with their Clang triples |
| `Layout.Interchange.Defs` | the `silmaril.c-record-layout` v1 JSON schema: `Report`, `Provenance`, `encode`, `decode`, `decodeText`, `Report.Matches`, `CrossChecked` |
| `Layout.Interchange.Thms` | `decode_encode : decode (encode r) = .ok r`, UTF-16 string round trip |
| `Layout.Command.Defs` | the `c_layout` and `c_layout_import` commands |
| `Layout.Examples.Clang`, `.Rejections` | the worked example and regression tests |

Proofs longer than a few lines are in `Silmaril/Proofs/Data/Layout/{Source,Record,Interchange}.lean`.

## The accepted C subset

```
unit       ::= record*
record     ::= ("struct" | "union") NAME "{" member+ "}" ";"
member     ::= spec declarator ("," declarator)* ";"
spec       ::= scalar | "struct" NAME | "union" NAME
declarator ::= "*"* NAME ("[" DECIMAL "]")*
```

Scalars are the standard integer types in their usual spellings, `_Bool`, `float`,
`double`, `long double`, `void` behind a pointer, and the `<stdint.h>`/`<stddef.h>` names
`int8_t` … `uint64_t`, `size_t`, `ptrdiff_t`, `intptr_t`, `uintptr_t` (built in, since no
preprocessor runs). Comments are skipped. Records used by value, directly or as array
elements, must be defined earlier in the same text; pointers may name any tag. Tags and
member names must be unique.

Rejected with a specific message (each one is a test in `Examples/Rejections.lean`):
bit-fields, `_Alignas`/`alignas`, `__attribute__`, `#pragma` and other preprocessor lines,
type qualifiers, `typedef`, `enum`, storage classes, flexible and zero-length arrays,
function pointers, anonymous members, records defined inside a member, forward
declarations, object declarations, empty records, `_Complex`, `__int128`, `_BitInt`,
non-decimal literals and non-ASCII characters outside comments.

## Targets and the placement rule

A `Target` bundles a `DataModel` (from `Layout.Defs`: every scalar's size and in-record
alignment, chosen per psABI), its well-formedness proof, a short name used for generated
declarations, and the Clang triple an observation must name. The five targets reuse the
existing data models: `sysvX86_64`, `i386Ilp32` (where `double`, `long long` and
`long double` are 4-aligned inside records and `long double` is 12 bytes), `aapcs64`,
`rv64Lp64` and `wasm32`. A new target is a new `Target` value; nothing in the parser or the
commands depends on the choice.

The placement rule is the existing `declLayout`: members at the next multiple of their
alignment, union members at offset zero, record alignment the largest member alignment,
size rounded up to it. `resolveEnv_wf` proves every result well-formed under a well-formed
data model: power-of-two alignments, members in bounds and aligned, struct members disjoint
and in order.

## The JSON interchange format

Clang does not print record layouts as JSON. Its `-cc1` flags `-fdump-record-layouts`
(byte offsets with names, nested records expanded) and `-fdump-record-layouts-simple` (per
record `Size`, `DataSize`, `Alignment` and `FieldOffsets` in bits, without names) print
text, and `-ast-dump=json` has member names but no offsets. So this slice defines a
normalized, versioned schema and keeps the Clang specifics in an adapter:

```json
{"schema": "silmaril.c-record-layout", "version": 1, "unit": "bit",
  "provenance": {"producer": "clang", "producerVersion": "Debian clang version 19.1.7 (3+b1)",
    "method": "clang -cc1 -triple i386-unknown-linux-gnu -fsyntax-only …",
    "target": "i386-unknown-linux-gnu", "adapter": "tools/c-layout/clang_record_layouts.py v1",
    "source": "struct Point { short x; short y; };\n…"},
  "records": [
    {"kind": "struct", "name": "Point", "size": 32, "dataSize": 32, "align": 16, "fields": [
      {"name": "x", "offset": 0},
      {"name": "y", "offset": 16}]}]}
```

* **Units** are bits, as Clang reports them, and the file says so (`"unit": "bit"`).
* **Provenance** records the producer, its version, the exact commands, the target triple,
  the adapter and the exact source text. The source and the target are checked
  (`Report.Matches`); the rest is recorded, not interpreted.
* **Records** are those defined in the source, in definition order, members in declaration
  order.
* **Readers are strict**: all members required, no unknown or duplicate members, numbers
  non-negative integers, `kind` one of `struct`/`union`, `version` exactly 1.

`decode_encode` proves the codec round-trips at the JSON-tree level. Bytes are read with the
repository's RFC 8259 reader (`Silmaril.Formats.JsonWire.parse?`), which has no
printer/reader round-trip theorem, so the byte level is not covered by a proof.

### The Clang adapter

[`tools/c-layout/clang_record_layouts.py`](../../tools/c-layout/clang_record_layouts.py)
runs `clang -cc1 -triple T -fsyntax-only -fdump-record-layouts-simple
-fdump-record-layouts-complete` and `-ast-dump=json` on one file and joins them by record
name (standard library only):

```sh
cd Silmaril/Data/Layout/Examples/clang
python3 -I ../../../../../tools/c-layout/clang_record_layouts.py message.c \
  --target i386-unknown-linux-gnu -o message.i386.json
```

[`tools/c-layout/check_offsetof.py`](../../tools/c-layout/check_offsetof.py) is an
independent cross-check that does not read layout dumps: it appends `_Static_assert`s on
`sizeof`, `_Alignof` and `__builtin_offsetof` for every number of a report to the report's
own source and has Clang compile it for the report's triple. `make c-layout-check` rebuilds
the Lean examples, re-derives every fixture with the local Clang (`--check`, ignoring the
version string) and runs the static assertions; it needs `clang` on the path and is not part
of `make check`. The committed fixtures were produced with Debian clang 19.1.7; the x86-64
assertions also hold under GCC 14.2.

## What is proved, what is checked, what is trusted

| step | status |
| --- | --- |
| C text → `Env` | `N.parses : Parses N.source N.ast`, a kernel proof (the parser run by `decide +kernel`, then `parse_sound`) |
| `Env` → layouts on a target | `N.<t>.resolves`, a kernel proof; `N.<t>.wf` from `resolveEnv_wf` |
| JSON tree ↔ `Report` | `decode_encode`, proved for all reports |
| JSON file → `Report` | run by the command (compiled `decodeText`), **not** a kernel proof: reducing the JSON reader in the kernel did not finish for a 2 KB file (minutes, tens of GB) |
| `Report` agrees with the layouts | `N.<t>.observed.matches`, a kernel proof (`decide +kernel`) |
| the report is what Clang printed | the adapter's job; re-checkable with `make c-layout-check` |

`N.<t>.observed.crossChecked : CrossChecked N.source N.<t>.target report` packages the kernel
part. All theorems use only `propext`, `Classical.choice` and `Quot.sound`.

Not claimed: that `Parses` is the C grammar (it is the subset above, by definition), that
the parser is complete for its grammar, that the data models are the psABIs (they are
transcriptions, checked here and in `Layout.Glibc` against compilers), or anything about C
or Clang semantics beyond the fixtures that agree.

## Build

Lake does not track files read at elaboration time (`include_str`, `c_layout_import`), as for
`include_bytes`: after regenerating a fixture, touch `Examples/Clang.lean` so it is
re-checked.

```sh
lake build --wfail Silmaril.Data.Layout.Examples.Clang Silmaril.Data.Layout.Examples.Rejections
make c-layout-check   # also needs clang
```

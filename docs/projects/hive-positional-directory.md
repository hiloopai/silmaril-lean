# Bounded positional partition directories

[`PartitionPath.Positional.parse`](../../Silmaril/Formats/Hive/PartitionPath/Positional/Defs.lean)
takes a directory byte cap, an ordered list of partition keys, and a segment
encoding. The function fits `Manifest.DirectoryParser`. Pass it to the
[existing bounded or ordered inventory](hive-manifest-inventory.md#literal-directory-profile)
to bind and scan supplied files.

## Profile

1. Measure the original directory's UTF-8 bytes before splitting. In a
   manifest the existing limits also count all supplied occurrences and
   bound each complete relative file path, including its leaf.
2. Split at literal slash. The empty directory has zero positions. Require
   exactly as many positions as declared keys before decoding. Reject
   empty segments. Delimiters inside percent escapes are interpreted only
   after splitting.
3. URI mode decodes one strict UTF-8 layer using the shared percent codec.
   Literal mode keeps the segment text, matching PyArrow's
   `segment_encoding="none"` convention. An equals sign is ordinary
   positional text. Validate key uniqueness, nonempty keys, and the
   configured required keys.
4. Bind supplied values to the declared keys in positional order. Every
   value is present. The typed binder uses the partition schema's own
   field order and its checked converter. Sorted lookup, duplicates,
   error indices, and bounded skip-open behavior follow the existing laws.

## Pinned PyArrow comparison

The profile shares the text convention of
[PyArrow 26.0.1 DirectoryPartitioning](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/arrow/dataset/partition.cc#L307-L382)
on the checked exact-arity subset. PyArrow accepts missing trailing
positions and ignores extra trailing segments. It can also accept an
empty string slot or malformed percent text. The strict Lean profile
refuses missing, extra, and empty positions and invalid URI escapes.
Both test suites reject invalid decoded UTF-8 in URI mode.

PyArrow's positional reader interprets `__HIVE_DEFAULT_PARTITION__` as
ordinary string text. Its positional formatter can omit trailing nulls
and refuses a later key after a null. The Lean parser never infers null
from a path segment. The shared manifest canonical renderer refuses
present text equal to its configured null marker with
`nullMarkerCollision`. A caller can choose a different, noncolliding
canonical marker to accept this text. The canonical directory is internal
`key=value` metadata. The opener receives the original file string. This
profile covers reading supplied paths and keeps existing URI and literal
Hive defaults. It assumes an explicit key declaration and typed schema.

[`parse_ok_iff`](../../Silmaril/Formats/Hive/PartitionPath/Positional/Thms.lean)
specifies exact arity, the byte cap, and the zip of keys with decoded values.
`parse_keys_present` gives the full ordered key declaration and proves
every value present. Existing `prepareInventoryWith_eq_reference`,
`prepareInventoryWith_paths`, and
`prepareOrderedInventoryWith_scanSkippingRejected_eq_reference` apply to
the positional parser through the shared admission interface.

## Replay

[The oracle](../../scripts/hive-positional-path-oracle/Oracle.py)
uses CPython 3.14.7, PyArrow 26.0.1 and NumPy 2.5.5 with the
[inventory digest and wheel pins](hive-manifest-inventory.md#independent-fixture).
It reads copies of the [pinned Parquet fixture](../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet)
under positional paths in both modes. A reversed listing, duplicate
escaped path, predicate, and control leaf yield the same retained
occurrences, with mode-specific values. PyArrow independently verifies
the rows under explicit caller ordering. Lean checks the aligned
`[3, 0, 2]` repeated group structure and exact final EOS pull.

```sh
python -I scripts/hive-positional-path-oracle/Oracle.py data/parquet-int32-byte-array-file/empty-middle-v2.parquet
lake build --wfail +Silmaril.Formats.Hive.PartitionPath.Positional.Checks
```

## Canonical bounded rendering

[`Positional.render`](../../Silmaril/Formats/Hive/PartitionPath/Positional/Render/Defs.lean)
takes the same ordered keys, encoding and options as the parser. Entries
must match the key sequence exactly and pass the shared key validation.
URI mode uses the shared uppercase percent encoder. It keeps underscores,
escapes literal percent and delimiters, and encodes non-ASCII text as UTF-8.
Literal mode keeps safe text as supplied, including equals, underscores,
percent and non-ASCII characters. Encoded segments must be nonempty and
may not contain slash, backslash, colon or NUL or equal `.` or `..`.
The URI encoder leaves dots unescaped, so the special dot and dot-dot components
are refused in either mode.

This exact-arity formatter refuses null in any position, including a trailing
one. It also refuses present text equal to the configured canonical Hive
null marker so the output can be used with shared manifest admission.
A different noncolliding marker permits that literal string. PyArrow reads
that string as ordinary positional text. Zero declared keys and zero entries
produce the empty directory.

Byte caps apply to each encoded segment and the whole joined directory,
including slash separators. The separate inventory bound applies to each
complete path with its leaf. These are output size bounds. Validation checks
the marker option, key order and shared key rules first, then encoded values
left to right, and finally the joined directory size.

`render_spec` proves that successful output parses to the original ordered
entries, has exactly the declared segment count, and satisfies both byte caps.
`parse_render_of_ok` gives the parser equality directly. The same shared
ordered inventory accepts the rendered directories. Its existing
`prepareInventoryWith_paths` law preserves supplied literal resolver keys,
including escape case and the leaf spelling.

The optional second argument to the pinned oracle is the output of
[`Generate.lean`](../../scripts/hive-positional-path-oracle/Generate.lean).
PyArrow reads actual Parquet bytes under these Lean-generated URI, literal,
alternate-marker and zero-key directories. It checks the exact virtual
values and all five physical rows, including null, empty and non-UTF-8
binary payloads. Lean checks admission and actual snapshot reads with a
second URI spelling that decodes identically but resolves at its own key.

```sh
lake build --wfail +Silmaril.Formats.Hive.PartitionPath.Positional.Render.Checks
lake env lean -DautoImplicit=false -DwarningAsError=true --run scripts/hive-positional-path-oracle/Generate.lean > /tmp/positional-directories.txt
python -I scripts/hive-positional-path-oracle/Oracle.py data/parquet-int32-byte-array-file/empty-middle-v2.parquet /tmp/positional-directories.txt
```

## Bounded scan of rendered directories

`Manifest.RenderedPositional.scan` is a specialization of the shared
ordered inventory and bounded paired INT32 and opaque BYTE_ARRAY scanner.
The inventory first checks the original listing, skipping exact controls
after lexical validation. On success it stably sorts the complete literal
keys, retaining repetitions. The partition predicate then removes rejected
occurrences before any Parquet actions are charged.

`Positional.parse_of_rendered_spelling` proves that an input directory within
its byte cap decodes to the original render entries when its segment count
and ordered segment decoding agree with the canonical directory. This
covers alternate percent escape case without changing the original parent
or leaf spelling. The renderer's per-segment output cap applies to the
canonical render. The reader applies its existing directory and full-path
input caps to the supplied spelling.

`RenderedPositional.scan_eq_reference` compares the full bounded result
to binding independently supplied original entries, then ordering and
pruning the resulting file occurrences. Its render witness is only needed
for lexically valid, affordable data paths in the inventory prefix, and
the reference still reports the indexed directory byte error when that cap
fails. The equality includes aligned projected batches, empty groups,
the exact selected prefix at budget cutoff and a reached retained error
with its original path. Invalid casts and marker collisions are admission
errors even for an occurrence the scan would have pruned.

The optional `--scan` generator argument adds directories for the ordered
comparison. PyArrow reads an explicit sorted listing with a repeated file,
an alternate escape spelling and a filtered partition. It checks all
twenty projected rows, including repeated virtual columns, nullable binary
payloads and the zero-column row count. Lean also checks a missing pruned
path, exact EOS and cutoff, and corruption in a later retained row group.
The action budget describes checked opens and pulls on supplied snapshots.

```sh
lake build --wfail +Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Checks
lake env lean -DautoImplicit=false -DwarningAsError=true --run scripts/hive-positional-path-oracle/Generate.lean --scan > /tmp/positional-scan-directories.txt
python -I scripts/hive-positional-path-oracle/Oracle.py data/parquet-int32-byte-array-file/empty-middle-v2.parquet /tmp/positional-scan-directories.txt
```

## Atomic named-table import

[`NamedTable.FromRenderedPositional.importScan`](../../Silmaril/Formats/Relational/NamedTable/FromRenderedPositional/Defs.lean)
feeds the bounded positional scan into the shared Arrow named-table
import at the exact projected schema. It returns a new packed database
only after EOS at a vacant name. The destination conflict has the
existing named-table error precedence. Admission failures are tagged
as open errors, retained read and close failures keep their original
causes, and budget exhaustion returns `.closed` even when all projected
rows have been emitted. Each failure returns an error without a new
database.

`importScan_ok_iff` identifies the exact single-name update.
`importScan_observe` proves the ordered named observation and equality
at every other key. The stored row count is the sum of the trace's
batch counts, including when the projection has zero columns.
`importScan_eq_reference` lifts the rendered scan's original-entry
law through the same import.

The rendered positional scan checks load the same Parquet listing into
a vacant name and compare its schema, ordered nullable rows, and
zero-column count against the same expectations as the pinned PyArrow
oracle. They also load an empty manifest at zero budget and verify
conflict, indexed admission failure, cutoff just before EOS, and a
retained read failure after emitted groups.

## Typed UTF-8 CSV export

[`NamedTable.FromRenderedPositional.ToCsv.convert`](../../Silmaril/Formats/Relational/NamedTable/FromRenderedPositional/ToCsv/Defs.lean)
exports the installed name through the shared UTF-8 named-table writer.
It returns the updated database, ordered typed CSV schema and bytes
together after observed EOS and a successful byte-count check. The
database retains its original String labels. The CSV view uses the exact
UTF-8 bytes of each projected label in position order, including repeated
labels. The CSV grammar can refuse unrepresentable labels.

The paired profile supports signed Int32 as canonical decimal and opaque
BYTE_ARRAY as the existing uppercase percent escaping of octets.
Unreserved ASCII bytes stay literal. The decoder requires canonical
escape spelling and recovers the original bytes, including invalid UTF-8
and NUL. The shared typed CSV tags distinguish `N` for null from `T`
for a present empty byte string. At width zero the shared marker emits
one quoted empty field for the header and one per data row. The schema
accompanying the bytes declares width zero.

`convert_roundTrip` proves that successful readback recovers every
projected row in order with its exact nullable cells. The result records
the single-name update and the output bound. `convert_eq_reference`
lifts the full original-render-entry scan and import law, including
indexed admission errors, late retained failure, and cutoff before
explicit EOS. Those errors propagate without a CSV or database result.
CSV encoding and oversize output have separate typed errors. The CSV
cap applies to the completed output length, including headers and
framing.

The independent oracle reads the actual Lean-produced CSV with CPython's
CSV reader and compares each tagged field to PyArrow's ordered rows from
the same sorted and pruned Parquet listing. The fixture covers repeated
columns, duplicate file occurrences, non-ASCII partition bytes, nullable
opaque payloads and width zero.

```sh
lake build --wfail +Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Checks
lake env lean --run scripts/hive-positional-path-oracle/Generate.lean --scan > /tmp/positional-scan-directories.txt
lake env lean --run Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Int32ByteArray/RenderedPositional/Checks.lean /tmp/positional.csv /tmp/positional-zero.csv
python -I scripts/hive-positional-path-oracle/Oracle.py data/parquet-int32-byte-array-file/empty-middle-v2.parquet /tmp/positional-scan-directories.txt /tmp/positional.csv /tmp/positional-zero.csv
```

## Restore the named table from typed CSV

[`NamedTable.FromRenderedPositional.FromCsv.importCsv`](../../Silmaril/Formats/Relational/NamedTable/FromRenderedPositional/FromCsv/Defs.lean)
takes an expected and a declared ordered String/Kind schema. The declared
schema determines the exact UTF-8 header and canonical Int32 and octet
codecs. The expected schema must agree exactly, including positional
labels, duplicate labels, kinds and layout tags. Kinds travel out of
band. Cells use the shared nullable table semantics.

An occupied destination is rejected before reading. For a vacant
destination, the importer checks the inclusive wire byte cap before
decoding. The input bytes are already supplied by the caller. The
shared typed decoder allocates the lexical and typed tables before the
inclusive admitted-row check. This row cap bounds the published table,
including zero-column rows. A header, cell or cap error returns the
original typed cause with no updated database. Exact schema matching
takes place at insertion after successful decoding and cap checks.

`readCsv_ok_iff` specifies exact decoding and both caps.
`importCsv_ok_iff` specifies the single-name update.
`import_convert` proves that a successful forward conversion imports
into a vacant target under the same projected schema exactly when the
reverse byte and row caps admit it. The update contains the original
String labels and ordered nullable cells and preserves every other name.

Pass an additional output directory to the independent oracle command
above to generate six CPython-authored inputs from the pinned PyArrow
rows. The valid projected and zero-column inputs use Python's minimal
CSV quoting. The other four exercise an incorrect header, noncanonical
byte and Int32 cells, and an incorrect zero-column marker. Replay them
against the actual importer.

```sh
python -I scripts/hive-positional-path-oracle/Oracle.py data/parquet-int32-byte-array-file/empty-middle-v2.parquet /tmp/positional-scan-directories.txt /tmp/positional.csv /tmp/positional-zero.csv /tmp/positional-csv-inputs
lake env lean --run Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Int32ByteArray/RenderedPositional/Checks.lean --check-csv /tmp/positional-csv-inputs
```

### Opt-in row-budgeted restore

[`FromCsv.Bounded.importCsv`](../../Silmaril/Formats/Relational/NamedTable/FromRenderedPositional/FromCsv/Bounded/Defs.lean)
uses the same String/Kind schemas, named insertion policy, wire byte cap,
and canonical column codecs. It checks the row cap during decoding.
Each accepted data row spends one unit, including zero-column markers.
Insertion still requires complete input and exact schema agreement.

An occupied destination takes precedence over wire processing. At a
vacant name, the supplied wire byte cap is checked before decoding.
Header errors precede body processing. A reached body record is
validated before the next budget check, so a malformed cell within the
budget returns its typed error. When the remaining budget is zero,
a nonempty suffix returns the bounded decoder's `.rowLimit` before
parsing that suffix. Schema mismatch is checked at insertion after a
successful complete decode.

`importCsv_agrees_on_success` proves that both entry points return
the same updated database on success under the same caps.
`importCsv_observe` gives the exact ordered observation, including
duplicate labels, layout tags and width-zero rows, and preserves every
other database entry. The existing complete-reader entry point is
available with its original error precedence.

The retained-row cap counts rows. The separate wire byte cap applies
to the already supplied list, and the parser can allocate the header and
individual fields within that wire. The row cap is not a per-field byte
limit. The bounded decoder does not build an entire raw table.

Append `--row-budget` after the output directory in the independent
oracle command to add late cell and wire errors. Run the checks with
`--check-bounded-csv` and the same directory. These checks cover exact
and short caps on both valid CPython inputs, plus reached and unreached
suffix errors. The existing complete importer is also run on the two
suffix cases to show the precedence difference.

# Hive ISO DATE partitions

[`Hive.Date32`](../../Silmaril/Formats/Hive/Date32/Defs.lean) is an opt-in
scan profile for a supplied manifest with one named DATE partition key and
one physical nullable, unannotated INT32 Parquet leaf. The virtual column
follows the physical leaf. Its values are nullable signed days since
1970-01-01, the Date32 payload representation. This profile adds no DATE
wire or filesystem operations.

## Admission and observation

The profile uses the existing native manifest path and file rules, including
the literal `part-0.parquet` basename. It uses the Hive URI directory parser:
split on raw delimiters, percent-decode key and value once as UTF-8, then
compare the decoded value with the configured null marker. A present,
non-marker value must use canonical `YYYY-MM-DD` in the Gregorian calendar,
with years `0000` through `9999` and astronomical year numbering. The DATE
codec preserves negative epoch days. The schema requires the named key and
rejects extra keys, duplicate decoded keys and collision with the physical
leaf name.

The default URI marker and custom nonempty markers yield null even in
escaped spellings. A marker that is itself a valid DATE, such as
`2000-02-29`, takes precedence over date conversion. On this URI profile
the same decoded spelling cannot denote a literal DATE and null under the
same options. The separate raw-marker profile retains its existing policy.

The scan checks each reached file path and typed binding before applying
the partition predicate. A rejected valid binding skips the payload.
Malformed paths and invalid DATE values fail even with a rejecting
predicate. A selected payload receives the existing bounded group and file
checks. Completed batches retain their literal manifest path, original
occurrence index, footer ordinal and row order. A reached failure preserves
the completed prefix and ends the scan before subsequent occurrences.
See [the public canonical conversion, nullable binding and first-error laws](../../Silmaril/Formats/Hive/Date32/Thms.lean).

## Independent comparison

The check driver emits genuine native Parquet and records both full and
pruned traces. The PyArrow 26.0.1 oracle opens the literal paths using an
explicit ordered inventory and a `date32[day]` Hive partition schema. It
compares exact date values as epoch days, nullable payload slots, footer
group counts, retained literal paths and repeated occurrences. The oracle
covers astronomical year zero, leap day, raw and escaped default markers,
a custom URI-escaped marker, and an escaped DATE-valued marker. Reading
one fragment at a time in explicit inventory order gives the comparator's
order.

Both sides reject invalid calendar values and invalid decoded UTF-8 on
these cases. PyArrow ignores the tested malformed-percent key
`%6Gay` and undeclared key `d%61x`, and treats the tested repeated
decoded key as a conjunction. The Lean profile keeps its strict URI,
schema and duplicate-key errors.

```sh
tmp=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Hive.Date32.Checks
lake env lean --run Silmaril/Formats/Hive/Date32/Checks.lean "$tmp"
docker run --rm --network host --platform linux/amd64 \
  -v "$PWD:/repo:ro" -v "$tmp:/out:ro" \
  python@sha256:51dafde81dbdb6ebde285137a295cf18a47ca95234fe388a343719cb97305b3d \
  sh -ec 'printf "%s\n" \
    "pyarrow==26.0.1 --hash=sha256:7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814" \
    "numpy==2.5.5 --hash=sha256:c48960d420e90cf305cb1fde0d4e6082cc90512cda87a9acf0b6e04e91cf4abe" > /tmp/requirements.txt
    python -m pip install --require-hashes -r /tmp/requirements.txt
    python -I /repo/scripts/hive-date32-oracle/Oracle.py /out'
```

## Canonical outbound paths

[`Date32.renderDirectory`](../../Silmaril/Formats/Hive/Date32/Render/Defs.lean)
takes one declared key, explicit Hive URI options, and a nullable signed
epoch day. It emits one relative `key=value` segment. The shared DATE
printer accepts days from −719528 through 2932896 inclusive and emits
canonical ten-byte date text. Null uses the supplied nonempty marker.
The existing Hive renderer checks the key and required keys, rejects a
present text equal to the marker, and percent-escapes keys and values.

Marker equality uses decoded text. For example, with marker `2000-02-29`,
a null renders as `day=2000-02-29` and the present leap date is refused
with `nullMarkerCollision`. With the literal marker `2000%2D02%2D29`,
null instead renders as `day=2000%252D02%252D29`. An out-of-range
present day fails before Hive key and marker validation.

[`decodeDirectory_renderDirectory`](../../Silmaril/Formats/Hive/Date32/Render/Thms.lean)
recovers the same nullable epoch day under the same key and options.
The present-cell encoder also satisfies the existing write plan's left
inverse, so it can be passed to native manifest emission and restored
with the existing DATE reader. Supplied file paths retain their literal
spelling. The formatter generates a directory, and the existing
manifest writer owns file admission and emission.

The outbound fixture uses the native write plan with interleaved dates,
nulls, year endpoints and an escaped key and marker. PyArrow reads nine
actual Parquet files at the generated literal paths and compares ten
groups, in explicit manifest and footer order. With the simple key it
also independently reproduces six directory spellings, and demonstrates
that PyArrow writes the same spelling for a valid DATE marker and the
present value equal to it. PyArrow reads that spelling as null. Lean
refuses the present value.

```sh
tmp=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Hive.Date32.Render.Checks
lake env lean --run Silmaril/Formats/Hive/Date32/Render/Checks.lean "$tmp"
docker run --rm --network host --platform linux/amd64 \
  -v "$PWD:/repo:ro" -v "$tmp:/out:ro" \
  python@sha256:51dafde81dbdb6ebde285137a295cf18a47ca95234fe388a343719cb97305b3d \
  sh -ec 'printf "%s\n" \
    "pyarrow==26.0.1 --hash=sha256:7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814" \
    "numpy==2.5.5 --hash=sha256:c48960d420e90cf305cb1fde0d4e6082cc90512cda87a9acf0b6e04e91cf4abe" > /tmp/requirements.txt
    python -m pip install --require-hashes -r /tmp/requirements.txt
    python -I /repo/scripts/hive-date32-render-oracle/Oracle.py /out'
```

## Checked named-table manifest round trip

[`Date32.emitManifest` and `Date32.restoreManifest`](../../Silmaril/Formats/Hive/Date32/Manifest/Defs.lean)
fix the writer and reader to this DATE codec and the existing bounded
row-group INT32 profile. The named source has the physical leaf first
and the single nullable DATE partition column second. On successful
emission, restoration with the same key, path options and row-group
policy returns the exact original typed rows grouped by first-seen
directory, with source-relative row order within each directory. The
grouped order can differ from the original interleaving. The manifest
law also certifies each literal path, cut vector and decoded slot list.

The source name and schema are checked before routing. After a valid
source and prefix, a present date equal to the marker reports the
original row index and key before cut or file admission, yielding no
manifest value. Restore visits supplied occurrences in order, including
duplicate paths. A reached path or DATE binding error retains its
original literal path, occurrence index and typed cause, before opening
the payload for that occurrence. See the [public manifest laws](../../Silmaril/Formats/Hive/Date32/Manifest/Thms.lean).

The outbound fixture driver above uses these manifest entry points to
emit and restore the same nine native files. The additional controls
check missing and mismatched sources, routing precedence over an invalid
cut policy, duplicate occurrences, alternate URI spelling, an empty
manifest, and late path and DATE failures with unreadable payloads.

## Selected manifest restore

[`Date32.restoreSelected`](../../Silmaril/Formats/Hive/Date32/Manifest/Defs.lean)
takes a predicate on the singleton nullable DATE partition row. After
checking the declared schema and row-group width, it visits the literal
manifest occurrences in their supplied order. For each reached occurrence,
it checks the relative path syntax and required basename, decodes the
Hive URI components, checks the declared key and the marker policy, and
converts any present DATE text. These checks precede the predicate.
A false or unknown result skips all per-file payload checks, including
manifest dimensions, Parquet schema and footer validation, and group
decoding. A true result uses the existing checked native file reader.

Following a successful full restore, the
[public laws](../../Silmaril/Formats/Hive/Date32/Manifest/Thms.lean)
give exact equality to stable filtering of those rows, including repeated
file occurrences. A reached binding failure preserves the original path,
index and typed cause. After a prefix has completed, the first
selected payload failure also carries the original path, occurrence and
payload error, including any indexed group cause. The restore result
returns an error in that case. Selecting from a manifest with unreadable
payloads can succeed by skipping a validly bound rejected occurrence.

The pruning fixture has a duplicate null-marker path and a leap-day file
with two groups. Its damaged variant changes the second group's page
header while leaving the footer and first group readable. Both Lean and
the pinned PyArrow comparator agree with post-filtering on the clean
fixture, skip the damaged payload under a rejecting predicate, and reach
its error under a selecting predicate. The Lean guards also exercise
unknown predicate results and malformed paths.

Generate the fixture with
`lake env lean --run Silmaril/Formats/Hive/Date32/Render/Checks.lean pruning "$tmp"`.
Use the pinned outbound command above with
`python -I /repo/scripts/hive-date32-render-oracle/Oracle.py /out --pruning`.

## Paired read with DATE and UTF-8 partition keys

[`Hive.Date32.Utf8`](../../Silmaril/Formats/Hive/Date32/Utf8/Defs.lean)
is an opt-in read profile with two distinct caller-named partition keys.
The caller chooses DATE-first or text-first order. Each path can spell
its assignments in either order. Missing keys are errors and explicit
decoded markers give nullable cells. A DATE uses signed epoch-day
storage, and decoded UTF-8 text uses a byte-array cell. Empty text
remains a present empty byte array. The physical Parquet columns are the
existing checked INT32 and opaque BYTE_ARRAY pair. Their order precedes
the declared virtual key order.

Path admission is strict and runs to completion before the first
snapshot lookup. The shared lexical and URI checks and the unknown-key
check apply before conversion. Once those checks pass, a missing key or
invalid DATE is reported in declared field order. The first failing
declaration retains its literal path and typed cause. Successful
admission retains exact lookup keys and repeated path occurrences. The
strict reader uses the existing checked paired opener and its payload
error semantics. Projections can repeat or reorder positions, and
zero-column projections preserve row counts. See the
[ordered binding and native scan laws](../../Silmaril/Formats/Hive/Date32/Utf8/Thms.lean).

The independent PyArrow comparator uses the pinned
[paired Parquet fixture](parquet-int32-byte-array-file.md). It reads
four literal path occurrences, including one repeat, with checked
groups of 3, 0 and 2 rows each. It compares both declared schemas and
a repeated projection, including escaped keys, a non-ASCII text value
with an escaped slash, empty text, and marker nulls. Lean guards pin
first binding error order for a path with an invalid DATE and missing
text and check that lexical failures and ingress errors precede lookup.

Generate the fixture with `lake build --wfail +Silmaril.Formats.Hive.Date32.Utf8.Checks`
and `lake env lean --run Silmaril/Formats/Hive/Date32/Utf8/Checks.lean "$tmp"`.
Use the pinned PyArrow command above with
`python -I /repo/scripts/hive-date-utf8-ingress-oracle/Oracle.py /out`.

## Canonical DATE and UTF-8 directories

[`Date32.Utf8.renderDirectory`](../../Silmaril/Formats/Hive/Date32/Utf8/Render/Defs.lean)
takes the same two typed virtual cells and URI options as the paired
read profile. The shared write-plan encoder visits the declared fields
in order. It prints present DATE values as canonical ISO dates and
checks that present text is valid UTF-8. Null cells bypass conversion.
After key and option validation, the URI renderer rejects the first
present value equal to the decoded null marker and percent-escapes the
components. An empty UTF-8 value emits an empty assignment.

The [public laws](../../Silmaril/Formats/Hive/Date32/Utf8/Render/Thms.lean)
recover the ordered entries and the exact typed row. A file declaration
whose checked parent is the rendered directory binds the same nullable
DATE and UTF-8 cells under the same options, preserving the supplied
literal filename and path. The encoder also supplies a left inverse
for the generic Hive write plan.

The PyArrow comparator parses eight actual Lean-rendered directories,
including both declared orders, empty text, escaped UTF-8 and escaped
keys and markers. Plain directories also match PyArrow's formatter.
The comparator shows the DATE marker and UTF-8 marker ambiguities
separately. PyArrow formats the corresponding present value and null
identically and reads the shared spelling as null. Lean refuses the
present collision.

Generate the directories with
`lake build --wfail +Silmaril.Formats.Hive.Date32.Utf8.Render.Checks`
and `lake env lean --run Silmaril/Formats/Hive/Date32/Utf8/Render/Checks.lean "$tmp/directories.tsv"`.
Use the pinned PyArrow command above with
`python -I /repo/scripts/hive-date-utf8-render-oracle/Oracle.py /out/directories.tsv`.

## Paired native manifest emission

[The manifest writer](../../Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Defs.lean)
takes a checked packed named table at the exact ordered schema. Its
physical columns are one nullable INT32 followed by one nullable opaque
BYTE_ARRAY. The two declared DATE and UTF-8 fields follow the physical
pair. The generic write plan diagnoses source and routing failures before
any file emission. Each first-seen directory gets one literal
`part-0.parquet` under its canonical directory, with source order
preserved within the bucket. An empty source yields an empty manifest.

The cut policy caps rows and groups per file and divides each nonempty
bucket into consecutive full groups followed by a possible shorter
group. [`MixedV1Writer.Multi`](../../Silmaril/Formats/Parquet/MixedV1Writer/Multi/Defs.lean)
applies its existing page, group, file-byte and total-row checks.
The pure emitter returns the whole manifest only after paired ingress
reopens the emitted bytes at their literal keys, reaches EOS, and
matches each group boundary and the exact typed rows from the route
plan. The manifest and the readback are materialized for this check.
The [public laws](../../Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Thms.lean)
relate emission to the independent first-directory route and the
ordered original rows within each bucket.

The pinned PyArrow comparator reads physical values and typed Hive
partition columns from six actual emitted Parquet files. It observes
the manifest and footer order explicitly. Fixtures include interleaving
across directories, two group sizes, empty and null cells, escaped
UTF-8, both virtual orders and opaque bytes that are invalid UTF-8.

Generate the files with
`lake build --wfail +Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Checks`
and `lake env lean --run Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Checks.lean "$tmp"`.
Use the pinned PyArrow command above with
`python -I /repo/scripts/hive-date-utf8-writer-oracle/Oracle.py /out`.

## Skip-open selection and projection of paired manifests

[`readSelected`](../../Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Pruning/Defs.lean)
uses the same literal resolver and paired reader as certified emission.
It admits all typed file declarations before evaluating the predicate
or opening bytes. It then opens only occurrences for which the
partition predicate returns SQL true. False and unknown leave the
payload unopened. Retained file occurrences and groups stay in their
original order. Any well-typed projection may reorder, repeat or
omit positions, including projecting zero columns.

A [successful strict read through EOS](../../Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Pruning/Thms.lean)
certifies that the rejected files would exhaust too. In that case,
the selected read agrees with stable typed post-filtering and
projection on ordered rows and EOS. For writer output, this becomes
a law over the original rows in first-seen directory order, stable
within each directory. For arbitrary supplied manifests, the
skip-open result is the strict scan on just the stable retained
occurrences. A reached retained error keeps its original path and
cause and the selected row prefix, including earlier groups from
that file. Skipped payload errors are absent from this result.

The fixture records calls to the literal resolver in the strict and
pruned comparison runs. Each virtual order reaches three strict
opens and one pruned open. The predicate accepts the leap day,
rejects year zero, and returns unknown for a null DATE. PyArrow
checks the selected native groups and repeated projection using
the same typed DATE filter and verifies the physical and virtual
values. Additional Lean controls exercise malformed declarations,
skipped unreadable payloads, retained open failures, and an indexed
second-group failure.

Generate the fixture and resolver trace with
`lake env lean --run Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Checks.lean pruning "$tmp" > "$tmp/opens.log" 2>&1`.
Use the pinned PyArrow command above with
`python -I /repo/scripts/hive-date-utf8-writer-oracle/Oracle.py /out /out/opens.log`.

## Atomic named-table import of selected rows

[`FromHiveDateUtf8.importSelected`](../../Silmaril/Formats/Relational/NamedTable/FromHiveDateUtf8/Defs.lean)
installs an in-memory typed table at a vacant name only after the
selected scan reaches EOS. The existing named-table importer gives
name conflicts precedence in the result. Admission errors carry their
typed declaration cause, and reached read errors carry the original file
and group cause. A failed or closed trace returns an error without an
updated database.

The [public laws](../../Silmaril/Formats/Relational/NamedTable/FromHiveDateUtf8/Thms.lean)
preserve every other table and give the exact projected schema and
ordered rows, including repeated positions and one empty row per
selected record for zero columns. For certified writer output the
reference is the filtered, projected original rows grouped by
first-seen directory and stable within each directory.

The import materializes the selected rows and inherits the paired
reader's configured limits. The nullable INT32 and opaque BYTE_ARRAY
leaves have maximum definition level 1 and repetition level 0. The
virtual DATE is an epoch-day value and UTF-8 is stored as bytes in the
typed rows. The comparator reads the original Parquet groups with
PyArrow and checks the installed labels, cells and zero-column
cardinality for both partition declaration orders.

Generate the named fixture with
`lake env lean --run Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Checks.lean named "$tmp" > "$tmp/opens.log" 2>&1`.
Use the pinned PyArrow command above with
`python -I /repo/scripts/hive-date-utf8-writer-oracle/Oracle.py /out /out/opens.log --named`.

## Selected opaque payload to native BinaryView IPC

[`ToIpc.convert`](../../Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/ToIpc/Defs.lean)
projects the physical nullable BYTE_ARRAY leaf of the paired scan to one
nullable Arrow BinaryView field under its declared name. The Parquet read
still checks both physical leaves of each reached group under the existing
paired reader limits. The IPC profile has a fixed one-column projection.
Physical INT32, virtual DATE and UTF-8 keys, mixed projections and
zero-width projections are outside this entry point.

All path declarations are checked before selection. Only SQL true opens
a file. Typed declaration failures and reached source outcomes are
returned ahead of writer admission. The adapter materializes the selected
batches and invokes the existing BinaryView writer after source EOS.
The writer applies its configured IPC and BinaryView limits. File
paths and group ordinals stay in the source semantics.

The [readback law](../../Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/ToIpc/Thms.lean)
recovers the exact field and nullable octets through IPC EOS, with one
record per retained group in order, including zero-row groups. A
descriptor-only stream represents a selection with no groups. A
present empty value remains distinct from null.

Generate genuine Parquet and IPC fixtures with
`lake env lean --run Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Checks.lean ipc "$tmp"`.
Use the pinned PyArrow command above with
`python -I /repo/scripts/hive-date-utf8-writer-oracle/Oracle.py /out --ipc`.
The comparator independently selects footer groups from both native
partition orders, including a repeated occurrence, then compares the
IPC schema, batch boundaries, raw slots and EOS. It compares a genuine
zero-row Parquet group and an empty selection separately and checks the
SHA-256 of each generated IPC stream.

## Selected virtual keys to native Date32 and UTF-8 IPC

[`ToTypedIpc.convert`](../../Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/ToTypedIpc/Defs.lean)
exports the two virtual keys as a nullable Arrow Date32 field and a
nullable plain UTF-8 string field in declaration order. It uses the
shared [Date32 and UTF-8 stream profile](../../Silmaril/Formats/Arrow/DateUtf8Stream/Defs.lean).
The schema uses the native DATE DAY tag and the plain UTF-8 tag. Records
reuse the existing signed four-byte and UTF-8 offset buffers. The DATE
slots remain signed epoch days, and the UTF-8 slots decode to strings
with the same bytes. Empty strings and nulls remain distinct.

The paired Parquet source checks both leaves of each retained group.
All path declarations are admitted before pruning. Typed admission
and reached source failures precede any sink admission, and only
source EOS allows export. The adapter materializes the selected batches.
The sink uses the existing Arrow IPC frame, row and cell limits. This entry
point exports exactly the virtual pair. The separate opaque BinaryView
entry point handles its own physical projection.

The [readback law](../../Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/ToTypedIpc/Thms.lean)
matches the complete typed schema and every batch through IPC EOS.
It preserves manifest occurrence and group order, including repeats
and explicit zero-row batches. An empty selection emits a schema and
EOS with zero record batches.

Generate the fixture with
`lake env lean --run Silmaril/Formats/Hive/Date32/Utf8/ManifestWriter/Checks.lean typed-ipc "$tmp"`.
Use the pinned PyArrow command above with
`python -I /repo/scripts/hive-date-utf8-writer-oracle/Oracle.py /out --typed-ipc`.
The comparator independently selects actual Parquet footer groups
in both partition declaration orders and compares Date32 days and
string slots against the native IPC and checks the generated stream
hashes. The fixtures include a pre-epoch
date, escaped UTF-8, null and empty keys, repeated occurrences, an
empty selection and a genuine zero-row group.

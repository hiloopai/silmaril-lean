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

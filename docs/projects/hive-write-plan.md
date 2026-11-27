# Pure Hive write planning

[`Hive.WritePlan.plan`](../../Silmaril/Formats/Hive/WritePlan/Defs.lean)
routes an ordered typed table to relative Hive directories and physical
row tables. The source schema extends the physical schema with the
explicitly supplied partition schema. Physical cells are preserved in
their original column order. A zero-column physical payload retains its
row count through the row list.

## Admission and errors

1. Check partition names and physical-name collisions using
   `TypedPartitions.checkSchema`, including on empty input.
2. Visit input rows in order. For each row, encode present virtual cells
   with the caller's checked dependent encoder in declared field order.
   Null bypasses the encoder. Encoder failure names the field and retains
   the caller's typed reason.
3. Render those entries with the existing `PartitionPath.render` policy.
   This checks required keys and rejects a literal cell whose encoded text
   equals the configured null marker. Parse the rendered directory using
   `PartitionPath.parse` with the same options before admitting the row.
   Path options apply to each row's directory. An empty table produces
   an empty plan after the schema check.
4. Group by exact rendered directory in first-occurrence order. Inside
   each group, preserve relative input order and every duplicate row.
   An empty partition schema routes rows to the dataset root.

A row failure reports its original zero-based index and its encoder,
render or parse error. The plan is returned only on complete success.
A caller can hand each physical table to a writer. Filename allocation,
file writes and catalog updates are outside this API. The grouping uses
the encoder's text as the key. Recovering typed virtual values on readback
additionally requires a suitable inverse for the caller's encoder.

The planner uses a stable partition of the remaining classified rows for
each directory. It makes at most one pass over the remaining rows for
each distinct directory. The plan groups interleaved input
rows, so only per-directory row order and first occurrence of directories
are guaranteed.

## Laws

[`plan_eq_reference`](../../Silmaril/Formats/Hive/WritePlan/Thms.lean)
equates the full result to an independent grouping that takes the
first-seen unique directory list and filters the original classified
rows once for each directory. Both use the checked classification above.

`plan_first_row_error_iff` characterizes exactly when the planner returns
a row error. The schema check succeeds, the index equals the length of an
all-successful input prefix, and classification of the next row gives the
same typed reason.

## Typed reconstruction

[`WritePlan.restore`](../../Silmaril/Formats/Hive/WritePlan/Restore/Defs.lean)
checks the supplied schema and parses and binds each bucket's directory
in order. It attaches the resulting typed partition tuple to every
physical row of the bucket using the existing typed materializer.
A path or binding error carries the bucket's literal directory and
the original error. The operation also accepts caller-supplied buckets.

[`restore_plan_eq_groupedRows`](../../Silmaril/Formats/Hive/WritePlan/Restore/Thms.lean)
states the result for a successful plan. Planning and restoration use
the same physical schema, partition schema, and path options. The only
codec premise is a left inverse for successful present-cell encodings.

```text
For each declared field and each present value and text,
  encode(field, value) = ok(text) implies decode(field, text) = ok(value).
```

Nulls are explicit in the partition entries and bypass both callbacks.
Successful planning supplies render admission, including the configured
nonempty null marker, required keys, and rejection of literal sentinel
collisions. [`PartitionPath.parse_render_of_ok`](../../Silmaril/Formats/Hive/PartitionPath/Thms.lean)
proves exact entry recovery under those same options. The left inverse
then ensures that a shared directory reconstructs the original tuple
for every row routed there. Successful planning by itself permits a
lossy caller encoder. A Lean regression demonstrates this by encoding
the original text as `fixed` and recovering that replacement.

The theorem equates restoration to grouping the *full original rows*
by their admitted directories. It preserves first-seen directory order,
within-directory row order, duplicates, and nullable typed cells.
Grouping changes the order of interleaved directories.

The [reconstruction checks](../../Silmaril/Formats/Hive/WritePlan/Restore/Checks.lean)
read the five [pinned PyArrow files](../../tools/parquet-flat-scan/fixtures/hive-write-plan)
in explicit first-seen directory order with the existing flat Int32
reader. They compare the parsed and typed result to the grouped input.
The same fixture generator and hashes below verify membership and
bytes independently. Lean alone asserts reconstruction order.

## Planning from a checked snapshot scan

[`Manifest.planSnapshots`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/WritePlan/Defs.lean)
takes an already prepared typed manifest. It scans immutable snapshots in
literal occurrence order with the full augmented schema and the caller's
partition predicate. The strict scan observes a reached file's terminal
outcome even when its partition is filtered out.

`WritePlan.plan` runs only after observed EOS. Earlier termination returns
`.scan` with the original typed outcome and the exact selected ordered
prefix. Open and group-read failures keep their literal file path and
payload, including the group index when present. An encoder or other
write-plan error returns `.planning` after EOS. No files or no selected
rows yield an empty plan when the scan reaches EOS. A failure with an
empty selected prefix remains a scan error.

[`planSnapshots_eq_reference`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/WritePlan/Thms.lean)
relates the composition to the independent checked snapshot row denotation
and the write-plan reference. A successful result groups by the first
occurrence of each directory among **selected rows**, with stable physical
payloads within each bucket, including duplicate rows and null cells.
Grouping can change cross-directory interleaving. Lookup and error paths
retain their original spellings. Output directories use the supplied
write-plan options and encoder.

The [snapshot-to-plan checks](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/WritePlan/Checks.lean)
reuse the [pinned PyArrow V1 and V2 inputs](parquet-flat-scan.md#independent-fixtures).
They include EOS with interleaved directory occurrences, null cells,
no files, no selected rows, and a V2 page-header failure at byte 234
in zero-based group 1. The derived damaged fixture has SHA-256
`37492c1b898d2f65f9601e4cda5f17f50ee296702fedc97abc55910141a88cac`.
The failure is checked with the partition both retained and filtered,
including an empty selected prefix. This is a pure composition
over supplied snapshots and rows.

## Pinned checks

[PyArrow membership oracle](../../scripts/hive-write-plan-oracle/Oracle.py) ·
[Parquet hashes](../../scripts/hive-write-plan-oracle/fixtures.sha256) ·
[Lean checks](../../Silmaril/Formats/Hive/WritePlan/Checks.lean)

The supported-domain fixture uses [pinned PyArrow 26.0.1](arrow-parquet-coverage.md#pinned-specifications)
with nullable UTF-8 and Int32 virtual cells. It checks five literal
directories and compares physical and logical row membership with
multiplicities. The rows include escaped slash and equals, Japanese text,
null, empty text and an interleaved repeated row. Separate Lean guards
assert first-directory occurrence and stable row order. The sentinel
collision is a Lean rejection with an exact index and key.

To regenerate, use the CPython 3.14.7 image and hash-pinned x86-64 binary
wheels below.

```sh
tmp="$(mktemp -d)"
docker run --rm --network host -v "$PWD/scripts/hive-write-plan-oracle/Oracle.py:/Oracle.py:ro" \
  -v "$tmp:/out" python@sha256:51dafde81dbdb6ebde285137a295cf18a47ca95234fe388a343719cb97305b3d \
  sh -ec 'printf "%s\n" \
            "pyarrow==26.0.1 --hash=sha256:7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814" \
            "numpy==2.5.5 --hash=sha256:c48960d420e90cf305cb1fde0d4e6082cc90512cda87a9acf0b6e04e91cf4abe" \
            > /tmp/oracle-requirements.txt
          python -m pip install --only-binary=:all: --require-hashes -r /tmp/oracle-requirements.txt
          python -I /Oracle.py /out/fixtures'
(cd "$tmp/fixtures" && sha256sum -c "$OLDPWD/scripts/hive-write-plan-oracle/fixtures.sha256")
diff -r tools/parquet-flat-scan/fixtures/hive-write-plan "$tmp/fixtures/data"
lake build --wfail +Silmaril.Formats.Hive.WritePlan.Checks +Silmaril.Formats.Hive.WritePlan.Restore.Checks
```

## Checked native files from a named table

[`WritePlan.FlatInt32.emit`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/Defs.lean)
takes a packed named nullable Int32 table with one selected physical
leaf followed by the declared typed partition fields. It matches the
full ordered schema and runs the existing Hive write plan, keeping
its schema, key, marker, and first indexed row errors. Only after
routing succeeds does it validate the literal paths and emit a native
Parquet file for each bucket. The optional unannotated INT32 leaf is
written as one uncompressed PLAIN V1 page in one row group, using the
existing writer's page and file caps.

Each bucket uses `part-0.parquet` under its checked directory, or at
the root if there are no partition keys. The manifest is an ordered
list of relative paths, physical row counts, and complete bytes.
Its order is first directory occurrence. Within each file, duplicate
and null payloads retain their source-relative positions. No rows
produce an empty manifest after schema admission. A later path or
writer failure returns its typed cause without a manifest. The API
constructs pure bytes and paths.

[`restore`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/Defs.lean)
reads each supplied path in manifest order and checks its lexical
shape and leaf spelling. The native snapshot reader must reach EOS
with the requested INT32 field, one batch and the declared row count.
After all physical reads succeed, the existing typed Hive restoration
binds the directories and reconstructs the full rows. The same path
options are used in both directions. Null partition cells use the
configured marker, and a present value that encodes to the marker
is refused by the existing planner.

`emit_eq_reference` identifies the exact result of named admission and
the independent routing reference. `restore_emit` proves that the
actual emitted bytes and paths restore the original full rows grouped
in first-seen directory order and stable within each bucket, under
the existing successful-cell encoder/decoder left inverse.
It also pins the ordered manifest paths and per-file row counts.

[The PyArrow oracle](../../scripts/hive-native-int32-oracle/Oracle.py)
reads four actual Lean-emitted files through Hive partitioning in the
manifest's explicit order. It confirms eight nullable rows, the
schema and physical group counts, and that exactly the listed files
were emitted. Use the existing CPython, PyArrow, and NumPy pins
listed above.

```sh
lake build --wfail +Silmaril.Formats.Hive.WritePlan.FlatInt32.Checks
lake env lean --run Silmaril/Formats/Hive/WritePlan/FlatInt32/Checks.lean /tmp/hive-native-int32
python -I scripts/hive-native-int32-oracle/Oracle.py /tmp/hive-native-int32
```

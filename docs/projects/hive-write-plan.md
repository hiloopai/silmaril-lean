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

### Partition-only restore

[`restorePruned`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/Prune/Defs.lean)
checks the schema once, then visits each literal manifest occurrence in order.
For each reached occurrence it checks the relative path and fixed leaf,
parses the partition directory with the supplied marker options, and binds
its nullable cells before evaluating the predicate. Only `some true` selects
an occurrence. `some false` and `none` skip its entire Parquet payload,
including any footer, page, schema, or advertised row-count checks.

The first reached failure aborts with no partial table. A file error records
its original zero-based manifest index, literal path, and typed cause. This
index counts duplicates and skipped occurrences. A malformed path or typed
binding still fails if its payload would have been skipped. A selected file
uses the same native Parquet reader and row-count checks as `restore`.

[`restorePruned_eq_filter`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/Prune/Thms.lean)
proves exact agreement with applying the partition predicate to each row
following a successful full restore. This preserves manifest order and
physical row order within each occurrence. Both readers share the same typed
path binder, so the law covers explicit nulls, the default marker, and
caller-selected markers. [`restorePruned_emit`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/Prune/Thms.lean)
composes with emission under the same path options and successful-cell codec
left inverse. The reference routes the original rows by first-seen directory,
keeps their order within each directory, and then applies the stable filter.

The pinned PyArrow oracle also checks the selected fragments and rows on
eight actual Lean-emitted Parquet files across default and escaped custom
markers. The manifest is passed in explicit order, with one thread for
readback. The Lean guards additionally check duplicate occurrences, empty
selection, typed path errors before the predicate, and an unreadable
payload that succeeds only when skipped. Use the same pinned Python
setup as above.

```sh
lake build --wfail +Silmaril.Formats.Hive.WritePlan.FlatInt32.Checks
lake env lean --run Silmaril/Formats/Hive/WritePlan/FlatInt32/Checks.lean pruning /tmp/hive-pruned
python3 scripts/hive-native-int32-oracle/Oracle.py /tmp/hive-pruned --pruning
```

### Bounded native row groups

[`WritePlan.FlatInt32.RowGroups`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Defs.lean)
adds an opt-in policy to the native manifest. Set a positive `rowsPerGroup`
and caps for `maxGroupsPerFile` and `maxRowsPerFile`. Each nonempty routed
bucket becomes one file with contiguous full groups and a shorter final
group when needed. An empty routed table produces an empty manifest. The
single-group entry points retain their original output.

The writer reuses the existing INT32 page measurement and writer and the
shared Compact group footer. It measures pages and caps the complete file
before materializing page bodies. Each file retains its literal path, total
row count and ordered group counts. Emission certifies the actual bytes
through the same bounded checked reader used for restore. The reader checks
the deterministic cut vector, footer total and group counts,
the unannotated physical schema, and each group's decoded slots at its original ordinal. Size caps are per
file and per group. The input table and final manifest are in memory.

[`restore_emit`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Thms.lean)
relates each file to the independent write-plan reference and reconstructs
first-seen partition order and stable row order within each bucket with the
same marker options and codec left inverse. The cut, slot and footer laws
pin the per-file count and ordered group sizes.

`restorePruned` checks each path and its typed partition values before applying
the predicate. Only `some true` checks the file payload and its dimensions.
A reached failure returns the original zero-based manifest occurrence and
literal path with its typed cause, including the original group ordinal on a
decode failure. The operation returns no partial table. On a successful full
restore the pruned result equals stable filtering over the typed partition
values. The API is pure.

The independent PyArrow oracle reads the actual emitted default- and
custom-marker files one row group at a time and also checks the ordered Hive
rows and pruned fragments. The Lean corruption control changes a later group
header in a selected file, verifies its earlier group still decodes, and
checks the enclosing file and group ordinals. A separate Lean control skips
a damaged payload. Use the pinned Python setup above.

```sh
lake build --wfail +Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Checks
lake env lean --run Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Checks.lean /tmp/hive-row-groups
python3 scripts/hive-native-int32-row-groups-oracle/Oracle.py /tmp/hive-row-groups
```

### Native row-group events

[`RowGroups.Events.scanPruned`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Events/Defs.lean)
admits the same schema and policy as relational restore. It checks the
partition path before its predicate and opens only selected payloads. Each
successful group contributes one aligned batch with the literal path,
zero-based manifest occurrence and zero-based footer ordinal. Repeated
literal paths retain separate occurrence indices. A failed group retains
all prior batches, including earlier groups of that file. Exhaustion
produces exactly EOS, including for an empty or entirely pruned manifest.

The scan produces a pure completed trace. `Trace.toArrow` exposes a standard
Arrow trace with the same batches and terminal outcome. The tagged view
retains positions alongside those batches. `Trace.project` applies a
logical projection and preserves positions and explicit row counts, even
when the output has width zero or repeats columns. Skipped payloads remain
unchecked.

[`finish_scanPruned`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Events/Thms.lean)
identifies the exhausted relational result with `restorePruned` and
preserves the same typed errors. The file and manifest prefix laws give
the complete ordered batches before the first reached failure and its
original cause. The independent PyArrow replay reads each selected group
separately and compares its occurrence, path, ordinal, count and typed
slots to the Lean events in both marker profiles.

```sh
lake build --wfail +Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Checks
lake env lean --run Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Checks.lean events /tmp/hive-row-group-events
python3 scripts/hive-native-int32-row-groups-oracle/Oracle.py /tmp/hive-row-group-events --events
```

### Native Arrow IPC from selected groups

[`RowGroups.Events.ToIpc.convert`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Events/ToIpc/Defs.lean)
finishes the partition-pruned scan before admitting IPC output. The narrow
projection always writes the physical payload first. Optional typed
partition positions supply nullable INT32 columns in caller order.
The writer receives one record per selected group in trace order, with
its explicit row count. File paths and group positions remain on the source
trace. An entirely pruned manifest writes its selected schema and EOS.

[`convert_readback`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Events/ToIpc/Thms.lean)
uses the existing ordered writer and native pull laws to recover the exact
fields, row counts and nullable slots through EOS. `convert_scan_error`
preserves an admission or reached scan error before any writer budget is
applied. A failed conversion returns its typed cause. The manifest writer,
relational restore and native reader keep their existing interfaces.

The pinned PyArrow replay opens the emitted IPC streams and compares each
record with an independent read of its selected Parquet group in the
existing fixtures. It checks nullable field declarations, record counts,
values and exact carrier consumption for the payload-only, partition
projection and schema-only streams under both marker profiles.

```sh
lake build --wfail +Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Checks
lake env lean --run Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Checks.lean ipc /tmp/hive-row-group-ipc
python3 scripts/hive-native-int32-row-groups-oracle/Oracle.py /tmp/hive-row-group-ipc --ipc
```

### Restriction of the unpruned tagged trace

[`scanPruned_eq_restrict`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Events/Pruning/Thms.lean)
identifies the complete result of the skip-open scan with stable batch
restriction of `scanUnpruned`. The reference uses the same typed path
binder and predicate at each original occurrence index. Every kept batch
retains its literal path, occurrence index, footer ordinal, row count and
cells. The restriction carries the terminal outcome through unchanged.

The proof requires each reached, successfully path-bound rejected file to
decode through all its groups. A file is reached when the unpruned scan of
its strict prefix exhausts. The premise permits a selected failure and
places no requirement on a suffix beyond that failure. Schema and policy
admission are shared. Both scans report a reached malformed path before
pruning. A rejected damaged payload can stop the unpruned trace, while
skip-open pruning can continue and reach EOS. The controls exercise both
that case and a selected failure before unreachable rejected damage.

`ToIpc.convert_readback_restrict` connects the same restriction to actual
native IPC pull readback on successful writing. The proof also recovers
exhaustion of the unpruned reference under its reached-decode premise.
The IPC fields and counts come from the selected groups, and the file and
footer tags stay on the source trace.

The pinned PyArrow replay uses an explicit ordered inventory with repeated
literal files, including the null partition in each marker mode. It reads
the source groups independently and compares the unpruned tags, the
selected tags at their original positions, and the decoded IPC records.

```sh
lake build --wfail +Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Checks
lake env lean --run Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Checks.lean repeat /tmp/hive-row-group-repeat
python3 scripts/hive-native-int32-row-groups-oracle/Oracle.py /tmp/hive-row-group-repeat --repeat
```

### Ordered IPC projection after partition restriction

[`ToIpc.convertProjected`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Events/ToIpc/Projection/Defs.lean)
selects from the wide payload/key layout. The wide width is exactly one
plus the length of the supplied typed key list, including repeated keys.
Each selected position is checked at that width. The output width is the
selection length, and its field and cell order follows the selection.
A zero-width selection still emits one record per selected group with its
explicit row count. The original `convert` entry point retains its field
order and wire bytes.

[`convertProjected_readback_restrict`](../../Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Events/ToIpc/Projection/Thms.lean)
composes stable group restriction with the existing native projection
observation. The reached rejected payload hypothesis is the same as for
tagged restriction. Both the wide and projected writes must succeed, and
each pull read uses the limits of its own write. Through EOS, selecting
positions of the decoded wide stream gives the exact ordered fields,
nullable cells and counts of the direct projected stream. Repeated
positions can increase the projected width and exhaust its writer cap.

The pinned PyArrow oracle independently decodes the wide, repeated and
zero-width streams for both null-marker profiles over the repeated
manifest. It compares the projected output to positional selection of the
wide readback and checks every group count even at width zero.

```sh
lake build --wfail +Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Checks
lake env lean --run Silmaril/Formats/Hive/WritePlan/FlatInt32/RowGroups/Checks.lean projection /tmp/hive-ipc-projection
python3 scripts/hive-native-int32-row-groups-oracle/Oracle.py /tmp/hive-ipc-projection --projection
```

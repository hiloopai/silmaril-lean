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

# Mixed GZIP V2 Parquet TIMESTAMP to native Arrow IPC

`Timestamp.Leaf.Gzip.Dispatch.V2.convert` opts into one modern
flat INT64 TIMESTAMP leaf in a checked snapshot. Each selected chunk
uses GZIP and one of three layouts.

| Original chunk | Admitted data pages |
| --- | --- |
| No dictionary offset | PLAIN V2 only |
| Leading PLAIN dictionary, no PLAIN data header | RLE_DICTIONARY V2 only |
| Leading PLAIN dictionary, at least one PLAIN data header | Nonempty RLE_DICTIONARY V2 prefix followed by a nonempty PLAIN V2 suffix |

The selected footer entry supplies the dictionary offset. Each route
frames the original chunk once. The dictionary-backed route inspects
those original data headers once to choose its strict reader, then
hands it the same frames. The PLAIN route uses the dedicated
`Timestamp.Leaf.Gzip.V2` reader. Both dictionary-backed routes reuse the
standalone planners and decoders. Each chosen route returns its exact
standalone result and typed errors. The strict entry points retain their
individual admission rules.

The proofs bind each group to the selected footer entry, original frame
chain, and declared row count. Each V2 page retains its raw definition
prefix and validates zero repetition bytes, row and null counts, and the
exact flag-selected suffix extent. A present Parquet CRC covers the
entire stored body. Compressed suffixes and leading dictionaries also
verify the GZIP member CRC-32 and ISIZE. The signed nullable counts remain
in their original order.

Native Arrow V5 readback through EOS preserves the field name,
nullability, original unit, canonical UTC or absent local timezone, and
one batch per original footer group. Earlier complete groups remain
in the event trace on failure. The first group error reaches the
converter before IPC writer admission. Within a group, framing and
admission errors take precedence over the data decoding they guard.

## Independent evidence

Two genuine PyArrow 26.0.1 files each contain both dictionary-only and
fallback groups. Nullable UTC nanos include signed INT64 endpoints, nulls,
and both V2 storage flags. Required local micros exercise zero level
bytes and absent Parquet CRCs. Two separately labeled assembled files
insert PLAIN-only groups from genuine PyArrow files. The assembly
copies each original column chunk verbatim and rewrites footer offsets
and group order. PyArrow independently reads the assembled Parquet
files and the actual Lean-emitted IPC for all four cases.

Thrift and zlib verify original frame boundaries, flags, raw levels,
checksums and GZIP member extents. The comparator reconstructs signed
slots independently and checks the Lean dispatcher against each strict
reader at every group. Mutated controls verify late PLAIN, reference,
dictionary and fallback errors, phase refusals, and an earlier failing
group followed by another fault.

[Public dispatch laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Gzip/Dispatch/V2/Thms.lean) ·
[PLAIN V2 laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Gzip/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-gzip-dispatch-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-gzip-dispatch-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-gzip-dispatch-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-gzip-dispatch-v2-oracle/check.py
```

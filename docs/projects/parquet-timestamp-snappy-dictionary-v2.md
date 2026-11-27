# Selected Snappy V2 Parquet TIMESTAMP dictionaries

`Timestamp.Leaf.Dictionary.Snappy.V2.convert` opts into codec 1 on one
checked modern flat INT64 TIMESTAMP leaf. Each selected chunk requires
one leading PLAIN dictionary and a nonempty sequence of RLE_DICTIONARY
Data Page V2 frames. The V2-only planner checks the original page kind
and then uses the shared Snappy schema and tag checks. V1 data pages
and PLAIN fallback receive typed header errors. The broader dictionary
and fallback APIs retain their existing page-version policy.

The checked chunk uses the original selected footer column and
dictionary and data offsets. Its frame chain covers the exact selected
chunk within the stored-byte cap. Header admission and the declared
group slot total are checked before expanding the dictionary. The
dictionary and data decoders check a present Parquet CRC across the
original stored body before decompression. The dictionary is decoded
within byte and entry bounds as exact signed PLAIN words.

Data Page V2 leaves the definition prefix raw and has zero repetition
bytes. The original storage flag chooses an exact literal reference
suffix or one bounded Snappy block consumed in full. The raw mask,
declared null count and exact hybrid index stream reconstruct the
original nullable slots with lookups into that chunk's own dictionary.
Header and admitted data-page failures keep their original ordinal and
absolute offset. These are separate validation stages.

Native Arrow V5 IPC preserves the selected field name, nullability,
time unit, UTC or local interpretation, and exact signed nullable ticks
through EOS, with one batch per original footer group. The event trace
retains every complete group before the first source failure. That
failure takes precedence over writer admission.

## Independent evidence

Two genuine PyArrow 26.0.1 files cover three groups each, including
nullable UTC nanoseconds with stored CRCs and required local
microseconds without them. The signed endpoints, negative counts, zero and null slots appear in
the producer inputs. Both storage flags occur in each file. Thrift and zlib check original
annotations, codec IDs, frame boundaries, flags and CRCs. An
independent hybrid decoder and PyArrow's Snappy implementation check
exact signed dictionary and data words. PyArrow reads the actual
Lean-emitted streams through EOS.

Separate controls cover a late dictionary CRC failure, a late
raw-level CRC failure, a malformed compressed reference suffix, a
genuine late producer fallback, and a labeled mixed-version assembly
of unchanged PyArrow chunks. The V1 assembly reads in PyArrow and
through the broader Snappy dictionary API. The strict adapter checks
eleven typed refusals and five complete prefixes.

[Public laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Dictionary/Snappy/V2/Thms.lean) ·
[Comparator](../../scripts/parquet-timestamp-snappy-dictionary-v2-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-snappy-dictionary-v2-oracle/fixtures.json) ·
[Pinned Python setup](parquet-timestamp-gzip-dictionary-v1.md)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-snappy-dictionary-v2-oracle/Axioms.lean
/tmp/parquet-timestamp-gzip-dictionary/bin/python -I scripts/parquet-timestamp-snappy-dictionary-v2-oracle/check.py
```

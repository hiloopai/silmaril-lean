# Selected V2 Parquet DATE dictionary fallback with Zstandard

`Parquet.Date.Leaf.Fallback.Zstd.V2` uses the original checked
flat INT32 DATE snapshot and one selected physical ordinal. It
checks codec 6, original dictionary and data offsets, and ordered
frames. One leading PLAIN dictionary is followed by a nonempty
RLE_DICTIONARY prefix and nonempty PLAIN suffix of V2 data pages.
The shared sequence checker returns the original ordinal and
absolute offset on the first reentry into dictionary encoding.
Row and expanded-byte totals include both phases. The expansion
budget also includes the leading dictionary. Existing strict
readers keep their admission.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Zstd/V2/Defs.lean) ·
[Selected DATE binding](parquet-date-selected-leaf.md)

Both phases use the existing Zstandard V2 readers on their original
bytes. Any stored Parquet CRC is verified over the complete frame
payload before interpreting levels or expanding values. The raw
definition prefix supplies the presence mask. Each resolved flag
selects the exact raw suffix or a bounded dictionary-free
Zstandard frame. The reference prefix uses checked Hybrid
indices into the original signed dictionary. The PLAIN suffix
decodes the exact signed words directly. The wire laws connect
the phase evidence to footer counts and preserve ordered nullable
slots in native Date32 IPC batches through EOS. An indexed
source failure retains the complete earlier groups and precedes
writer limits.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Fallback/Zstd/V2/Thms.lean) ·
[Dictionary-only V2 DATE](parquet-date-zstd-dictionary-v2.md) ·
[PLAIN V2 DATE](parquet-date-zstd-v2.md)

## Pinned comparison

Two genuine PyArrow 26.0.1 files use dictionary thresholds of 12
and 8 bytes. The nullable CRC-bearing file has two reference pages
per group and exercises both flags in each phase. The required
fixture has one reference page per group and no stored CRCs.
Together they cover four dictionaries, 18 original data pages
and both signed Int32 endpoints. Thrift checks original offsets
and headers, libzstd 1.5.7 checks frame extents, zlib checks
stored CRC, and the independent Hybrid runner checks levels and
reference order. PyArrow reads the source and Lean-emitted IPC.

The 15 controls keep genuine V1 and dictionary-only files separate
from edited headers, CRC and frame mutations, and low budgets.
The reentry mutations include a later unsupported header and
check the earlier refusal and complete earlier group with a
zero-batch writer limit.
[Comparator](../../scripts/parquet-date-zstd-fallback-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-zstd-fallback-v2-oracle/fixtures.json) ·
[libzstd 1.5.7](https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-zstd-fallback-v2/Axioms.lean
python3 -I scripts/parquet-date-zstd-fallback-v2-oracle/check.py
```

# Per-group GZIP DATE dispatch with V1 data pages

`Parquet.Date.Leaf.Gzip.Dispatch.V1` is an opt-in reader for a selected flat
INT32 DATE leaf. It retains the strict DATE binding and original snapshot,
column path, footer indexes, and chunk spans. Each row group uses one
leading GZIP PLAIN dictionary. The reader uses fallback planning when the
original framed data contains a V1 PLAIN header, and dictionary-only
planning when it does not. The selected planner checks every version and
encoding in its prescribed order. The same checked chunk and dictionary
supply the subsequent body reads.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/Dispatch/V1/Defs.lean) ·
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/Gzip/Dispatch/V1/Thms.lean)

For a group with its original checked frame list, the dispatch result agrees
with the dedicated reader for that branch, for both signed nullable slots
and typed errors. Dictionary errors map into the same chunk or header
constructors with the original cause and coordinate. An error exits the
selected route immediately. Successful reads retain the selected profile's
original frame, CRC, whole-member, mask, and index or PLAIN-value witnesses.
Each chunk shares the existing stored, expanded, and row caps.
[Dictionary-only V1](parquet-date-gzip-dictionary-v1.md) ·
[Dictionary fallback V1](parquet-date-gzip-fallback.md)

Native Date32 IPC preserves the exact field descriptor, footer-order
groups and signed optional days through exact EOS. An original indexed
source error preserves the earlier complete group prefix and takes
precedence over IPC writer limits.

## Pinned comparison

Two genuine PyArrow files each have dictionary-only, dictionary-to-PLAIN,
and dictionary-only row groups in that order. A short dictionary limit
and repeated values in the outer groups produce those phases directly.
The fixtures cover nullable CRC-bearing and required CRC-absent fields.
Thrift and zlib check original frames, CRCs, levels and signed values.
PyArrow independently checks the Lean-emitted Date32 IPC.

Labeled controls include damaged CRCs and inner members, a reentry header
mutation, and two damaged groups where the earlier failure wins. Genuine
PLAIN-only and V2 files exercise the profile boundary.
[Comparator](../../scripts/parquet-date-gzip-dispatch-v1-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-gzip-dispatch-v1-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V1.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-date-gzip-dispatch-v1/Axioms.lean
python3 -I scripts/parquet-date-gzip-dispatch-v1-oracle/check.py
```

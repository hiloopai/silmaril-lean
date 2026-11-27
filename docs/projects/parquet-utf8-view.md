# Parquet STRING to native Arrow Utf8View

`Parquet.Plain.ByteArray.Utf8.convert` exports one named, flat,
required or optional BYTE_ARRAY leaf as an Arrow IPC V5 Utf8View
field. The checked PLAIN file reader supplies the original selected
groups under the usual file, row, and page caps. The physical profile
admits codec 0 and PLAIN Data Page V1 with the existing RLE level
contract or Data Page V2. The physical page checks reject CRC-bearing pages.

The annotation comes from the serialized leaf at the physical
binding's original column ordinal. The reader accepts three annotation forms.

- LogicalType field 10 with exactly STRING member 1 and an empty
  marker payload.
- ConvertedType field 6 with the UTF8 code 0, in the absence of
  LogicalType.
- Both of those forms together.

Both present fields must agree. A different or malformed modern
marker, a nonzero converted code, and a missing annotation each
produce a typed refusal. The source validity check runs before IPC
admission. After a complete physical group read, every present slot
is decoded with strict `String.fromUTF8?`. An invalid slot reports its
zero-based group and logical row position. Physical failures retain
their original indexed error. The opaque BYTE_ARRAY exporter exposes the same bytes as BinaryView.

`openFile_wire` ties the raw annotation and physical reader to the
same checked footer leaf. `readGroup_wire` retains the original
framed PLAIN group and proves that encoding the resulting nullable
strings recovers the original slot bytes. `convert_readback` ties
the native descriptor and all string batches through exact EOS to the
checked group list. `convert_first_error` preserves the first failed
group cause before IPC emission.

The oracle uses PyArrow 26.0.1 and Thrift 0.25.0. It independently
reads nullable and required STRING values from V1 and V2 producer
files, including distinct composed and decomposed spellings, nulls,
empty strings, multibyte values, and embedded NUL. The V2 empty group
gets an explicit zero-slot page per chunk via a Thrift edit, preserving
the original nonempty producer pages and `[5, 0, 4]` batch counts.
The late text edit changes a payload octet without changing the
lengths and fails at group 2, slot 1. A separate PLAIN length edit
fails at group 2, column 1, page 0, header offset 142. Footer edits
exercise modern-only, converted-only, missing, inconsistent, and
malformed annotations.

[Definitions](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Defs.lean) ·
[Laws](../../Silmaril/Formats/Parquet/Plain/ByteArray/Utf8/Thms.lean) ·
[Fixture hashes](../../scripts/parquet-utf8-view-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Checks \
  +Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Checks
python3 scripts/parquet-utf8-view-oracle/check.py "$(mktemp -d)"
```

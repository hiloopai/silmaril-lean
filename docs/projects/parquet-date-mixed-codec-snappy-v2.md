# Selected Parquet DATE V2 dispatch across GZIP, Zstandard and Snappy

`Parquet.Date.Leaf.MixedCodec.V2.WithSnappy` binds one flat INT32 DATE
leaf by physical ordinal in a checked snapshot. One lookup of the
original selected footer codec ID chooses the strict V2 dispatcher.
Codec 1 selects Snappy, codec 2 GZIP and codec 6 Zstandard. Each codec
retains its strict PLAIN-only, dictionary-only and one-way fallback
profiles. The selected dispatcher returns its first error directly.
[Definitions](../../Silmaril/Formats/Parquet/Date/Leaf/MixedCodec/V2/WithSnappy/Defs.lean) ·
[Snappy V2 dispatch](parquet-date-snappy-dispatch-v2.md) ·
[GZIP and Zstandard V2 dispatch](parquet-date-mixed-codec-v2.md)

The old two-codec entry point shares its GZIP and Zstandard selector
with the new API. The agreement law covers its complete result outside
codec 1, including lookup failures and the original unsupported codec
ID. The new API wraps its errors in `twoCodec` and the Snappy
dispatcher's errors in `snappy`. The existing entry point returns
`unsupportedCodec 1` on Snappy input.

Each successful route retains its original selected frames, stored CRC
and flag-selected suffix witnesses. The first indexed source failure
retains every earlier complete event batch and takes precedence over
writer limits. Native Date32 IPC retains the exact descriptor and every
footer-order batch of signed nullable slots through EOS.
[Public laws](../../Silmaril/Formats/Parquet/Date/Leaf/MixedCodec/V2/WithSnappy/Thms.lean)

## Pinned comparison

A labeled mixed-codec assembly contains eight original chunks from
six genuine PyArrow 26.0.1 parents. The comparator independently checks
the parent files, copies chunks byte for byte and relocates the footer
offsets. The selected DATE leaf follows an unannotated INT32 neighbor.
The assembly exercises all three Snappy profiles, including both V2
storage flags in each Snappy fallback phase, and PLAIN GZIP and
Zstandard. The previous two-codec oracle exercises the GZIP and
Zstandard dictionary and fallback profiles. PyArrow reads the assembly
and the Lean-emitted IPC.

Ten controls compare full strict results and event prefixes. They
include one stored CRC failure per codec, failures in two codecs,
Snappy fallback reentry, a Snappy body labeled Zstandard, a synthetic
unknown codec ID and genuine uncompressed Parquet DATE.
[Comparator](../../scripts/parquet-date-mixed-codec-snappy-v2-oracle/check.py) ·
[Fixture pins](../../scripts/parquet-date-mixed-codec-snappy-v2-oracle/fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.Thms \
  +Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true \
  tests/formats/parquet-date-mixed-codec-snappy-v2/Axioms.lean
python3 -I scripts/parquet-date-mixed-codec-snappy-v2-oracle/check.py
```

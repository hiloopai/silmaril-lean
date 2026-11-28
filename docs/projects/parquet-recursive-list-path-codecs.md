# Bounded codec profiles for canonical signed LIST paths

ListPath reads one signed INT32 or INT64 leaf under a bounded canonical
LIST chain from an unindexed PLAIN V1 or V2 column. The original column
metadata selects the codec separately for each row group.

| ID | Admitted payload |
| --- | --- |
| 0 | UNCOMPRESSED |
| 1 | Bounded raw Snappy block |
| 2 | Bounded single GZIP member |
| 6 | Bounded single Zstandard frame with compression dictionary ID zero |
| 7 | Bounded LZ4_RAW block |

Deprecated LZ4 codec 5, Brotli, other codec IDs, Parquet dictionary
encoding, indexed pages and pageless groups are outside this profile.
The GZIP controller-call and Zstandard window and command limits
use the existing repeated-leaf defaults and adapters.
[Snappy profile](parquet-recursive-list-path-snappy.md)

In V1, optional CRC covers the original stored body, and the entire
body uses the checked column codec. The compressed frame coordinates
stay absolute. Its prefixed Hybrid and value-section coordinates refer
to the decoded body. In V2, the original stored payload supplies both raw
level slices. A true flag dispatches the value suffix through the
original codec. A false flag passes the stored suffix directly to the
signed-word decoder without codec work. The original header contributes
to both exact footer totals.

V1 carries live ancestors across legal continuations, and V2 requires
complete-row boundaries and checks the slot, row and null counts.
Successful native reads preserve exact group rows, Events and IPC
observations. The first reached page error retains its original group,
path, frame offset and ancestry cursor. Empty projection retains
completed prior groups and the source error takes precedence over
IPC output limits. [V1 reader](parquet-recursive-list-path-v1.md) · [V2 reader](parquet-recursive-list-path-v2.md) · [Events](parquet-recursive-list-path-events.md) · [Arrow V5 IPC](parquet-recursive-list-path-to-ipc.md)

## Verification

Pinned PyArrow supplies genuine multipage V1 and V2 inputs for all three
new codecs at depths three and six with both signed widths. Pinned
liblz4, zlib and libzstd and independent Compact, Hybrid, CRC and
signed-word checks verify 29 inputs and 180 original frames. The set
includes 79 raw V2 suffixes and one labeled five-codec file assembled
from unchanged original producer frames. Authored GZIP and Zstandard
raw bypasses decode under zero controller and zero window and command
budgets. Both projections produce 58 Lean IPC streams through exact EOS.

Thirty-two typed controls cover byte caps, the deprecated LZ4 ID,
exact block and frame consumption, a second GZIP member and a second
Zstandard frame, trailer and checksum failures, compression dictionary
ID, and both header-inclusive totals. Late codec failures retain
the original address and complete prior-group prefix, including four
prior groups in the mixed-codec Zstandard control.
[Producer, reference and byte pins](../../scripts/parquet-recursive-list-path-codecs-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-list-path-codecs-oracle/Axioms.lean
python3 scripts/parquet-recursive-list-path-codecs-oracle/check.py
~~~

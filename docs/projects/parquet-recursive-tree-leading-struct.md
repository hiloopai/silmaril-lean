# Leading Structs in repeated signed Parquet paths

The [checked Tree footer plan](parquet-recursive-tree-compiler.md)
now binds signed leaves that have at least one original repeated
wrapper below a Struct. The same physical scanner also reads the
existing LIST-led plans. The legacy ListPath logical plan still
models an original leading LIST.

For each Tree leaf, the carrier uses the complete unary path
from the original footer. In a nullable Struct above a nullable
LIST, the null Struct, null LIST and empty LIST use three
different definition levels. A continuation reaches a LIST
wrapper only above its original empty-list definition threshold.
The projection theorem preserves the ordered definition steps,
every wrapper threshold, both level maxima and the original
signed leaf. A zero-repetition path returns a typed representation
refusal. Its omitted-level sections require a separate profile.

The carrier still binds the physical column by group, index, path
and kind. V1 and V2 use the existing original framing, levels,
codec dispatch, signed payloads and ancestry checks. V1 carries its
live cursor across continuations. V2 retains its original raw level
spans and complete-row boundaries. The wire theorem binds each
page back to its original absolute header address. A page refusal
retains the checked original prefix and reached cursor.

The [native row join](parquet-recursive-tree-rows.md) compares
Struct presence at the shared site and gives each sibling LIST
its own cursor. Its exact projection recovers each original signed
trace. The existing Events and [strict IPC](parquet-recursive-tree-to-ipc.md)
adapters retain the selected completed groups and the first native
failure.

## Verification

Genuine PyArrow V1 and V2 files cover a nullable leading Struct
with independently repeated INT32 and INT64 descendants and a
separate top-level LIST. The files distinguish a null Struct,
present Struct with a null LIST, and empty LIST, including an
optional nested LIST. Independent wire inspection checks original
frame offsets, CRC, level spans, cursors and signed words. A labeled
mixed-version reframe uses separate continuation cuts. A late
Struct-presence mismatch and a continuation below the original
wrapper threshold retain the preceding complete group in Events
and IPC, including under empty projection and exhausted target
budgets.
[Parquet and IPC pins](../../scripts/parquet-recursive-tree-leading-struct-oracle/fixtures.json)

~~~sh
lake build --wfail +Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-recursive-tree-leading-struct-oracle/Axioms.lean
python3 scripts/parquet-recursive-tree-leading-struct-oracle/check.py
~~~

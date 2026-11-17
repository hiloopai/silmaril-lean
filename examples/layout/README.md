# C aggregate layouts against real compilers

`cases.h` holds aggregates with bit-fields and the scalar types where data models differ.
`measure.sh` measures each one, in the image built from `Dockerfile` (Ubuntu 24.04: gcc 13.3,
clang 18.1):

* `gcc-x86_64.txt`: gcc, x86-64 System V. `sizeof`, `_Alignof`, and every member's bit offset and
  width, found at run time (a bit-field is set to all ones in a zeroed object; an ordinary member
  by `offsetof` and `sizeof`). An unnamed bit-field cannot be probed; its offset is `?`.
* `msvc-x64.txt`: clang `--target=x86_64-pc-windows-msvc -Xclang -fdump-record-layouts`, the
  Microsoft x64 record layout as clang computes it. The dump gives a bit-field's bit range and an
  ordinary member's byte offset (its width is `?`). It omits zero-width bit-fields. This is clang's
  MSVC-compatible layout; it has not been checked against `cl.exe` here.

```sh
docker build --network host -t layout-cc examples/layout
docker run --rm --network host -v "$PWD/examples/layout:/l" -w /l layout-cc ./measure.sh
examples/layout/gen-lean.sh          # Silmaril/Data/Layout/Bitfield/Examples/Defs.lean
examples/layout/gen-lean.sh --check  # fail if it differs
```

`Silmaril.Data.Layout.Examples.cases_agree` proves, by `decide +kernel`, that
`Silmaril.Data.Layout.bitLayout` agrees with every value of both tables. The tables are what the
compilers printed, and a missing value constrains nothing. The Lean declarations are generated
from `cases.h` by `scripts/layout/gen.py`, a small reader for this file's one-line declarations.
That reader is untrusted; a wrong declaration would make the agreement fail.

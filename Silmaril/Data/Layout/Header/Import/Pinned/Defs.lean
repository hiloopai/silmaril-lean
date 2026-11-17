module

public import Silmaril.Data.Layout.Header.Import.Defs

/-!
# The pinned clang imports, and the same headers as text

Each artifact of `examples/headers/clang/` (produced and checked byte for byte by
`examples/headers/recipe.sh --check`) has its own generated module `Pinned.<Name>.Defs`: the JSON
and its provenance (`<name>Json`, `<name>Prov`), their import (`<name>`, by `Imported.ofJson`)
and the entries of that import as a literal (`<Name>.entries`). The JSON is the output of the
pinned clang 18.1.8 (`silkeh/clang@sha256:3914c93a…`, see each `.prov`), filtered to the
declarations of the header's own files and projected to the keys the import reads; the import
normalizes it and does not assume clang correct.

| value | header | flags (see the `.prov`) | kept files |
| --- | --- | --- | --- |
| `arith` | `elf-ladder/01-leaf-arith/arith.h` | `-ffreestanding -fno-builtin -I../common` | `arith.h`, `../common/rt.h` |
| `probe` | `headers/probe/probe.h` | `-ffreestanding -fno-builtin` | `probe.h` |
| `zlibSolo` | zlib 1.3.1 `zlib.h` | `-ffreestanding -fno-builtin -DZ_SOLO` | `zlib.h`, `./zconf.h` |
| `zlibHosted` | zlib 1.3.1 `zlib.h` | hosted (the image's glibc) | `zlib.h`, `./zconf.h` |
| `glibcString` | glibc `/usr/include/string.h` | hosted | `/usr/include/string.h` |
| `glibcStdlib` | glibc `/usr/include/stdlib.h` | hosted | `/usr/include/stdlib.h`, `/usr/include/alloca.h` |
| `glibcMath` | glibc `/usr/include/math.h` (libm) | hosted | `/usr/include/math.h`, `bits/mathcalls.h`, `bits/mathcalls-helper-functions.h`, `bits/floatn-common.h` |

All use `-std=gnu11` and target `x86_64-unknown-linux-gnu`.

This module holds the text of `arith.h` and `rt.h` for the subset reader. Their SHA-256 (which
`recipe.sh --check` compares with the files, since Lake does not track `include_str`):

* `examples/elf-ladder/01-leaf-arith/arith.h`:
  `61eb45a5756b10db4d130c18d9e34130d1ad06ef359cdeb31527b1983f55ebd0`
* `examples/elf-ladder/common/rt.h`:
  `bad2f2ad76bea06a400ad4ecfa9571627468a16077aabffe497468254b8a2174`
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

/-- `examples/elf-ladder/common/rt.h`. -/
def rtH : String :=
  include_str "../../../../../../examples/elf-ladder/common/rt.h"
/-- `examples/elf-ladder/01-leaf-arith/arith.h`. -/
def arithH : String :=
  include_str "../../../../../../examples/elf-ladder/01-leaf-arith/arith.h"
/-- The files of `arith.h`, as the subset reader takes them. -/
def arithFiles : List (String × String) := [("rt.h", rtH), ("arith.h", arithH)]

end Silmaril.Data.Layout.Header.Import.Pinned

end

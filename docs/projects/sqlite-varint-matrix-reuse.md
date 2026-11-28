# Reusing the SQLite one-byte varint proof on the GCC matrix ELF

Both inputs are ordinary unstripped SQLite 3.54.1 GCC `-O2` x86-64 shared
objects. They have distinct whole-file digests. The matrix adds the comparison
profile's defines and compiler flags, including `-fno-builtin`.
[Comparison report](https://share.hiloop.ai/sqlite-elf-comparison-f1aff7/) ·
[Generator PR #5406](https://github.com/hiloopai/silmaril-lean/pull/5406) ·
[Exact generator revision and measurements](https://github.com/hiloopai/silmaril-lean/tree/a29561a4a16ee37a98e569412a4b8ede52e47793/reports/sqlite/elf-comparison)

| Artifact | SHA-256 | Wrapper VA and size | Reader VA and size |
| --- | --- | --- | --- |
| Corpus GCC `-O2` | `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8` | `0x117b0`, 50 bytes | `0x10a40`, 274 bytes |
| Matrix GCC `-O2` | `31d32767089dadc634fc6b07f5975fe8371a2c2d5765e35cea6fe0a82166ac06` | `0xf140`, 50 bytes | `0xe700`, 274 bytes |

The matrix ELF is 6,958,352 bytes. Its wrapper's SHA-256 is
`106601b04963e8b59af7107a434a8867359b2a640428778382117215a97a6a02`.
Both full readers have SHA-256
`b063938e7e336bcdd972316f308635ae19227b0f5b63a0472d21185892dd529b`.

## Shared proof and independent checks

`firstReturn_at` factors the proof from
[#5410 at 77899c5e](https://github.com/hiloopai/silmaril-lean/commit/77899c5e4b08ee0928f4c37b05c468083d1b1a85)
over the two ELF virtual addresses and the encoded signed rel32. The wrapper
byte template has exactly one variable field, its four-byte immediate. Both
specializations use the same callee window, the same 21-instruction path,
the same symbolic execution and the same entry and memory-effect contracts.
The original corpus proof and standalone example are still built by the
regular checks. [Shared theorem](../../Silmaril/Elf/Corpus/SqliteOneByteVarint/Thms.lean) ·
[Entry and effects](sqlite-varint-elf.md)

The matrix replay checks the digest before importing the **complete** file.
Lean checks both executable mappings through the file's program headers and
matches the full wrapper and the callee window against that file. It also checks
the two indexed local `.symtab` records and their linked names, equality of the
complete 274-byte readers via executable spans in both files, and admissible
placement at bias zero.

The matrix call at `0xf14a` encodes `e8 b1 f5 ff ff`. Its signed immediate is
`-0xa4f`, the continuation is `0xf14f`, and the target is `0xe700`. Lean checks
all of the matrix path's decodes again and checks that the call reaches the
reader. Supplying the corpus immediate at the matrix addresses fails the
direct-call check. Bias is common to both addresses, so the shared execution
proof transports this direct transfer to each supplied placement.
[Matrix file checks and theorem](../../tools/sqlite-matrix-varint/MatrixReplay.lean)

`Matrix.matrixFirstReturn` assumes a modeled `RoLoaded` image, valid placement
at the chosen bias and the admitted ABI/buffer state. The proof keeps the same
data-access trace and write frame. Execution covers the one-byte varint route.
The 274-byte comparison is file equality. Dynamic relocation application,
host loading and cross-compiler transfer are outside the experiment.

## Replay from the exact matrix build

From the repository root on x86-64 Debian with the GCC, glibc headers and
binutils versions listed in the pinned measurements:

```bash
set -euo pipefail
scratch=$(mktemp -d)
revision=a29561a4a16ee37a98e569412a4b8ede52e47793
git fetch https://github.com/hiloopai/silmaril-lean.git "$revision"
test "$(git rev-parse FETCH_HEAD)" = "$revision"
git archive "$revision" reports/sqlite/elf-comparison | tar -x -C "$scratch"

mkdir -p "$scratch/work/source"
python3 -I - "$scratch" <<'PY'
import importlib.util
from pathlib import Path
import sys

scratch = Path(sys.argv[1])
recipe = scratch / "reports/sqlite/elf-comparison/build.py"
spec = importlib.util.spec_from_file_location("comparison_builder", recipe)
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)
work = scratch / "work"
builder.fetch(None, work / "source")
builder.compile_one("gcc-O2", work)
PY

tools/sqlite-matrix-varint/check.sh "$scratch/work/gcc-O2/libsqlite3.so"
```

The generator checks the official ZIP and source digests. The last command also
works with an existing copy of the exact unstripped matrix library. It checks
the full-file SHA-256, builds the shared theorem and corpus regression with
`--wfail`, imports the whole matrix ELF in a temporary Lean module, prints six
transitive axiom footprints, and replays the module in Lean's kernel. The
matrix ELF and generated Lean outputs stay outside Git. SHA-256 and rebuild
provenance are host checks. Lean checks the included bytes and ELF relations.

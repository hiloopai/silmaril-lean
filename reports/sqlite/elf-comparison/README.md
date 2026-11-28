# SQLite ELF comparison generator

The measured matrix covers SQLite 3.54.1 on x86-64 Linux with glibc. The
GCC `-O2` build is the baseline. [Measured report](Report.md) ·
[Measurements](results.json) · [JSON schema](results.schema.json)

## Reproduce

Use x86-64 Debian 13 or a compatible GNU/Linux host with Python 3.10+,
GCC, Clang, glibc development headers, GNU binutils with `ld.bfd`, LLVM objdump,
Rust and Cargo 1.85+, and curl. The measured run used GCC 14.2.0, Clang 19.1.7,
glibc 2.41, GNU binutils 2.44, and Rust 1.85.1. Exact Debian package versions
and the compiler target triples are in `results.json`. The Rust dependency
versions and registry checksums are in `Cargo.lock`.

Run from this directory. The builder downloads the official ZIP and checks both
archive digests and both amalgamation file digests. To use a previously
downloaded ZIP, pass `--archive /path/to/source.zip`.

```sh
scratch=$(mktemp -d)
python3 build.py "$scratch/first" --jobs 4
python3 build.py "$scratch/second" --jobs 4
python3 report.py "$scratch/first" "$scratch/report" --replay "$scratch/second"
cmp Report.md "$scratch/report/Report.md"
cmp results.json "$scratch/report/results.json"
```

The final two comparisons use the recorded toolchain and versions. With other
versions, the same commands measure the local matrix and establish replay
agreement for that environment. The builder retains `build.json`, the objects,
ELFs, expanded compiler-driver commands and sorted C preprocessor macro dumps
under the supplied directory. The report includes build commands, digests,
file lengths, tool versions and analysis results. `report.py` can also analyze a
single build directory. Replay checks file bytes and parses both matrices.
The independent disassemblers and runtime smoke tests run on the primary matrix.

```sh
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
python3 -m jsonschema -i "$scratch/report/results.json" results.schema.json
```

The final command requires the optional Python `jsonschema` package. The
generator itself uses only the Python standard library, the locked Rust
dependencies, and the toolchain above.

## Build and strip relationship

Every row builds the same amalgamation with `SQLITE_THREADSAFE=1`,
`SQLITE_OMIT_LOAD_EXTENSION=1`, `SQLITE_MAX_MMAP_SIZE=0`,
`SQLITE_DEFAULT_MMAP_SIZE=0`, and the release's default built-in features.
The flags fix the generic AMD64 target, PIC, explicit pthread support through
`-pthread`, and `-fno-builtin` for implicit compiler substitutions. Explicit
built-ins in SQLite and the compiler predefines can still differ by compiler.
Optimization changes only the `-O` switch. DWARF 4 remains available for hints.
GNU ld supplies the SONAME and deterministic SHA-1 build ID. The generator
records the exact command arguments and input and output hashes.

The ordinary `libsqlite3.so` and its `stripped.so` share a build ID.
The analysis link `relocs.so` retains text relocations and uses the same object
and link options plus `--emit-relocs`. Directly stripping the relocation-rich
link with the measured GNU strip 2.44 or LLVM strip 19.1.7 left stale
`.dynsym` section indices in an examined GCC `-O0` build. The build therefore
strips the ordinary link. The analyzer checks executable load segment addresses,
file and memory sizes and SHA-256 across all three artifacts. It compares
dynamic symbol records using section names and checks dynamic string, hash,
version and relocation tables. It also checks the usable unstripped symbol
slices for byte, address and name equality across the two links.

## Measurement definitions

### Universe and matching

- The universe is defined, named, positive-size `STT_FUNC` records in the
  unstripped `.symtab` whose full slices lie in file-backed executable sections.
  Equal address and extent records join one span with a set of alias names.
  All members of a conflicting overlap are excluded and counted. Separate
  counters cover input records, zero sizes, unusable records and aliases.
- A pair of spans matches if they share at least one exact name and each is the
  other's only candidate. Multiple candidates or a non-reciprocal candidate
  yield an ambiguous span. No candidate yields an unmatched span. Static
  name overlap counts distinct names in usable spans. Dynamic name overlap
  counts distinct defined nonlocal `STT_FUNC` names in `.dynsym`.
- For unmatched spans only, clone hints compare names after recognizing
  `.isra.`, `.constprop.`, `.part.`, `.cold`, and `.llvm.` suffix markers.
  The target must contain the unsuffixed name or a recognized sibling clone.
  An inline hint means the target includes a DWARF `DW_TAG_inlined_subroutine`
  whose direct or referenced name agrees with the source name or clone base.
  Inline counts include nested DIEs. They resolve through abstract-origin
  and specification references and count unresolved names separately.
  Clone and inline evidence can co-occur. The residual category is unknown.
  Both hints depend on compiler output and leave the exact match unchanged.
- Exact comparison uses raw bytes over the full symbol span. Exact byte totals
  sum the size of the equal spans once per side. The JSON records all eligible
  and matched bytes separately for both directions.

### Normalized signatures

`sqlite-elf-norm-v1` describes address fields while retaining the rest of the
machine encoding. Each fully decoded instruction contributes its length as a
byte, its bytes with any resolved address field zeroed, and a length-prefixed
UTF-8 target label. The label length is an unsigned 32-bit little-endian
integer and is zero for instructions without a normalized field. The
concatenation follows the function's address order and is hashed with SHA-256
after a `sqlite-elf-norm-v1` prefix and NUL byte.

The analyzer finds signed PC-relative encodings using decoder field offsets.
Direct near branches or calls within the span use the target instruction
ordinal. Other direct targets must name an exact usable function entry or PLT
stub. RIP-relative operands may also name a dynamic GOT slot or an offset in a
unique, nonoverlapping named `STT_OBJECT` range. PLT and GOT labels carry ELF
symbol versions when present. Function labels carry the sorted names unique
within the build. Each retained text relocation inside an instruction must
start at its decoded address field and have a supported width and type
(`PC8`, `PC16`, `PC32`, `PLT32`, `GOTPCREL`, `GOTPCRELX`,
`REX_GOTPCRELX`). The labels describe the linked target. Relocation records
supply a separate check on the field location and type. Branches and RIP-relative
fields resolved at assembly time can be normalized without a retained relocation.

Unresolved fields, unsupported retained relocations and failed decoding make
the span ineligible. Anonymous literals, mid-instruction addresses and uncertain
function targets can therefore reduce the denominator. Encoded data constants,
registers, instruction size, layout and opcodes remain significant. The
signature carries labels for data references and makes no claim about their
contents or runtime resolution. [AMD64 System V ABI](https://gitlab.com/x86-psABIs/x86-64-ABI)

### Control flow, calls and idioms

- The CFG uses linear disassembly over the symbol extent. Blocks start at
  entry, after block terminators and at decoded local branch targets. Edges
  include fallthrough, local branch, direct exit, indirect exit, return and
  stop. The comparison uses address-order block ordinals and edge kinds.
  Equal CFGs have equal block counts and equal edge sets. Edge intersections
  treat the matched caller as part of the edge key. A bad local branch
  boundary excludes a CFG. Calls ordinarily fall through and indirect jumps
  end at a graph exit.
- A direct call edge joins a caller span to a known code label or local
  instruction ordinal. PLT-labelled calls describe their linker stubs.
  Repeated call sites to the same target yield one edge. The overlap compares
  target labels within reciprocal caller pairs and reports both the
  mutually decoded and full-build edge denominators. Direct calls to unknown
  targets and direct outside-span jumps have separate site counts. Direct
  exit jumps can be tail calls or code splits and are counted outside the
  direct call graph.
- Indirect calls and jumps remain unresolved unless they use a RIP-relative
  memory operand pointing to a dynamic `JUMP_SLOT` or `GLOB_DAT` relocation.
  That case labels the dynamic symbol behind the GOT slot. It still represents
  a dynamic transfer. The switch detector looks for a register jump preceded
  by a signed scale-four indexed load and an add of the table base. It looks
  back up to eight instructions within the block for an unclobbered RIP-relative
  LEA to `.rodata`. The first two relative table entries must land on decoded
  boundaries in the same span. The detector counts candidates and retains
  indirect exits in the CFG.
- Machine idioms count explicit LOCK prefixes, MFENCE, memory XCHG, and transfers
  labelled with `pthread_mutex_`, `sqlite3_mutex_` or `pthreadMutex`.
  The helper filter covers common stack protector, atomic, sanitizer,
  wide-integer arithmetic, TLS, and x86 thunk names. A zero count applies
  to that name filter. The split or outline label detector uses `.part.`,
  `.cold` and `OUTLINED_FUNCTION_`, which are compiler naming conventions.
  The report includes examples and the JSON records labelled target counts.

These metrics support discovery. A name, hash, CFG edge or call edge agrees
under the stated representation. Padding, interposition, escaped control
flow, indirect dispatch and data contents remain relevant to any deeper
comparison. DWARF is used only as a hint for unmatched functions.

# C headers: two routes to the declarations

A conformance row (see [ABI conformance](abi-conformance.md)) takes its C prototype from a
header, never from a hand-written signature. There are two routes from a header to the
declarations it introduces. They produce the same kind of value, and theorems compare them.

| route | module | reads | trusts |
| --- | --- | --- | --- |
| **subset reader** | `Silmaril.Data.Layout.Header` (`read`) | the header *text*, with the files it includes, by a small C reader the kernel evaluates | nothing beyond the reader's definition. It refuses what it does not read: `#if`, struct definitions, function pointers, attributes, `static`/`inline` |
| **clang import** | `Silmaril.Data.Layout.Header.Import` (`Imported.ofJson`) | a pinned clang JSON AST of the header, through the fail-closed decoder `Compiler.Clang.TotalJson` | the pinned artifact: that the pinned clang, run by the recorded command, printed this AST for the header. The import normalizes a tool's output and does not assume clang correct |

## The normalized header

`Imported` has a provenance record and one `Entry` per top-level declaration, in clang's order.
**No declaration is dropped**: `importNodes_length` proves one entry per node of the document.
A node the strict decoder refuses becomes an entry with `Body.unsupported` and the decoder's
message.

| field | content |
| --- | --- |
| `name`, `kind` | the declaration's name (`""` for an anonymous tag); function, typedef, struct, union, enum, variable, or another clang kind |
| `loc` | the file as clang prints it, and the line (for a macro, the expansion) |
| `implicit` | clang declared it itself (a library builtin's implicit declaration) |
| function `proto` | the `CProto` (`Data.Layout.Header.CProto`) when the subset can express it, else `Got.unsupported` with the reason: no prototype (K&R `f()`), a function-pointer parameter or result, an incomplete array, an unknown type |
| function `variadic` | clang's `variadic` |
| function `cc` | the calling convention of the function type: `c` (the target's default), `msAbi`, `sysvAbi`, `regcall`, `vectorcall`, or `other` |
| function `attrs` | the attributes as data: `noreturn` (GNU or `_Noreturn`), `nonnull`, `format`, `deprecated`, `visibility v`, `asmLabel`, `pure`, `const`, `nothrow`, `leaf`, `builtin`, … and `other kind` for the rest. Clang's JSON has no arguments for `format` or `nonnull` |
| function `symbol`, `asmLabel` | clang's `mangledName`: the C name, or the asm label (`__asm__("…")`, glibc's `__REDIRECT`) |
| function `storage`, `inline`, `definition` | `extern`/`static`, `inline`, whether it has a body |
| typedef, variable | the `CTy` or the reason |
| struct, union, enum | defined, or only declared |

Types come from clang's printed types. The import keeps the typedef names it has read
(`CTy.typedef`), as the subset reader does. A typedef name the import does not declare (a
system name such as `size_t`) is read from clang's desugared spelling of it. Parameters come
from the `ParmVarDecl`s, which keep their typedef names; the result and the convention come
from the function type. Convention attributes are part of a function type in clang, so they
are read from its spelling. On x86-64 System V, `sysv_abi` is the default convention; the
import keeps the spelling.

`Imported.header` is the subset reader's `Header` view of the import: the typedefs and the
first prototype of each external function (not implicit, not `static`).
`Imported.conflicts` lists redeclarations with a different prototype.

## The provenance record

`examples/headers/recipe.sh` produces every artifact and writes its provenance as
`examples/headers/clang/<name>.prov`, which the Lean side reads (`Provenance.parse`):

- `image`: the container, by digest (`silkeh/clang@sha256:3914c93a…`, Debian clang 18.1.8);
- `clang`: `clang --version`;
- `target`, `std`, `cwd`, `command`: the exact command (`clang -target x86_64-unknown-linux-gnu
  -x c -std=gnu11 … -Xclang -ast-dump=json -fsyntax-only <header>`);
- `define`, `include`: the `-D` macros and include paths;
- `filter`, `filter-sha256`: the filter command and the SHA-256 of `filter.py`;
- `source`: the release archive, its SHA-256 and URL (zlib);
- `input`: each kept file as clang names it, with its SHA-256;
- `json-sha256`, `json-bytes`: the artifact itself. `Imported.ofJson` refuses a document whose
  byte count is not the recorded one.

`recipe.sh --check` regenerates everything in a temporary directory and compares byte for byte.
That includes the JSON, the provenance, the zlib excerpt below and the generated Lean literals.

The filter (`examples/headers/clang/filter.py`, run in the same image) does five things:

1. It keeps the top-level declarations located in the header's own files.
2. It resolves each kept declaration's location to an explicit file and line. Clang omits a
   location's file and line when they repeat the previous one, so the filter follows that
   chain through the whole document.
3. It projects each declaration to the keys the import reads: `id`, `kind`, `loc`, `name`,
   `mangledName`, `type` (`qualType`, `desugaredQualType`), `storageClass`, `isImplicit`,
   `variadic`, `inline`, `tagUsed`, `completeDefinition`. Of the children it keeps only the
   kinds the import reads: `ParmVarDecl`, the attributes, `CompoundStmt` (that there is a
   body) and `EnumConstantDecl`. Ranges, columns, type nodes and other children are dropped.
4. It renumbers clang's node ids, which are heap addresses, by order of first appearance.
5. It writes compact ASCII JSON, one declaration per line.

The values kept are clang's.

| artifact | header | flags | kept files | JSON bytes |
| --- | --- | --- | --- | --- |
| `arith` | `examples/elf-ladder/01-leaf-arith/arith.h` | `-ffreestanding -fno-builtin -I../common` (the ladder's) | `arith.h`, `../common/rt.h` | 7748 |
| `probe` | `examples/headers/probe/probe.h` | `-ffreestanding -fno-builtin` | `probe.h` | 7113 |
| `zlib-solo` | zlib 1.3.1 `zlib.h` | `-ffreestanding -fno-builtin -DZ_SOLO` (rung 03's) | `zlib.h`, `./zconf.h` | 24087 |
| `zlib-hosted` | zlib 1.3.1 `zlib.h` | hosted | `zlib.h`, `./zconf.h` | 38247 |
| `glibc-string` | the image's glibc `string.h` | hosted | `/usr/include/string.h` | 33403 |

All five use `-std=gnu11` and target `x86_64-unknown-linux-gnu`. glibc's `math.h` is not
pinned. Its declarations are in `bits/mathcalls.h`, expanded once per floating type, so
filtering it to its own files keeps several hundred declarations, all outside the INTEGER
fragment.

### One kernel parse per artifact

The kernel reads the JSON through `Formats.Json.parseChars?`, which is the standard RFC 8259
lexer and parser without the UTF-8 decoding step. `Thms.parseDecimal?_eq_parseChars?` proves
that the byte parser equals it on valid UTF-8. That step takes seconds per kilobyte in the
kernel. The artifacts are ASCII, and `asciiChars` reads them structurally.

Each artifact has a generated module `Header.Import.Pinned.<Name>.Defs`. It holds the JSON and
its provenance (`include_str`), their import (`<name>`), and the import's entries as a literal
(`<Name>.entries`). `examples/headers/emit.lean` writes the module, `recipe.sh` runs it, and
`--check` compares it byte for byte. The emitter is not trusted. Its own module
`Pinned.<Name>.Thms` holds the only theorem that parses the JSON, `import_<name> : <name> =
⟨.parse <name>Prov, <Name>.entries, none⟩`. These five modules check in parallel. Every other
theorem rewrites with `import_<name>` and computes on the literal.

The generated module also includes the provenance verbatim. Lake does not track the files
`include_str` reads, so a changed JSON must change a module for it to be rebuilt. For the
same reason, the modules that read the header texts (`Pinned.Defs`, `Zlib.Defs`) name the
texts' SHA-256, and `--check` compares those hashes with the files.

| module (local `lake build`, one thread per module) | before | after |
| --- | --- | --- |
| `Pinned.Arith.Thms` (`import_arith`) | — | 8 s |
| `Pinned.Probe.Thms` | — | 9 s |
| `Pinned.ZlibSolo.Thms` | — | 22 s |
| `Pinned.GlibcString.Thms` | — | 30 s |
| `Pinned.ZlibHosted.Thms` | — | 34 s |
| `Pinned.Thms` (cross-checks; `Header.Import.Thms` before) | 347 s | 13 s |
| `Machine.Abi.Conformance.Import.Thms` | 554 s | 12 s |

## What each route covers

| header | subset reader | clang import |
| --- | --- | --- |
| `arith.h` + `rt.h` | all of it: 6 typedefs, 20 prototypes | all of it: 26 entries |
| zlib 1.3.1 `zlib.h` | refused (`#if`). It reads the pinned excerpt `examples/headers/zlib-1.3.1/zlib.h`, which keeps the 11 checksum-API declarations verbatim with their line numbers and includes a resolved `zconf-solo.h` or `zconf-hosted.h` | all of it: 72 entries under `Z_SOLO` (48 functions), 108 hosted (81 functions) |
| glibc `string.h` | refused | 66 entries: 40 explicit functions and 26 implicit builtin declarations |
| `probe.h` | refused (struct definitions, attributes) | 31 entries |

## Cross-checks (`Data.Layout.Header.Import.Pinned.Thms`)

| theorem | statement |
| --- | --- |
| `arith_routes_agree` | `read arithFiles "arith.h" = some arith.header`: the same typedefs, the same 20 prototypes in order, and the same qualifiers by pointer level (`Header.quals`; the import reads them from clang's `qualType`, `Fn.quals`) |
| `zlibSolo_routes_agree` | under `-DZ_SOLO`, the 11 checksum functions have the same `CProto` |
| `zlibHosted_routes` | hosted, 9 agree. **`adler32_z` and `crc32_z` disagree**: the reader's built-in `size_t` is `.int .size .unsigned`, while clang's `size_t` (from stddef.h) is `unsigned long`. Both lower to `uint64 (uint64, pointer, uint64)` (`zlibHosted_disagreement_lowers_alike`) |
| `probe_reads` | kinds, tag definitions, conventions (`ms_abi`, `sysv_abi`, `regcall`), attributes and the asm label of the probe |
| `glibcString_reads` | 66 entries, 26 implicit, `strerror_r` renamed to `__xpg_strerror_r` |
| `provenance_reads` | fields of the provenance records |

## Coverage and `Declares` (`Machine.Abi.Conformance.Import`)

`status A ccs e` classifies each declaration for an ABI `A` with conventions `ccs`
(`sysvCcs = [.c, .sysvAbi]` for `sysvInt`):

| status | when |
| --- | --- |
| `claimable` | an external function with a `CProto` in a convention of `ccs` that `A.lower` accepts, and no asm label |
| `unsupported why` | an external function that is not claimable. The reason is the import's (outside `CProto`, decoder refusal), the convention's, the asm label's, or `A.lower`'s |
| `internal why` | an implicit builtin declaration, or a `static` function |
| `notFunction` | a typedef, tag or variable |

The `interface` is the first external declaration of each function name. `coverage A ccs imp
claimed` builds a conformance `Coverage`: `claimed`, plus every other interface function
excluded as `unsupported` (with the reason) or `unclaimed`. `checkCoverage` checks any
`Coverage` against the import, as `Coverage.check` checks one against the subset reader.
`DeclaresImport A ccs imp f p` is `Declares` on the import, and it also requires the
convention.

- `declares_iff_of_header`: when the two routes read the same `Header`, `Declares` and
  `DeclaresImport` coincide.
- `arith_declares_iff`: they coincide for `arith.h`, for every name and prototype.
- `zlibSolo_declares_iff` and `zlibHosted_declares_iff`: they coincide on the zlib names
  where the routes agree.
- `arith_coverage`: `LeafArith.coverage` is checked by both routes.

| header (`sysvInt`) | claimable | unsupported | internal |
| --- | --- | --- | --- |
| `arith.h` + `rt.h` | 20 (all) | none | none |
| `zlib.h`, `Z_SOLO` | 47 of 48, including the 11 checksum functions | `inflateBack` (parameter `in_func`, a function pointer) | none |
| `zlib.h`, hosted | 79 of 81 | `inflateBack`; `gzprintf` (variadic) | none |
| `string.h` | 39 of 40 | `strerror_r` (asm label `__xpg_strerror_r`) | 26 implicit builtins |
| `probe.h` | 9 of 19 | `knr` (no prototype), `vf` (variadic), `renamed` (asm label), `win` (`ms_abi`), `rc` (`regcall`), `by_value` (struct), `fp` (floating), `flag` (`_Bool`), `sort` (function pointer), `paint` (enum) | `inl` (static) |

Hosted `gzvprintf` is claimable. Its `va_list` parameter is read from clang's desugared
spelling as `struct __va_list_tag *`, which the psABI also passes as a pointer.

## Limits

- The import reads only top-level declarations. Struct and union members and enum constants
  are not entries, and `Data.Layout`'s struct reader is separate.
- Without `-fno-builtin`, clang merges a library builtin's redeclaration with the builtin's
  type. The function type then loses the header's typedef names in its result (`strlen` is
  printed `unsigned long (const char *)`). Parameters keep theirs. The ladder headers are
  imported with `-fno-builtin`, as they are compiled.
- An unknown typedef inside a compound type (`const size_t *`) is read from the desugared
  spelling and loses its name.
- The JSON is trusted as clang's output. Nothing here proves it faithful to the C standard or
  to the compiler that built a binary.

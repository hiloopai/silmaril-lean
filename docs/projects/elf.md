# ELF process support

ELF syntax and loaded-image facts are exposed through
`Silmaril.Formats.ELF.Cst.Defs` and `Silmaril.Formats.ELF.Cst.Thms`. The CST
layer validates the header and program-header shape used by the x86-64 and
RV64 launch models, while the process headers connect those facts to startup
and syscall proofs.

The process release checks ELF bytes in three places:

1. the freestanding `sha256-cli` image;
2. the static-musl checksum image and its launch facts;
3. the 49 small x86-64 probe images, each rebuilt from assembly and compared
   with `SHA256SUMS` before its generated Lean module is accepted.

The build recipes and hashes are kept beside the verification projects so a
fresh clone can replay the byte-level checks without relying on an untracked
binary.

## The ELF verification API (`Silmaril.Elf`)

`import Silmaril.Elf.Defs` gives one namespace for what a proof needs to know about an ELF64
file, with no per-file indices: a statement names a function by lookup ("the definition
`adler32_z` of this `libz.so.1`"), not by section, symbol and program-header numbers.

### Layers

| layer | module | main names |
|---|---|---|
| bytes | `Silmaril.Elf.Link.Dyn.Elf`, `Silmaril.Elf.Link.Dyn.Pages` | `Rd`, `blobRead`, `Chunk`, `sparseRead`, `run_sparse`, `pageRead`, `chunks_of%` |
| AST | `Silmaril.Elf.Ast` | `File`, `Section`, `Body`, `Span`, `Kind`, `File.kind` |
| parse | `Silmaril.Elf.Parse` | `read`, `parse`, `Parses`, `format` |
| semantics | `Silmaril.Elf.Lookup` | `Ref`, `Ver`, `Def`, `Sel`, `File.lookupDef`, `File.select`, `File.relocs`, `DynConsistent` |
| index | `Silmaril.Elf.Index` | `Index`, `Index.build`, `Index.lookup` |
| facts | `Silmaril.Elf.Facts` | `KindIs`, `SymbolAt`, `Lookup`, `Needed`, `Relocs`, `Placement`, `CodeAt`, `Binds` |
| checker | `Silmaril.Elf.Check` | `Check.file`, `Check.file_sound`, `Check.parses_of_pages` |
| shapes | `Silmaril.Elf.Shapes` | the `silmaril.shapes.elf.*` problems below |
| loading models | `Silmaril.Elf.Link.{ElfBind,Dyn.Loader,Dyn.Image}` | `ElfBind.{Bound,CodeAt,Placement,RoLoaded}`, `Dyn.ExeLoaded` |
| bridges | `Silmaril.Elf.Bridge`, `Silmaril.Elf.BindEq` | the API against the loader readers, `ElfBind` and silmaril's ELF readers |
| executables | `Silmaril.Elf.Exe` | `NoTextRelD`, `InterpIs`, `ExeFacts`, `roLoaded_of_exeLoaded` |
| CLI executables | `Silmaril.Elf.CliExe` | `silmaril.shapes.elf.cli_exe` over the CLI institution |

The parse is the specification: `Parses F A` says that the reader `read`, run on the bytes `F`,
returns the AST `A`. Every fact is an existential over the parse (`KindIs F k := ∃ A, Parses F A
∧ A.kind = k`), so two facts about one file agree on the parse they use. The symbol semantics
(`File.lookupDef`) is ld.so's `do_lookup_x` over the AST: SysV and GNU hash tables, symbol
versions, weak and hidden definitions.

### Problem shapes

| name | statement | module |
|---|---|---|
| `silmaril.shapes.elf.parses` | `Parses X A`: the metadata of `X` is the AST `A` | `Shapes` |
| `silmaril.shapes.elf.index` | `IndexIs X ix`: the lookup index of `X` is `ix` | `Shapes` |
| `silmaril.shapes.elf.kind` | `KindIs X k`: `X` is an object of kind `k` | `Shapes` |
| `silmaril.shapes.elf.symbol_at` | `SymbolAt X t i s`: entry `i` of table `t` is `s` | `Shapes` |
| `silmaril.shapes.elf.lookup` | `Lookup X sel d`: the selector `sel` denotes `d` | `Shapes` |
| `silmaril.shapes.elf.needed` | `Needed X ns`: the `DT_NEEDED` names are `ns` | `Shapes` |
| `silmaril.shapes.elf.relocs` | `Relocs X sel rs`: the relocations `sel` names are `rs` | `Shapes` |
| `silmaril.shapes.elf.placement` | `Placement X base`: `X` may be loaded at `base` | `Shapes` |
| `silmaril.shapes.elf.code_at` | `CodeAt X v code`: `code` is mapped read-only executable at `v` | `Shapes` |
| `silmaril.shapes.elf.binds` | `Binds X sel v code`: `sel` denotes the plain function at `v`, with code `code` | `Shapes` |
| `silmaril.shapes.elf.entry_point` | `EntryIs X v`: the entry point of `X` is `v` | `Shapes` |
| `silmaril.shapes.elf.cli_exe` | `CliExe exe k ld L M φ`: an executable of kind `k` with the API facts its loading model `ld` needs satisfies the CLI sentence `φ` under the model `M` | `CliExe` |

They sit beside the loader shapes `silmaril.shapes.elf.loads` and `silmaril.shapes.elf.entry`
(`Silmaril.Project.Shapes.Elf`, the LPS `ET_EXEC` loader), which they do not replace. A row over
a registered file:

```lean
silmaril instance zlib.libz132.adler32_z := silmaril.shapes.elf.binds
  (X := zlib.libz132) (sel := .dyn { name := nameOf "adler32_z" })
  (v := 0x3350) (code := Zlib.adler32zCode)
```

### Proving facts about real files

Small files: `decide +kernel` on the reader (`Silmaril.Elf.Example`). Large files (a 2 MB
`libc.so.6`): include the file as 4 KiB chunks (`include_bytes`, `chunks_of%`), take the AST from
an emitter as a candidate, and close `Parses` with the checker on the pages
(`Check.parses_of_pages`); every kernel read then touches one chunk. Lookups then go through the
index (`Index.lookup`, proved to answer `File.lookupDef`: `Index.Thms`) instead of a hash walk
on the bytes.

### Staged parsing (`Silmaril.Elf.Staged`)

`Parses F A` covers the whole file. For a multi-megabyte executable, `Silmaril.Elf.Staged` splits
the **same specification** into facts that can be established separately and recombined:

| stage | fact | reads |
|---|---|---|
| 1 | `LayoutIs F L` | ELF header, program and section headers, section names |
| 2 | `BodyIs F L sh b` | one section's body (`Parse.body`) |
| 2' | `LoaderIs F L ld` | `PT_DYNAMIC`, `PT_INTERP`, the `DT_STRTAB` names |
| 3 | `EntriesAt F p o w i es`, `TilesAt F ok o lens` | a window of a table; byte tiles of a span |

`Staged.parses_iff` says that a parse is exactly its stages and `parses_assemble` builds one
from them. `bodyIs_relas_iff` and `entriesAt_append` turn adjacent windows into a body. The
layout keeps no payloads. Sections and segments are `Span`s into the file (`Layout.section?`,
`segmentOf`, `vaddrOf`, `offsetOf`, `boundsOk`), read through whichever source checks them.
Each fact comes from running its reader on a source that answers as the file (`Check.Sub`):

* **paranoid**: `pageRead` on 4 KiB literals, `decide +kernel` (`layoutIs_of_pages`, …);
* **fast**: `fastRead` on a `ByteArray` (`sub_fast`). A compiled run is trusted computation.
  A theorem from it uses compiled evaluation, which on the current toolchain adds one
  auxiliary axiom per computation (`thm._native.…​.ax_…`); the policy decides
  which named computations may do so.

**Disassembly certificates.** A tile list is a claim of instruction boundaries. Any
disassembler can supply one (objdump, iced-x86, llvm-objdump, Capstone, XED, ddisasm). They
need not be trusted or agree, because a wrong boundary fails the check and cannot prove a false
theorem. `tilesOk r ok o lens` reads each tile once and applies an ISA predicate `ok`, for
example "`Silmaril.X86.Ext.decode` reads exactly this tile". Tiles are independent, so a
function, a window or a whole `.text` can be checked in parallel files.

`Silmaril.Elf.Staged.Example.Thms` (generated by `benchmarks/elf-staged/gen-example.sh`)
checks every stage of `examples/dyn/pinned/hello-gcc` in the kernel and assembles `Parses`.
`benchmarks/elf-staged/` measures the stages on ripgrep 14.1.1's 6.6 MB static-pie release
binary, pinned by SHA-256 and not committed. Its native tool is `elf-staged`
(`tools/elf-staged`).

### Trust

- Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
- `Dyn.ExeLoaded` (`Silmaril.Elf.Link.Dyn.Loader`) is a **specified relation**: what `execve`
  and glibc's `ld.so` leave in memory, transcribed from glibc 2.39, not a verified loader. Its
  module doc lists what it does not model (`DT_RELR`, TLS, `dlopen`, ...).
- The bridges are named open goals, frozen as `def Task.x : Prop` in `Silmaril.Elf.Bridge.Defs`;
  theorems that need one take it as a hypothesis. Proved: `Task.check_sound`,
  `Task.header_silmaril`, `Task.tables_silmaril`, `Task.codeAt_iff`, `Task.placement_iff`,
  `Task.parse_frame` and the index goals (`Task.index_lookup_sound`, `Task.index_symtab_sound`, `Task.gnu_eq_scan`).
  Proved from open goals: `Task.roLoaded_of_exeLoaded` (from `Task.dynInfo_rd` and
  `Task.relas_rd`; `Exe.roLoaded_of_exeLoaded` needs neither). Open: the reader
  agreements `Task.dynInfo_rd`, `Task.lookup_rd`, `Task.needed_rd`, `Task.relas_rd`,
  `Task.bound_iff`, `Task.readObject_agrees`, `Task.cst_agrees` and `Task.elfImage_agrees`.
- A problem row is a closed `Prop`. A consumer that assumes the parse row of a file takes it as
  a hypothesis or cites the open problem; it is never an axiom.

### Build

```sh
lake build --wfail Silmaril.Elf.Defs Silmaril.Elf.Shapes.Thms Silmaril.Elf.Check.Thms \
  Silmaril.Elf.Bridge.Thms Silmaril.Elf.BindEq.Thms Silmaril.Elf.Exe.Thms Silmaril.Elf.CliExe.Thms \
  Silmaril.Elf.Example.Thms Silmaril.Elf.Staged.Thms Silmaril.Elf.Staged.Example.Thms
lake build elf-staged   # the native tool (benchmarks/elf-staged)
```

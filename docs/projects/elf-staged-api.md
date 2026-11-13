# An accelerable ELF API: design, supported scope and roadmap

This note designs the API around `Silmaril.Elf.Staged`: ELF facts that are cheap to state,
checked in small leaves, run natively or in the kernel under one policy, and grounded in the
bytes of a named file. It records what this repository supports now and what is future work.
The ELF guide is [elf.md](elf.md). The benchmark is `benchmarks/elf-staged/`.

## Principles

1. **One specification, many stages.** Every fact is the specification's own reader run on the
   file (`Silmaril.Elf.read` and its sub-readers), restricted to what the fact needs.
   `Staged.parses_iff` says the stages are exactly the parse. A new table or format adds a
   reader and a stage, never a second specification.
2. **Certificates are untrusted data; leaves are trusted checks.** An emitter (a Rust or Lean
   tool, objdump, a DWARF library, a compiler) writes small named definitions: the layout, a
   window of a table, a symbol index or instruction boundaries. Each is checked by a leaf, a
   Boolean checker over an abstract byte source with one soundness lemma
   (`Silmaril.Elf.Staged.Leaf`). A wrong certificate fails its leaf. It cannot prove a false
   theorem.
3. **Two sources, one proposition.** A leaf's checker is written once over a byte source. It
   runs natively on the file's `ByteArray` (`fastRead`, `Leaf.of_native`) or in the kernel on
   its 4 KiB pages (`pageRead`, `Leaf.of_kernel`). Both conclude the same `P (blobOf b) c`.
   The bytes are bound by each source's `Sub` lemma, not by the certificate.
4. **Bounded width.** No statement holds more than a bounded amount of data, for example one
   window of 1,024 relocations or one function's instruction boundaries. A large table is a
   tree of fixed-width windows (`EntriesAt`, glued by `entriesAt_append`). Its leaves are
   independent, so they run in parallel modules and cache separately. A monolithic literal does
   not scale: the whole 2.5 MB AST of a 6.6 MB executable did not elaborate in 11 minutes.
5. **Caching by imports.** A leaf module imports only its object module and the bytes module
   (`include_bytes`). Changing one object or one checker rebuilds only the leaves that use it.

## Trust policy integration

The trust framework (`Silmaril.Prelude.Trust`, [trust.md](../trust.md)) owns the profiles,
the scope policy, `edge_decide`, the use records and the audit. Each ELF leaf
(`Silmaril.Elf.Staged.Native`) has two checkers for one proposition:

| | native checker | kernel checker |
|---|---|---|
| function | `Native.<leaf> b c` | `Kernel.<leaf> x c` |
| bytes | the file's `ByteArray` (`fastRead`) | core's kernel bytes `x` (`KBytes.readLE`) |
| declared | `Silmaril.Procedures.elf.<leaf>` (`ProcDecl`), native backend | the same declaration, kernel backend; only ever checked by the kernel |
| soundness | `Native.<leaf>_sound` | `Kernel.<leaf>_sound x.wf_true x.toByteArray_eq` |
| conclusion | `P (blobOf ⟨raw⟩) c` | the same `P (blobOf ⟨raw⟩) c` |

The kernel bytes and the raw bytes come from the same `include_bytes` literals
(`kbytes_def x of_include raw` proves `x.toByteArray = raw` without decoding a byte).
`sub_kbytes` and `sub_fast` tie each source to the one file.

A leaf theorem is `by sil_check elf.<leaf> (native := Native.<leaf>_sound …) (kernel :=
Kernel.<leaf>_sound x.wf_true x.toByteArray_eq …)`. `sil_check` checks both sides against the
declaration before running anything.

* **Native allowed:** the `ByteArray` backend runs natively, and the use and its axiom
  `<decl>._native.edge.elf.<leaf>.ax_i_j` are recorded under `elf.<leaf>`. Errors and `false`
  propagate, with no fallback.
* **Otherwise:** the kernel checks the kernel-bytes backend, and the kernel use is recorded
  under the same name.
* A check that gives only the kernel side is kernel-only in every profile.

The `default` set holds `elf.layout` (core's policy); the other `elf.*` procedures run natively
under `local`. `Silmaril.Elf.Staged.Example.Profiles` checks every case with audits and use
records:

* default: native layout, kernel loader;
* local: native;
* paranoid: kernel;
* kernel-only under local: kernel;
* an unsupported leaf;
* a false claim, under native and under kernel.

`Example.Thms` itself is checked in the default build and in the paranoid profile build. Only
the profile-test module is excluded from the paranoid build.

## Supported now

| area | facts | leaves | module |
|---|---|---|---|
| file type, header | `LayoutIs` (and `File.kind` through the parse) | `elf.layout` | `Staged` |
| program headers, segments | spans, `segmentOf`, `vaddrOf`, `offsetOf`, `boundsOk` | `elf.layout` | `Staged` |
| sections | named spans, typed bodies (`Body`: symbols, RELA/REL/RELR, dynamic, hashes, versions, notes) | `elf.body` | `Staged` |
| loader view | `PT_DYNAMIC`, `PT_INTERP`, `DT_NEEDED`, `DT_SONAME`, run path | `elf.loader` | `Staged` |
| RELA windows | `EntriesAt`, `bodyIs_relas_iff` | `elf.rela` | `Staged` |
| symbols | `SymAt`; name → entry (`ByName`), address → entry (`ByAddr`), sound lookups | `elf.symbols.byName`, `elf.symbols.byAddr` | `Staged.Symbols` |
| code | instruction tiles: bounds, and per-tile acceptance by `Silmaril.X86.Ext.decode` | `elf.tiles`, `elf.tiles.x86` | `Staged.Leaf` |
| whole parse | `Parses` assembled from stages | `parses_assemble` | `Staged` |
| policy | native (`ByteArray`) or kernel (`KBytes`) per leaf | `sil_check` | `Staged.Native` |

Worked examples:

* `Silmaril.Elf.Staged.Example` covers the pinned `hello-gcc`.
  - Its object module and leaf module are generated by `benchmarks/elf-staged/gen-example.sh`.
  - Its bytes module holds the raw `ByteArray`.
  - In the default profile the layout runs natively and the rest in the kernel; under
    `paranoid`, everything runs in the kernel.
  - Every stage is checked, and `Parses` is assembled from them.
  - **Grounded `main`.** The forward index names entry 31 as `main`, and the reverse map
    gives its extent. `offsetOf` places it at file offset `0x1060`. The seven objdump
    boundaries tile its 27 bytes, and each tile is one instruction of the local x86 model.
* `benchmarks/elf-staged` covers ripgrep 14.1.1 (6.6 MB static-pie). The layout, the loader
  view, all 21,594 relocations in 22 windows, and instruction tiles are checked in the kernel.

## Future work, by design

Nothing below is registered as a leaf. Each item names the stage it would add.

* **Windows of every table.** Symbols, `REL`, `RELR`, version tables and hash tables would
  each get an `EntriesAt`-style window and a `bodyIs_*_iff` lemma, as for RELA.
* **Object trees.** Today windows are flat. The general form is a tree of named nodes of
  bounded width. Each node is a definition in a shared object module, and a leaf per node
  checks it. The theorem for the whole table follows from the leaves of the node structure,
  without restating the data.
* **Symbol tries.** A byte trie over names would be shared between files (libc, libstdc++ and
  their users). It would support forward lookup by prefix, with a reverse map from addresses
  to names. The present `ByName` and `ByAddr` sorted arrays are its leaf form. Completeness (an
  absent answer means absent) needs the sortedness the checks already establish, plus a
  counting lemma.
* **Function bounds without symbols.** Stripped binaries such as ripgrep have no `.symtab`.
  Function starts would come from `.eh_frame_hdr`'s sorted table, as a leaf over its entries
  and the FDEs they point to.
* **DWARF.** The plan is `.debug_line` programs (address to file and line), then
  `.debug_info` DIEs for functions and variables. Each is a reader over section spans (a
  stage) with windowed certificates per compilation unit, as for symbols. Supported now:
  nothing beyond locating the sections by name in the layout.
* **More disassemblers.** objdump and iced-x86 agree on ripgrep's 981,080 boundaries. Capstone,
  XED, llvm-objdump and ddisasm could also propose tiles. Disagreements are flagged, never
  trusted. The x86 model accepts 91.3 % of ripgrep's instructions at the claimed length; the
  rest is the coverage work list for `Silmaril.X86`.
* **Translation validation grounded in ELF.** The target is Godbolt-style: C or assembly beside
  machine code, with each line's code proved to come from the binary. The chain is: a function
  named in the source, its symbol (`ByName`), its extent (`ByAddr`), its file bytes
  (`offsetOf`), its instructions (`elf.tiles.x86`) and its semantics (the x86 block
  certificates, `Silmaril.X86.BlockCert`), compared with the compiler's IR or the C semantics.
  The hello-gcc example carries this chain up to the instruction tiles. Lines need DWARF line
  tables.

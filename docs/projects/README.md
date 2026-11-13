# Projects

| Project | Included in this release | Guide |
| --- | --- | --- |
| WebAssembly | Seven native tools, binary/text models, execution models and scoped transformation proofs | [Wasm](wasm.md) |
| Wasm components | The component model (codec, validator, reference machine, streams), WIT, jco and WAC work-alikes, the component and generator subcommands of `wasm-tools`, the CLI specification API and the generator API | [Wasm components](wasm-components.md) |
| More Wasm | WasmFX and asyncify on it, the unified and deterministic semantics, Wasm games and institutions, program logics, version models, wasmi and OCaml models, WASI preview 1/0.2/0.3 theories and adapters, a networking stack, and the component registry shapes | [More Wasm](wasm-wasi.md) |
| Compiler foundations | Semantic contracts, passes, checked transformations, translations and compiler categories | [Compiler APIs](compilers.md) |
| Logics and institutions | HOL, Metamath, ZF/ZFC, arithmetic, proof translations and Hets-style development graphs | [Logic](logic.md) |
| Lambda calculi | Eight cube corners, STLC categorical semantics, System F/Fω parametricity and institution graphs | [Lambda cube](lambda-cube.md) |
| HTTP | RFC 9110 semantics and RFC 9112 HTTP/1.1 parsing and framing; RFC 9113 HTTP/2 frames, settings, flow control, stream states and field validity; RFC 7541 HPACK; the roadmap to full HTTP (HTTP/3, caching, cross-version and security properties) | [HTTP](http.md) |
| HTTP servers | One framework for HTTP servers on any platform: the server institution over request/response traces (overlapping requests, connections) with atomic, linearizable (shown equal to Herlihy–Wing), sequentially consistent, per-connection and in-order readings, refinement as trace inclusion, one fresh-instance-per-request model and liveness under fairness; `wasi:http` proxy components read as servers, with hello, route and echo proved for every host; state models (component state, files the server alone edits, shared files), with a file-backed store component over `wasi:filesystem` proved to refine the file store; a survey of Wasm HTTP frameworks and server formalizations, and the process, container and CGI/WAGI instances | [HTTP servers](http-servers.md) |
| Lossless compression | A decoder/codec/container/streaming framework; DEFLATE, zlib, gzip and a zlib 1.3.1 streaming inflater model | [Compression](compression.md) |
| Silmaril projects | Records for artifacts, values, problems and the problem DAG; format adapters and shapes; the `sil project` CLI (check, SQLite, explorer) | [Silmaril projects](silmaril-projects.md) |
| Cambridge courses | L1/L2 semantics, domains and PCF, optimising compilers and exercises | [Courses](../courses/cambridge.md) |
| x86-64 machines and processes | User-mode machines (`Ext` to `Str9`, `Sse9`, `Atomic9`), function contracts, segment VCs, block certificates, a separation logic, the loose specification and x86 institution, static linking, memory models, the ELF ladder proofs, and the process slice | [x86 machines](../x86.md), [x86 processes](x86.md) |
| Command-line interfaces | Argument grammars with a derived, proved front end; behaviour specifications with refinement and composition; Lean CLI programs and a test harness; the CLI institution | [CLI](cli.md) |
| ELF files | One parse of an ELF64 file, ld.so's symbol lookup, a lookup index, facts and problem shapes over files, a checker for large files, and the x86-64 dynamic-loading models they relate to | [ELF](elf.md) |
| C library contracts and allocators | The contract institution of C library signatures (allocator chain, stdio, tensor), the allocator signature hierarchy and its POSIX-safe contract over ELF shared objects, a concrete loading model with named import contracts, and the problem shapes | [Allocators](alloc.md), [classifying libc specs](../libc-classification.md) |
| SpecTec | The Wasm 1.0, 2.0 and 3.0 specifications read from SpecTec's IL into Lean, patches, a surface-language fragment, grammar institutions and simulations with the Core semantics | [SpecTec](spectec/README.md), [divergences](spectec-divergences.md) |
| Data layouts | C struct layouts under LP64/ILP32 data models, byte lenses with frame lemmas, bit specifications, glibc malloc structures checked against DWARF; separation-logic cells, lists, bitmaps and boundary tags | [Data](data.md) |
| Dynamically linked processes | An x86-64 process linked against glibc 2.39 with library functions as atomic contract steps, the C runtime, block certificates, library modules, the program API with standard executables and their tactics, and hello world, `cat` and an adder for gcc and clang | [Dynamic processes](dyn.md) |
| SSA calculi and λRTL | The let family, λSSA, λRTL with loops, versioning, nameless presentations and institutions; a flat CFG with a sound validator; the SSA-form machine RTL with its λSSA translations | [SSA](ssa.md) |
| glibc's allocator | A layered model of glibc's ptmalloc (algorithm, byte representation, x86 block simulations, per-version pins) and the unconditional end-to-end theorems for the tcache paths of glibc 2.39's `malloc` and `free` | [ptmalloc](ptmalloc.md) |
| C semantics (Cerberus) | A Lean port of the Cerberus C semantics: C frontend, Cabs and typed Ail, Core dynamics and memory models, the Ail-to-Core elaboration with correctness theorems for restricted sources, the Core institution, and the `cerb-lean`, `ail-lean`, `core-lean`, `core-elab` and `cfront` tools | [Cerberus](cerberus.md) |
| System V translation validation | Function-by-function shapes: a placed x86-64 function implements a C function (Cerberus meaning) or a specification, lifts to an IR, IR-to-C correspondence, their composition, and several builds of one source; a worked example at `-O0` and `-O2` | [System V TV](sysv-tv.md) |
| System V AMD64 ABI | Argument classification and call planning for C types, native layouts of the Cerberus types, typed FFI contracts, real compiled examples | [System V ABI](systemv-abi.md) |
| C to x86, segment by segment | Program points between a C function's Cerberus Core and its machine code (DWARF line table and frame slots), segment goals with generic `-O0`/`-O2` segment theorems, the bridge to `c.compiles_to`, the `c-tv` generator and three examples at `-O0` and `-O2` | [Compiles-to](compiles-to.md) |
| Calling conventions | Calling conventions as institution comorphisms (System V AMD64, Microsoft x64), cross-ABI thunks and link compatibility, and x86 function contracts as System V and FFI certificates | [ABI](abi.md) |
| C compiler | `ccomp`'s IRs (Mir, RTL, Lir), behaviours and refinement, passes and validators, x86-64 and RV64 back ends, stage contracts, verified Core fragments, the C semantics ladder and the native x86-64 compiler, arriving in waves | [C compiler](ccomp.md) |

All projects share the root `Silmaril` library. The `sil` command groups available
tools by project; `sil --help` lists only implemented families. A project guide
should identify its definitions, theorem statements, examples, build commands,
source citations and assumptions.

Further planned ports cover game semantics, RISC-V, C semantics
and compilers. Each will arrive with a guide and examples as it joins the library.

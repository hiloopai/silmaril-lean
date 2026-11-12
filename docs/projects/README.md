# Projects

| Project | Included in this release | Guide |
| --- | --- | --- |
| WebAssembly | Seven native tools, binary/text models, execution models and scoped transformation proofs | [Wasm](wasm.md) |
| Compiler foundations | Semantic contracts, passes, checked transformations, translations and compiler categories | [Compiler APIs](compilers.md) |
| Logics and institutions | HOL, Metamath, ZF/ZFC, arithmetic, proof translations and Hets-style development graphs | [Logic](logic.md) |
| Lambda calculi | Eight cube corners, STLC categorical semantics, System F/Fω parametricity and institution graphs | [Lambda cube](lambda-cube.md) |
| Lossless compression | A decoder/codec/container/streaming framework; DEFLATE, zlib, gzip and a zlib 1.3.1 streaming inflater model | [Compression](compression.md) |
| Silmaril projects | Records for artifacts, values, problems and the problem DAG; format adapters and shapes; the `sil project` CLI (check, SQLite, explorer) | [Silmaril projects](silmaril-projects.md) |
| Cambridge courses | L1/L2 semantics, domains and PCF, optimising compilers and exercises | [Courses](../courses/cambridge.md) |
| x86-64 machines and processes | User-mode machines (`Ext` to `Str9`, `Sse9`, `Atomic9`), function contracts, segment VCs, block certificates, a separation logic, the loose specification and x86 institution, static linking, memory models, the ELF ladder proofs, and the process slice | [x86 machines](../x86.md), [x86 processes](x86.md) |
| Command-line interfaces | Argument grammars with a derived, proved front end; behaviour specifications with refinement and composition; Lean CLI programs and a test harness; the CLI institution | [CLI](cli.md) |
| SpecTec | The Wasm 1.0, 2.0 and 3.0 specifications read from SpecTec's IL into Lean, patches, a surface-language fragment, grammar institutions and simulations with the Core semantics | [SpecTec](spectec/README.md), [divergences](spectec-divergences.md) |
| SSA calculi and λRTL | The let family, λSSA, λRTL with loops, versioning, nameless presentations and institutions; a flat CFG with a sound validator; the SSA-form machine RTL with its λSSA translations | [SSA](ssa.md) |

All projects share the root `Silmaril` library. The `sil` command groups available
tools by project; `sil --help` lists only implemented families. A project guide
should identify its definitions, theorem statements, examples, build commands,
source citations and assumptions.

Further planned ports cover game semantics, RISC-V, ELF, C semantics
and compilers. Each will arrive with a guide and examples as it joins the library.

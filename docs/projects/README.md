# Projects

| Project | Included in this release | Guide |
| --- | --- | --- |
| WebAssembly | Seven native tools, binary/text models, execution models and scoped transformation proofs | [Wasm](wasm.md) |
| Compiler foundations | Semantic contracts, passes, checked transformations, translations and compiler categories | [Compiler APIs](compilers.md) |
| Logics and institutions | HOL, Metamath, ZF/ZFC, arithmetic, proof translations and Hets-style development graphs | [Logic](logic.md) |
| x86 process verification | Planned port: machine/process models, assembly proofs and whole-utility verification | [x86 roadmap](x86.md) |

All projects share the root `Silmaril` library. The `sil` command groups available
tools by project; `sil --help` lists only implemented families. A project guide
should identify its definitions, theorem statements, examples, build commands,
source citations and assumptions.

Further planned ports cover game semantics, parametricity, RISC-V, ELF, C semantics
and compilers. Each will arrive with a guide and examples as it joins the library.

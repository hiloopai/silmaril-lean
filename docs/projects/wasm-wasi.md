# More Wasm: semantics, WASI and networking

The third part of the Wasm release. It adds the remaining WebAssembly semantics and proof
developments, the WASI theories, and a small networking stack. It builds on the core tooling of
[wasm-binaryen-tooling.md](wasm-binaryen-tooling.md) and the component model of
[wasm-components.md](wasm-components.md).

## What ships

| Part | Modules | What it is |
| --- | --- | --- |
| WasmFX | `Silmaril.Wasm.FX` | stack switching (WasmFX) and asyncify expressed on it |
| Unified semantics | `Silmaril.Wasm.Unified` | one semantics across the Wasm versions, with version maps |
| Determinism | `Silmaril.Wasm.Det` | determinism results for the core and component semantics |
| Games and institutions | `Silmaril.Wasm.Game`, `Silmaril.Wasm.Institution`, `Silmaril.Wasm.Category` | game semantics of modules and components, Wasm institutions and their categories |
| Function institutions | `Silmaril.Wasm.FnInst` | the remaining function-level institutions, including `Ground` |
| Automatic checks | `Silmaril.Wasm.Auto2`, `Silmaril.Wasm.Dataflow` | the rest of the automatic verifier and dataflow analyses |
| Specifications and logic | `Silmaril.Wasm.Spec`, `Silmaril.Wasm.Logic`, `Silmaril.Wasm.Verify`, `Silmaril.Wasm.WatSpec` | specification library parts, the program logics (Wasm 1.0 Hoare logic and its soundness) and annotated WAT |
| Models | `Silmaril.Wasm.Models`, `Silmaril.Wasm.Atlas`, `Silmaril.Wasm.LimeCompile`, `Silmaril.Wasm.Lime1ToV1`, `Silmaril.Wasm.Resource` | further version models and their simulations, the atlas, Lime compilation |
| Implementations | `Silmaril.Wasm.Wasmi`, `Silmaril.Wasm.Interp`, `Silmaril.Wasm.OCaml` | a wasmi 2.0.0 model, the Binaryen interpreter against Core 3.0, the reference interpreter's OCaml programs |
| Transformations | `Silmaril.Wasm.Replace`, `Silmaril.Wasm.LambdaRTL`, `Silmaril.Wasm.Outcome`, `Silmaril.Wasm.RuntimeMap` | function replacement on reachable stores, the λRTL fragment, outcomes |
| Examples | `Silmaril.Wasm.Examples` | compiled Rust, C and AssemblyScript adders with their proofs (sources in `examples/wasm-demos`) |
| WASI | `Silmaril.Wasi` | WASI preview 1, 0.2 and 0.3 as theories, adapters between them, hosts, worlds, streams, the converse of linking, and the WIT import of the vendored interfaces (`Silmaril.Wasi.Versions.WitImport`) |
| Networking | `Silmaril.Net` | wire formats, IP, UDP, TCP, HTTP/1 and HTTP |
| OCaml | `Silmaril.ML.OCaml` | the OCaml syntax and the generated standard library used by `Silmaril.Wasm.OCaml` |
| Project registry | `Silmaril.Project.Components`, `Silmaril.Project.Formats.{Wit,Wac,Component}`, `Silmaril.Project.Shapes.{Component,Wasm}` | component registry records, the WIT, WAC and component formats, and the component and Wasm problem shapes |

## Building

```sh
lake build Silmaril SilmarilWasiWit
```

The WIT readers of `Silmaril.Wasi.Versions.WitImport` read the files of `specs/wasi` while they
elaborate, so they are the library `SilmarilWasiWit`, whose `needs` cover that directory. Every
other module is in `Silmaril`.

## Third-party material

- `specs/wasi`: unmodified WASI interface definitions (W3C Community Contributor License
  Agreement) and the wasmtime preview1 adapter sources (Apache-2.0 WITH LLVM-exception); see
  `NOTICES/WASI`.
- `Silmaril.Raw.ML.OCaml.Gen.OCamlStdlib`: Lean generated from the OCaml 5.4.1 standard
  library; see `NOTICES/OCaml`.

## Not included

- Modules whose import closure needs the x86 process models (`Machine`), among them part of
  `Wasi.Versions` (the preview1/0.2/0.3 process-level relations and the HTTP and socket
  adapters over OS models) and the WASI 0.3 Rust example registry.
- Modules that need packages this repository does not depend on: the Iris-based program logic
  (`Wasm.Logic.Iris`, `Wasm.FX.Logic.Iris`) and the benchmarks module of the automatic checks.
- The SpecTec meta-theory and the SpecTec Lean 4 backend model.
- The Wasm components pilot registry (registered binaries, records and blobs).

## Known limitations

- Some results are stated over frozen `def Task.x : Prop` statements, used only as
  hypotheses.
- `Raw` modules hold valid but unrefined proofs.
- The tools that generated some modules (the Wasm-to-Lean printer, the OCaml importer) are not
  part of this repository; the generated modules say what they were generated from.

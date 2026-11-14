# Wasm extras: SpecTec meta-theory, Iris, WASI over process models, components

The fourth part of the Wasm release. It adds the Wasm developments that need more than the
earlier parts ([wasm-binaryen-tooling.md](wasm-binaryen-tooling.md),
[wasm-components.md](wasm-components.md), [wasm-wasi.md](wasm-wasi.md)): the SpecTec
meta-theory and the model of SpecTec's Lean 4 backend, the Iris program logics, the WASI
theories that are stated over the x86 process models, the Wasm components registry with its
binaries, the WASI 0.3 Rust example components, and more tools.

## What ships

| Part | Modules | What it is |
| --- | --- | --- |
| SpecTec meta-theory | `Silmaril.Wasm.SpecTec.Meta`, `Silmaril.Raw.Wasm.SpecTec.Scripts.MetaIL`, `Silmaril.Wasm.SpecTec.Institution.Versions.Thms` | the SpecTec internal language's own semantics (the meta-theory branch of SpecTec), imported from `specs/spectec/meta-theory-3a10283c5b/meta-il.ast`, with errata and the version institution results that use it |
| SpecTec Lean 4 backend | `Silmaril.Wasm.SpecTecLean`, `Silmaril.Raw.Wasm.SpecTecLean.Wasm30` | the Lean file SpecTec's Lean 4 backend generates for Wasm 3.0, and a first bridge from Core 3.0 rules to its `Step_pure` rules; the generator patches and the wrapper are in `specs/spectec-lean/` |
| Iris logics | `Silmaril.Wasm.Logic.Iris`, `Silmaril.Wasm.FX.Logic.Iris` | Iris program logics for Wasm and WasmFX (language instance, heap, rules, adequacy, examples), over the `iris-lean` package |
| WASI over process models | `Silmaril.Wasi.{Cli,Os,Runtime,Spec}`, `Silmaril.Wasi.Versions.*` (P2OverP3, P3OverP2, HTTP and socket adapters over OS models), the WIT import certificates | the WASI theories whose statements use the x86 process models |
| Machine | `Silmaril.Machine.{X86,Link,Process}` (part) | the x86 process-model modules these theories import |
| Components registry | `Silmaril.Project.WasmComponents`, `silmaril/wasm-components/*.toml`, `examples/wasm-components` | the components registry: registered binaries (generated components, the WASI preview 1 adapter, `wasi:io` releases, a WAC composition), their records and certificates |
| WASI 0.3 Rust | `Silmaril.Project.WasmP3Rust`, `examples/wasip3-rust` | four WASI 0.3 Rust components (sources, Cargo files, the built `.wasm` in `dist/`) and what is proved about their bytes |
| Automatic checks | `Silmaril.Wasm.Auto2.{Front2,VCInfer,…}` | the `Auto2` headers that use the benchmark modules `tests.wasm.auto.FrontBench` |

## Libraries

`Silmaril.Project.WasmComponents.*` and `Silmaril.Project.WasmP3Rust.*` read records, registered
binaries and the example components while they elaborate, so they are the library
`SilmarilWasmProject`, whose `needs` cover those files. The SpecTec meta-theory modules are in
`SilmarilSpecTec`, whose `needs` now include the meta-theory stream. Every other new module is
matched by `Silmaril`.

## Tools

| Executable | What it is |
| --- | --- |
| `wasm-streams` | executable tests of the stream transformer components under random schedules |
| `wasm-streams-gen` | core modules of stream components generated from byte kernels |
| `wasm-wac-spec` | the expected outputs of the WAC stream pipelines, from the Lean transformers |
| `wasm-wac-kbytes`, `wasm-kappa`, `wasm-kdrop` | generated stream core modules: their bytes by the verified encoder, `κ` on composed binaries, the drop-aware kernel variant |
| `wasm-cm-p3` | the WASI 0.3 component grammar's report for component binaries |
| `wasm-verify` | decodes a Core 3.0 module and runs the verified checker `Silmaril.Wasm.Verify.check` |
| `wasip3-trace`, `cli-core-trace` | run a WASI 0.3 command's core layer on the Core 3.0 interpreter and print its canonical ABI calls |
| `component-wast` | component `.wast` scripts (JSON form) on the component reference machine |
| `wasm-conformance-lean` | the Lean side of a core conformance harness (the harness itself is not included) |
| `wasm-tools-{core,vt,meta,wast,wast-bench,wastenc,witbench,gen-diag}` | narrower builds, benchmarks and diagnostics of `wasm-tools` subcommands |
| `cli-io-demo` | the `Silmaril.Cli.Io.Examples` programs, run |

## Building

```sh
lake build SilmarilWasmProject wasm-streams wasm-verify
```

## Known limitations

- Several results take frozen `def Task.x : Prop` statements as hypotheses.
- `Raw` modules hold valid but unrefined proofs.
- The generators of the generated modules and binaries (SpecTec, the component generators, the
  Rust toolchain) are described next to their outputs but are not run by CI.

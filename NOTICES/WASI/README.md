# WASI notices and provenance

`specs/wasi/` holds unmodified copies of upstream WASI interface definitions and of the
wasmtime preview1 component adapter sources. They are test and reference inputs: the
`Silmaril.Wasi.Versions.WitImport` modules read the `*.wit` files while they elaborate, and the
other WASI modules cite them. Revisions and hashes are in
[specs/wasi/README.md](../../specs/wasi/README.md) and `specs/wasi/SHA256SUMS`.

| Included files | Upstream | Licence |
| --- | --- | --- |
| `specs/wasi/preview1/*.witx` | [WebAssembly/WASI](https://github.com/WebAssembly/WASI), branch `wasi-0.1` | W3C Community Contributor License Agreement, as published by the WebAssembly Community Group: [LICENSE-WASI.md](LICENSE-WASI.md) |
| `specs/wasi/{v0.2.9,0.2.12,0.3.2}/*/*.wit` | [WebAssembly/WASI](https://github.com/WebAssembly/WASI), tags `v0.2.9`, `v0.2.12`, `v0.3.2` (`proposals/*/wit/`) | W3C Community Contributor License Agreement: [LICENSE-WASI-proposals.md](LICENSE-WASI-proposals.md) (each proposal's `LICENSE.md`; the vendored copies are kept next to the files) |
| `specs/wasi/adapter/*` | [bytecodealliance/wasmtime](https://github.com/bytecodealliance/wasmtime) tag `v50.0.1`, `crates/wasi-preview1-component-adapter` | Apache-2.0 WITH LLVM-exception: [LICENSE-wasmtime](LICENSE-wasmtime) |

The WASI texts are not under the Apache-2.0 WITH LLVM-exception licence of the WebAssembly
repositories' code: the files checked here carry the W3C Community CLA notice above, and that is
the licence recorded for them. The files are unchanged; the repository's MIT licence does not
apply to them.

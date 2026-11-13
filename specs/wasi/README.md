# Vendored WASI interface sources

Unmodified copies of the upstream interface definitions that `Silmaril/Wasi/Versions/**` is
checked against (see `docs/projects/wasm-wasi.md`). Nothing here is built; the modules of
`Silmaril.Wasi.Versions.WitImport` read the `*.wit` files while they elaborate (the
`SilmarilWasiWit` library, whose `needs` cover this directory). `SHA256SUMS` lists the hash of every vendored file (`sha256sum -c SHA256SUMS` from this
directory).

| Path | Upstream | Revision | Upstream path |
|---|---|---|---|
| `preview1/typenames.witx`, `preview1/wasi_snapshot_preview1.witx` | <https://github.com/WebAssembly/WASI> branch `wasi-0.1` | `fae981bae14809d91f9bc2d63852d461f331d161` (2025-12-17) | `preview1/witx/` |
| `v0.2.9/<proposal>/*.wit` | <https://github.com/WebAssembly/WASI> tag `v0.2.9` | `34c0258951fb` | `proposals/<proposal>/wit/*.wit` |
| `0.2.12/<proposal>/*.wit` | <https://github.com/WebAssembly/WASI> tag `v0.2.12` | `281ba75fafcd50961ef55f9e52747afcc9b71ede` (2026-06-02) | `proposals/<proposal>/wit/*.wit` |
| `0.3.2/<proposal>/*.wit` | <https://github.com/WebAssembly/WASI> tag `v0.3.2` | `bdadbbb8cadd287cc5014c4b5a0bf76efc60291c` (2026-10-13) | `proposals/<proposal>/wit/*.wit` |
| `adapter/{lib,descriptors,macros}.rs`, `adapter/README.md` | <https://github.com/bytecodealliance/wasmtime> tag `v50.0.1` | `c307ec81de02852d815e9849f7c89d955c03c30d` (2026-10-29) | `crates/wasi-preview1-component-adapter/{src/*.rs,README.md}` |

Only the `*.wit` files of each proposal's `wit/` directory are copied (no `deps/`, `deps.lock`
or `deps.toml`: the `deps/` folders duplicate other proposals). WASI 0.3 has no `wasi:io`
package; its streams and futures are Component Model built-ins.

The official preview1 adapter (`adapter/lib.rs`) is generated against the WIT of
`wasmtime/crates/wasi/src/p2/wit` at the same wasmtime revision, whose packages are all
`@0.2.12`; that is why `0.2.12` is the vendored 0.2 version.

The files were fetched on 2026-11-07 with

```sh
git clone https://github.com/WebAssembly/WASI.git wasi
git -C wasi show fae981bae14809d91f9bc2d63852d461f331d161:preview1/witx/<file>
git -C wasi show v0.2.12:proposals/<p>/wit/<file>      # likewise v0.3.2
git clone --depth 1 --branch v50.0.1 --filter=blob:none --sparse \
  https://github.com/bytecodealliance/wasmtime.git wasmtime
git -C wasmtime sparse-checkout set crates/wasi-preview1-component-adapter
```

## Licenses

* WASI (witx and WIT): published by the WebAssembly Community Group under the W3C Community
  Contributor License Agreement; `LICENSE-WASI.md` (repository root, branch `wasi-0.1`) and
  `LICENSE-WASI-proposals.md` (`proposals/cli/LICENSE.md` at `v0.2.12`; the proposals' license
  files are identical to each other and differ from the root one only in the copyright years).
* wasmtime adapter: Apache License 2.0 with LLVM exception; `adapter/LICENSE-wasmtime`
  (wasmtime's root `LICENSE` at `v50.0.1`).

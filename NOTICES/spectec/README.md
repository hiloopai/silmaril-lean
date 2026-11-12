# SpecTec specification sources and streams

`specs/spectec/` vendors material from the
[WebAssembly specification repository](https://github.com/WebAssembly/spec):

| Path | Upstream revision | What it is |
| --- | --- | --- |
| `specs/spectec/src/` | [`608711107b7f1edb13efd57b7d79b49477462d36`](https://github.com/WebAssembly/spec/tree/608711107b7f1edb13efd57b7d79b49477462d36) | `.spectec` sources of the Wasm 1.0, 2.0 and 3.0 specifications (`specification/`), unmodified, with their SHA-256 sums in `specs/spectec/manifest.json` |
| `specs/spectec/src/spectec/` | same | Three SpecTec frontend files (`lexer.mll`, `parser.mly`, `elab.ml`) that the surface-language fragment follows, unmodified, with the Apache 2.0 licence of `spectec/` (`LICENSE-Apache-2.0`) |
| `specs/spectec/wasm-{1.0,2.0,3.0}.ast` | same | The elaborated internal language of those sources, printed by the SpecTec frontend (`spectec --ast`) |
| `specs/spectec/e7a9df7c/` | [`e7a9df7cdd351df9d8d8546a53248669d51c1aa8`](https://github.com/WebAssembly/spec/tree/e7a9df7cdd351df9d8d8546a53248669d51c1aa8) | The same streams at a later revision, and its root `LICENSE` |

Derived from them in this repository: the generated Lean scripts under
`Silmaril/Raw/Wasm/SpecTec/Scripts/` (written by `tools/spectec-gen` from the
streams), the patched variants of those scripts, and the source excerpts in
`Silmaril/Raw/Wasm/SpecTec/Scripts/Sources.lean`.

[LICENSE](LICENSE) is the exact root licence index of `WebAssembly/spec` at
`e7a9df7c` (also at `specs/spectec/e7a9df7c/LICENSE`). Since upstream commit
[`c794c6a67`](https://github.com/WebAssembly/spec/commit/c794c6a678858b9c6be9f055c0abee51fe0b8ba6)
(WebAssembly/spec#2277) it lists `specification/` under the **W3C Software and
Document Notice and License**; the full licence text is retained in
[`../WebAssembly-spec/core-LICENSE.txt`](../WebAssembly-spec/core-LICENSE.txt),
and the attribution in [`../WebAssembly-spec/README.md`](../WebAssembly-spec/README.md)
applies. The `--ast` streams are mechanical output of the SpecTec frontend on
these sources; we treat them as derived from the specification sources and
under the same licence. The vendored frontend files stay under the Apache
License 2.0 of upstream `spectec/`, whose text is next to them.

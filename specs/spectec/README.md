# Pinned `spectec --ast` streams

`wasm-1.0.ast`, `wasm-2.0.ast` and `wasm-3.0.ast` are the elaborated internal
language of the three WebAssembly specifications, as printed by the official
SpecTec frontend:

```
spectec specification/wasm-N/* --ast-width 80 --ast -o wasm-N.ast
```

at `WebAssembly/spec` revision `608711107b7f1edb13efd57b7d79b49477462d36`.
`manifest.json` records the revision, the `--ast-width`, each stream's SHA-256
and top-level definition count, and the SHA-256 of every `.spectec` source file
that went into it, in the order the official `specification/Makefile` passes
them.  `cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- check-sources`
re-checks the source hashes, and `-- check` the streams against the generated scripts.

The streams are stored uncompressed (2.6 MB in total) because
`spectec_import` (`Silmaril/Raw/Wasm/SpecTec/SpecTec/Import.lean`) reads them at elaboration time and Lean has no
decompressor.

`Silmaril/Raw/Wasm/SpecTec/SpecTec/IL/Decode.lean` turns these files into `IL.Script` values and
`Silmaril/Raw/Wasm/SpecTec/SpecTec/IL/Print.lean` prints them back; `docs/projects/spectec/README.md` describes
the correspondence.

## These streams are kept as they are

A later `WebAssembly/spec` main revision is vendored next to them in `e7a9df7c/`
(`e7a9df7c/README.md`). The streams here are **not** updated: they are the worked
example of importing a SpecTec specification that has defects (errata applied as
checked patches, defects stated as predicates and proved), and they are the base
that every erratum in `Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata/` is written against.
`docs/projects/spectec-divergences.md` compares the two revisions defect by defect.

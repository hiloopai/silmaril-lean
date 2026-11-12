# `spectec --ast` streams of `WebAssembly/spec@e7a9df7c`

`wasm-1.0.ast`, `wasm-2.0.ast` and `wasm-3.0.ast` are the elaborated internal language of the
three WebAssembly specifications at `WebAssembly/spec` revision
`e7a9df7cdd351df9d8d8546a53248669d51c1aa8` (main, 2026-11-03, "[interpreter] Fix
i32x4.dot_i16x8_s and ixx saturation (#2318)"), printed by the SpecTec frontend built at the same
revision:

```
spectec specification/wasm-N/* --ast-width 80 --ast -o wasm-N.ast
```

run from the root of the checkout, with the shell glob in `LC_ALL=C` order (the order
`specification/Makefile` passes the files in). `specification/wasm-latest` at this revision
prints byte for byte the same stream as `wasm-3.0` (SHA-256
`7809e2e6…8138f`); `manifest.json` records it under `aliases` instead of storing it twice.

`manifest.json` has the same layout as `../manifest.json` (revision, `--ast-width`, each
stream's SHA-256 and top-level definition count, and the SHA-256 of every source file), plus
`aliases` and `frontend`. The `.spectec` sources are not vendored.

## How the frontend was built

```sh
git clone https://github.com/WebAssembly/spec && cd spec
git checkout e7a9df7cdd351df9d8d8546a53248669d51c1aa8
cd spectec
# what `make exe` does, without its `opam install` step:
rm -rf src/backend-interpreter/reference-interpreter
cp -R ../interpreter src/backend-interpreter/reference-interpreter
rm -r src/backend-interpreter/reference-interpreter/{dune-project,jslib}
cp src/backend-interpreter/dune-ref-interp src/backend-interpreter/reference-interpreter/dune
nix-shell -I nixpkgs=flake:nixpkgs -p ocamlPackages.{ocaml,dune_3,menhir,menhirLib,zarith,findlib} \
  --run 'dune build src/exe-spectec/main.exe'
```

with nixpkgs `da6dc0e7b26060f2f71ce3ef7088fb56ee44fa36`: OCaml 5.4.1, dune 3.21.1, menhir
20260203, zarith 1.14.

**Reproduction check.** The same recipe at the earlier pin `608711107b` reproduces
`../wasm-{1.0,2.0,3.0}.ast` byte for byte (SHA-256 `8cdad0da…`, `8986f40c…`, `7ae4c580…`), so
the frontend build and the command line are the ones the pinned streams were made with.

## How the streams are used

`tools/spectec-gen` reads `manifest.json` (SHA-256 and definition counts checked, the printer's
byte-for-byte reproduction checked) and writes `Silmaril/Raw/Wasm/SpecTec/Scripts/Main/`;
`Silmaril/Proofs/Wasm/SpecTec/Versions/Import.lean` reads the same files with `spectec_import`
and proves the two readings equal. `docs/projects/spectec-divergences.md` describes what changed and
which defects remain.

## `LICENSE`

`LICENSE` is the repository's root licence notice at `e7a9df7c`, exact bytes (SHA-256
`c06a930f71554662be662d09287c7588b2d9e1aff7a84da503d10ea09a7117c3`). Since
`c794c6a67` ("[license] Add license for specification/ dir (#2277)", 2026-10-13) it lists
`specification/` under the W3C Software and Document Notice and License; the notice at the
original pin (`../src/LICENSE`) named no licence for `specification/`. There is no per-directory
`LICENSE` file in `specification/` or `spectec/` at this revision.

## Re-check against upstream (2026-11-12)

The 57 source SHA-256s of `manifest.json` were compared with the blobs of a fresh clone of
`WebAssembly/spec` at `e7a9df7c` (`git show <rev>:<path> | sha256sum`): all match, as do the 57 of
`../manifest.json` at `608711107b` and the vendored files under `../src/`. This snapshot stays the
latest one vendored: upstream `main` was at `943c5df07e84f11d2b83078964df5812530afbd2`
(2026-11-10), and the commits after `e7a9df7c` that touch `specification/` or `spectec/`
(`6d032009c`, `c4a1a336c`, `859d3232a`, `f3268fa9d`, 2026-11-04 to 2026-11-06) are less than two
weeks old, so no stream was rebuilt from them. Reading their sources, none changes a definition
that a local patch targets (`docs/projects/spectec-divergences.md`).

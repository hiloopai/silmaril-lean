# OCaml notices

`Silmaril/Raw/ML/OCaml/Gen/OCamlStdlib/**` and `Silmaril/ML/OCaml/Stdlib/Defs.lean` are Lean
programs generated from the typed trees of the OCaml 5.4.1 standard library
(<https://github.com/ocaml/ocaml>, tag `5.4.1`). Each generated module names the standard library
unit it comes from. The OCaml standard library is licensed under the GNU Lesser General Public
License version 2.1 with the OCaml static linking exception
(`LGPL-2.1-only WITH OCaml-LGPL-linking-exception`); see the `LICENSE` file of that revision.
These generated files are under that licence, not the repository's MIT licence.

The generated programs under `Silmaril/Raw/Wasm/OCaml/` come from OCaml sources of the
WebAssembly specification repository (<https://github.com/WebAssembly/spec>):

| Generated modules | Upstream source | Licence |
| --- | --- | --- |
| `Silmaril/Raw/Wasm/OCaml/RefInterp/**` | `interpreter/` at `608711107b7f1edb13efd57b7d79b49477462d36` | Apache-2.0 (`interpreter/LICENSE`) |
| `Silmaril/Raw/Wasm/OCaml/SpecTecPin/**` | `spectec/` at `608711107b7f1edb13efd57b7d79b49477462d36` | Apache-2.0 (`spectec/LICENSE`; the text is `specs/spectec/src/spectec/LICENSE-Apache-2.0`) |
| `Silmaril/Raw/Wasm/OCaml/SpecTecMain/**` | `spectec/` at `e7a9df7cdd351df9d8d8546a53248669d51c1aa8` | Apache-2.0, as above |

Each module names the upstream file it was generated from. These generated files are under the
upstream licence, not the repository's MIT licence.

# SpecTec: the WebAssembly specification's DSL in Lean

[SpecTec](https://github.com/WebAssembly/spec/tree/main/spectec) is the language
the WebAssembly specification is written in. Its frontend elaborates `.spectec`
text into an internal language (IL), and `spectec --ast` prints that IL as
S-expressions. This project reads those printed streams into Lean, gives the IL
a meaning, and relates the Wasm 1.0, 2.0 and 3.0 specifications read this way
to the hand-written Wasm semantics in `Silmaril.Wasm`.

Nothing here is an official artefact of the WebAssembly Community Group or of
the SpecTec authors. Where we patch the specification, the patch and our reason
for it are listed in [spectec-divergences.md](../spectec-divergences.md); we may
be mistaken about any of them.

## What ships

| Topic (`Silmaril.Wasm.SpecTec.…`) | Contents |
| --- | --- |
| `Defs`, `Thms` | IL syntax, the S-expression reader and decoder, the elaboration-time import `spectec_import`, IL evaluation, relations and grammars. |
| `AstText` | The `--ast` text format as a relation, and a reader that is sound and complete for it. |
| `Scripts` | The imported Wasm 1.0, 2.0 and 3.0 scripts (`WasmNN.original`) and their patched variants (`WasmNN.fixed`), with theorems that the generated terms are the import and the patches. |
| `Broken`, `Versions`, `VersionEval` | Observations about the pinned scripts stated as predicates and proved, and the same predicates evaluated on a later upstream snapshot. |
| `Surface` | A lexer, parser and elaborator for a fragment of the `.spectec` surface language, checked against lines of the vendored sources. |
| `GrammarInst`, `Institution` | SpecTec grammars and whole scripts as institutions: signatures, models, sentences and consequence. |
| `Sim`, `Sim10`, `Sim20` | Simulations between the SpecTec reduction relation and the Core 3.0 (and 1.0/2.0) small-step semantics, under the assumptions stated in each theorem. |

Some topics depend on parts of the Wasm development that are not public yet
(the Wasm version models, the component model and the cross-version atlas):
the `Institution` instances for Wasm 2.0/3.0 and their chains, parts of `Sim10`
and `Sim20`, `BinaryAgree`, `Lime1Gram` and `SimLime1*`. They are not in this
release.

Two further parts are held back until their licensing is settled: the import of
SpecTec's own IL meta-theory (`Meta`, from the `Wasm-DSL/spectec` `meta-theory`
branch) and the Wasm 3.0 model printed by SpecTec's work-in-progress Lean 4
backend (`Silmaril.Wasm.SpecTecLean`). Both come from the `spectec/` tree of
`Wasm-DSL/spectec`, which carries no licence file at the revisions we used.
The `Institution.Versions` header, which imports `Meta`, is held back with
them. [spectec-divergences.md](../spectec-divergences.md) still describes our
patches to those parts, for reference.

Each topic has a `Defs` and usually a `Thms` header. Longer proofs are under
`Silmaril/Proofs/Wasm/SpecTec/`; the copied and generated parts are under
`Silmaril/Raw/Wasm/SpecTec/`. A few results are stated conditionally on frozen
`Task` propositions; the theorem statements say which.

## How it is built

The inputs are vendored under `specs/spectec/` with their SHA-256 sums:

| Input | Upstream revision | Used for |
| --- | --- | --- |
| `wasm-{1.0,2.0,3.0}.ast`, `src/` | `WebAssembly/spec@608711107b7f1edb13efd57b7d79b49477462d36` (2026-09-22) | The base scripts, the patches and every simulation and institution result. `src/` holds the 57 `.spectec` sources of these streams and the frontend files the surface fragment follows. |
| `e7a9df7c/wasm-{1.0,2.0,3.0}.ast` | `WebAssembly/spec@e7a9df7cdd351df9d8d8546a53248669d51c1aa8` (2026-11-03) | The later snapshot of `Versions`: the same predicates re-evaluated, and the status of each patch. |

Each stream was printed by the official frontend built at the same revision:

```sh
spectec specification/wasm-N/* --ast-width 80 --ast -o wasm-N.ast
```

`specs/spectec/README.md` and `specs/spectec/e7a9df7c/README.md` give the
frontend build, the toolchain and the reproduction check. The licence of the
vendored specification sources is in `NOTICES/spectec/`.

From the streams there are two routes into Lean, and theorems tie them together:

1. `spectec_import` reads a stream at elaboration time, decodes it and adds the
   script as a constant.
2. `tools/spectec-gen` (std-only Rust, unverified) writes the same scripts as
   explicit Lean terms (`Silmaril/Raw/Wasm/SpecTec/Scripts/**`), together with the
   patched variants and the per-patch status rows. Lean then proves each
   generated term equal to the import, or to the import with the patches
   applied.

To regenerate and check:

```sh
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- generate
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- check
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- check-sources
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- errata-status
lake build Silmaril.Wasm.SpecTec.Thms Silmaril.Wasm.SpecTec.Versions.Thms
```

## What is and is not claimed

- The link from file bytes to Lean terms goes through compiled code (the
  generator and the elaboration-time reader). Lean proves that the two readings
  agree; it does not verify the bytes.
- A patch is a checked textual edit of one printed definition. That the edit
  applies is proved. That it is the right correction is our judgement.
- The simulations hold for the readings, domains and assumptions in their
  statements (for example bounded, export-free configurations for the Core 3.0
  whole-step theorem). They are not an equivalence with the official
  interpreter or with every SpecTec backend.
- Functions that the specification leaves as built-ins (numeric primitives,
  `$ieee_`, `$s33_to_u32`, …) are parameters or are supplied by us; results
  that use them say so.

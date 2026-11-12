# spectec-gen

Writes the pinned SpecTec `--ast` streams of `specs/spectec/`, and the scripts their errata
produce, as explicit Lean `IL.Def` data under `Silmaril/Raw/Wasm/SpecTec/Scripts/`. Std-only Rust,
no dependencies. Run from the repository root:

```sh
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- generate       # write
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- check          # byte-identical?
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- check-sources  # vendored .spectec
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- errata-status  # errata vs main
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- theory-diff [--list]  # scripts as theories
cargo run --locked --manifest-path tools/spectec-gen/Cargo.toml -- version all --checkout DIR --revision REV [--build]
```

`version` takes a new `WebAssembly/spec` revision through the pipeline (`src/version.rs`;
`version` alone prints its usage): `vendor` runs the frontend of a checkout over every
`specification/wasm-*` directory and writes `specs/spectec/<rev8>/{wasm-*.ast,manifest.json,README.md}`
(byte-identical duplicates become `aliases`), `scripts` writes the `Original` scripts under a
channel name to a scratch directory, `report` writes a Markdown report (changed declarations
and rules, errata status, known defects that carry over or need a Lean re-check, lints), and
`all` does the three. See `tools/spectec-gen/README.md`.

Two sets of streams are read: the pinned ones of `specs/spectec/manifest.json`
(`WebAssembly/spec@608711107b`, with errata) and the later main ones of
`specs/spectec/e7a9df7c/manifest.json` (`WebAssembly/spec@e7a9df7c`, no errata). The latter are
written as `Main/WasmNN/Original{,/PartK}.lean` (namespace `Silmaril.Wasm.SpecTec.Scripts.Main.*`),
and `Main/ErrataStatus.lean` records, for every `spectec_erratum` command, what became of its
target on main: `unchanged` (patch applies verbatim), `fixedAsErratum` (main's definition equals
the corrected one), `changedStillApplies`, `changedReview` (patch no longer applies) or
`targetGone`. `errata-status` prints the same table.

`theory-diff` reads each script as a theory of the SpecTec specification institution
(`Silmaril.Wasm.SpecTec.Institution`, `docs/projects/spectec/README.md`): its rules, each with its
relation's declaration (`src/theory.rs`). For consecutive versions, every errata variant against
its original, and every pinned stream against main, it reports how many rules are retained
verbatim and which are dropped (`--list`); nothing dropped means the inclusion of theories is a
theory morphism. The comparison is syntactic (S-expression equality) and unverified.

Pipeline:

1. read `specs/spectec/manifest.json`, check each stream's SHA-256 and definition count, parse
   it (`src/sexp.rs`, mirroring `SExp/Parse.lean`) and check the printer (`SExp/Printer.lean`
   transcribed) reproduces the file byte for byte;
2. read the `spectec_erratum` commands of `Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata/*.lean` as text
   (`src/errata.rs`) and apply them as the Lean elaborator does: the unique definition named by
   the target, rendered flat, the fragment replaced exactly once, re-read, then spliced in list
   order (last wins);
3. emit Lean (`src/emit.rs`): a transcription of `IL.decodeDef?` that outputs the term `qDef`
   (`Import.lean`) reflects, so the generated constants are *syntactically* equal to the
   imported ones and the kernel equalities in `Silmaril/Proofs/Wasm/SpecTec/Scripts/` are linear.

Outputs: `WasmNN/Original{,/PartK}.lean` (one `def dI` per top-level definition, `script`),
`Wasm10/Fixed`, `Wasm20/Fixed`, `Wasm30/{Binary51,Text6x,Fixed}` (only the changed
definitions; `script` shares the rest with `Original`), and `Wasm30/AstSlices.lean` (literal
stream text of definitions 0–4 and of `gram Bi32`). `check-sources` verifies each manifest
source present under `specs/spectec/src/`; it passes when none are vendored.

The generator is unverified; Lean proves each generated script equal to the elaboration-time import (see `docs/projects/spectec/README.md`).

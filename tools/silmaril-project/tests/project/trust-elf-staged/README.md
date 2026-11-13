# trust-elf-staged: real producer output for ELF (#127)

`trust.jsonl` was written by `sil project trust-dump` (origin `lean`), over the core's stable
hooks.

Provenance:

- Branch: #127 (`elf/staged-trust`) at `60bf9e14`, which merges core #125 at `6d5b5254`. The ELF
  leaves are declared with `ProcDecl`/`sil_check`.
- Build: a checkout of `60bf9e14`, with dependencies (Mathlib) restored read-only from the
  repository's shared Lake cache.
- Command: `sil project trust-dump --module Silmaril.Elf.Staged.Example.Thms --root Silmaril.Elf.Staged`.
- Roots: only `Silmaril.Elf.Staged.*` is described and audited. Other modules are `external`, but
  their axioms appear in the axioms of the audited declarations.

Result:

- 12 procedures (eight `elf.*` leaves and four `bytes.*`), 299 declarations audited and **0
  violations**.
- 36 uses: 1 native (`elf.layout`, which is in #127's `default` set), and 35 kernel runs, each
  of a declared kernel side.

The sources are not copied here, so the modules read `stale`.

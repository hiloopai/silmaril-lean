# trust-elf-staged: real producer output for ELF (#127)

`trust.jsonl` was written by `sil project trust-dump` with the **legacy** core API (origin `lean`).
#127 (`elf/staged-trust` at `9ad00a40`) merges core #125 at `28418c29`, which predates
`#trust_dump`.

- Build: a checkout of `9ad00a40`, with dependencies (Mathlib) restored from the repository's
  shared Lake cache.
- Command: `sil project trust-dump --module Silmaril.Elf.Staged.Example.Thms --root Silmaril.Elf.Staged`.
- Roots: only `Silmaril.Elf.Staged.*` is described and audited. Other modules are `external`,
  but their axioms still appear in the axioms of the audited theorems.
- Target: the normal example. `Silmaril.Elf.Staged.Example.Profiles` holds the profile tests and
  is not imported.

Result:

- 12 procedures (the eight `elf.*` leaves and four `bytes.*`), 102 theorems and no violations.
- One native use: `elf.layout` is in #127's `default` set.
- The ELF kernel runs (`elf_leaf`) check `Silmaril.KBytes` with a separate kernel checker that
  the legacy registry does not name. They are recorded with `kernel_side = unregistered`: no
  axiom, but no registered identity either. With the v1 core, `ProcDecl`/`sil_check` declares
  that kernel side.

The sources are not copied here, so the modules read `stale`.

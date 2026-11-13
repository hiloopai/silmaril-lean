# trust-elf-staged: real producer output for ELF (#127)

`trust.json` is the core's frozen export (`silmaril.trust-core.v1`), unchanged, written by
`#trust_export` through `sil project trust-dump`.

- Branch: #127 (`elf/staged-trust`) at its head `67503c32`, which merges core #125 at `34ec436e`.
  The ELF leaves are declared with `ProcDecl` and checked with `sil_check`.
- Build: a checkout of `67503c32`, with dependencies (Mathlib) restored read-only from the
  repository's shared Lake cache.
- Command: `sil project trust-dump --module Silmaril.Elf.Staged.Example.Thms --root
  Silmaril.Elf.Staged`. Of the 139 `Silmaril` modules reached, the 10 under `Silmaril.Elf.Staged`
  are listed for audit. The other 130 are described but `unaudited`, so coverage is partial.
- `policy.toml` is a copy of the checkout's, and its digest matches the export.

Result: 299 declarations audited and **0 violations**. `elf.layout` runs natively once; every
other run is a kernel run of a declared kernel side. In the checkout, `--strict-trust` passes on
partial coverage.

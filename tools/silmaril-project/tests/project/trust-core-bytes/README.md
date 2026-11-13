# trust-core-bytes: real producer output (normal targets)

`trust.json` is the core's frozen export (`silmaril.trust-core.v1`), unchanged, written by
`#trust_export` through `sil project trust-dump`. It is not hand-written.

Provenance:

- Core: PR #125 (`prelude/kernel-bytes-trust`) at its head `cbcd896c`. That head includes the
  frozen export `792e7ed6` and the exact-head audit `0b2a82e0`.
- Build: the import closure (24 modules, no Mathlib) was copied into a standalone Lake package
  (`globs = ["Silmaril.+"]`), together with `policy.toml`, `regions.toml`, `lean-toolchain`,
  `scripts/trust-profile-exclude.txt` and the export module.
- Command: `sil project trust-dump --module Silmaril.Prelude.Bytes.Examples --module
  Silmaril.Data.IncludeBytes.KernelExamples --module Silmaril.Data.IncludeBytes.KernelImportExamples
  --module Silmaril.Prelude.Bytes.Checker.Thms`. The command lists every reached `Silmaril` module
  for audit.

`policy.toml` is a copy of the build's. Its SHA-256 equals the export's
`inputs.policy_toml_sha256`, so its own set (`standard`) may be read.

Result:

- 556 declarations audited, **0 violations**. `bytes.cstring` and `bytes.sameBytes` run natively.
- `default` includes the set `elf`, whose member `elf.layout` is not implemented in this
  environment. The export lists it as `named` and `unresolved`, and it is never granted.
- 3 modules declare no theorem or definition (`Bytes.Native.Defs`, `Trust.Policy.Defs`,
  `Trust.Export.Defs`), so they are `unaudited` and coverage is partial. The export does not say
  which modules were listed.
- In the build package, `--strict-trust` passes on that partial coverage.

The sources are not copied here, so the modules read `stale`.

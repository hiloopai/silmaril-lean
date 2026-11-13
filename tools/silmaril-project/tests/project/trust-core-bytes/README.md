# trust-core-bytes: real producer output (normal targets)

`trust.jsonl` was written by `sil project trust-dump` with the **v1** core API (origin `lean`), not
by hand. Its lines are the core's `#trust_dump` (`silmaril.trust.v1`) plus the adapter's
(`silmaril.trust-adapter.v0.1`).

- Core: PR #125, branch `prelude/kernel-bytes-trust`, commit
  `91f7e0de` (`91f7e0de…`, "ProcDecl … and sil_check").
- Targets: `Silmaril.Prelude.Bytes.Examples`, `Silmaril.Data.IncludeBytes.KernelExamples` and
  `Silmaril.Prelude.Bytes.Checker.Thms`. These are normal examples; the profile tests are in
  `trust-core-profile-tests`.
- How it was built: the import closure of those modules and of
  `Silmaril.Prelude.Trust.Examples` (21 modules, no Mathlib) was copied into a standalone Lake
  package (`[[lean_lib]] name = "Silmaril"`, `globs = ["Silmaril.+"]`), with `policy.toml`,
  `lean-toolchain` and `examples/dyn/pinned/hello-gcc`. Then:
  `sil project trust-dump --module Silmaril.Prelude.Bytes.Examples --module Silmaril.Data.IncludeBytes.KernelExamples --module Silmaril.Prelude.Bytes.Checker.Thms`.

Result: no violations, and `--strict-trust` passes in that package. The sources and inputs are
**not** copied here, so this case reports them `missing` and the modules `stale`. The
`lake-manifest.json` digest is the standalone package's.

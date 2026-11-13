# trust-core-bytes: real producer output (normal targets)

`trust.jsonl` was written by `sil project trust-dump` (origin `lean`), not by hand. It holds two
kinds of line:

- the core's lines (`silmaril.trust.v1`), from its stable hooks (`dumpLines`, `allDecls`,
  `moduleLine`, `declsOf`, `auditLine`), the same lines `#trust_dump path M₁ …` writes;
- the adapter's lines (`silmaril.trust-adapter.v0.2`).

Provenance:

- Core: PR #125, branch `prelude/kernel-bytes-trust`, commit `3c731fc1`.
- Targets (normal examples; the profile tests are in `trust-core-profile-tests`):
  `Silmaril.Prelude.Bytes.Examples`, `Silmaril.Data.IncludeBytes.KernelExamples`,
  `Silmaril.Data.IncludeBytes.KernelImportExamples` and `Silmaril.Prelude.Bytes.Checker.Thms`.
- Build: the import closure of those modules and of `Silmaril.Prelude.Trust.Examples` (22
  modules, no Mathlib) was copied into a standalone Lake package (`[[lean_lib]] name =
  "Silmaril"`, `globs = ["Silmaril.+"]`), together with `policy.toml`, `lean-toolchain` and
  `examples/dyn/pinned/hello-gcc`.
- Command: `sil project trust-dump --module …` with the four targets.

Result:

- 21 modules and 551 declarations audited, with **0 violations**.
- The core's per-declaration violation counts agree with the recomputed audit.
- `--strict-trust` passes in that package.

The core lists the realized constants `eq_def` and `match_1.congr_eq_*` once per module that
realizes them. The tool merges these identical audits and reports them.

The sources and inputs are **not** copied here, so this case reports them `missing` and the
modules `stale`.

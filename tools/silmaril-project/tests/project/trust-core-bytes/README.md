# trust-core-bytes: real producer output

`trust.jsonl` was written by `sil project trust-dump` (origin `lean`), not by hand. It covers the
kernel-bytes and trust modules of the core trust work: PR #125, branch
`prelude/kernel-bytes-trust`, commit `28418c290ba266a30dee05d4e327e918433a2f74`.

How it was produced:

1. Copy the import closure of `Silmaril.Prelude.Bytes.Examples`,
   `Silmaril.Data.IncludeBytes.KernelExamples` and `Silmaril.Prelude.Trust.Examples` (17
   modules, no Mathlib) into a standalone Lake package, with `policy.toml`, `lean-toolchain` and
   `examples/dyn/pinned/hello-gcc`. The lakefile is `[[lean_lib]] name = "Silmaril"`,
   `globs = ["Silmaril.+"]`.
2. Run `sil project trust-dump --module Silmaril.Prelude.Bytes.Examples --module Silmaril.Data.IncludeBytes.KernelExamples --module Silmaril.Prelude.Trust.Examples`.

The module sources and inputs are **not** copied here, so this case reports them `missing` and
every module `stale`. The digests in the file are those of commit `28418c29`. That
`lake-manifest.json` digest is the standalone package's manifest, not the repository's.

The three violations are the examples that run `test.evenSum` under the `local` and `toys`
profiles (`Silmaril.Trust.Examples.byLocal`, `byName`, `byToys`). The core's own `trust_audit`
rejects `byLocal` in the default profile too, which its examples expect.

# trust-core-export-rejected: real producer output, refused by name

`trust.jsonl` is a real `#trust_export` document (`silmaril.trust-core.v1`), written by core #125 at
`d5d8f78c` for `Silmaril.Prelude.Bytes.Examples` in the same standalone package as
`trust-core-bytes`, with
`#trust_export "…/trust-core.json" Silmaril.Prelude.Bytes.Examples`. The file name `trust.jsonl` is
only what the test harness passes to `--trust`.

The project database has **one** canonical input: JSON lines of `silmaril.trust.v1` (the core's
stable hooks) and `silmaril.trust-adapter.v0.2`, written by `sil project trust-dump`. The tool
refuses a `silmaril.trust-core.v1` document by name rather than reinterpreting it, and it refuses
the retired `silmaril.trust-dump.v0.1` the same way.

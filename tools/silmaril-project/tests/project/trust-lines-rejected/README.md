# trust-lines-rejected: the retired JSON-lines input, refused by name

`trust.json` holds the first five lines of a real `sil project trust-dump` output in the earlier
JSON-lines format: `silmaril.trust.v1` and `silmaril.trust-adapter.v0.2` lines, from #125 at
`d5d8f78c`. That format is retired as an input. The database now reads only the core's frozen
export (`silmaril.trust-core.v1`). The tool refuses these lines by name and does not convert
them.

# Process/LPS v0.1 promotion

Status: under review as a pull request; no tag or GitHub release yet.

Source commit: `27a27eb4d5af3ac24dcf276aa5700179575da173`.
The selected import closure contains 638 Lean modules.  The promotion records
the source pin, file hashes, and selected roots in `.process-promotion.json`.

| Gate | Status |
| --- | --- |
| Source full CI/replay | Pending: latest full run was killed by runner resource exhaustion. |
| LPS/x86/RV64/ELF/IEEE754 slice | Copied from the pinned source and exposed through public headers. |
| musl launch/probes | Included as recorded model and probe artifacts; fixed-launch caveats remain in source docs. |
| freestanding sha256-cli | VERIFIED end to end (`sha256Cli_total`), with its 2,368-byte image and provenance hash. |
| GNU sha256sum-min | VERIFIED end to end on the stdin tier: six release theorems with no hypothesis (`gnuSha256sum_*` in `Silmaril.Process.Thms`), including agreement with sha256-cli. GPLv3 (`NOTICES/GPLv3/`). |
| import closure | Computed for the selected roots and checked into the promotion metadata. |

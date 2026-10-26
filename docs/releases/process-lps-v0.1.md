# Process/LPS v0.1 promotion

Status: under review as a pull request; no tag or GitHub release yet.

Source commit: `fc6be8f5e6f6de4c7795776842608dc9795c728f`.
The selected import closure contains 509 Lean modules.  The promotion records
the source pin, file hashes, and selected roots in `.process-promotion.json`.

| Gate | Status |
| --- | --- |
| Source full CI/replay | Pending: latest full run was killed by runner resource exhaustion. |
| LPS/x86/RV64/ELF/IEEE754 slice | Copied from the pinned source and exposed through public headers. |
| musl launch/probes | Included as recorded model and probe artifacts; fixed-launch caveats remain in source docs. |
| freestanding sha256-cli | Included with its 2,368-byte image and provenance hash. |
| GNU sha256sum-min | Kept in a separate GPLv3 area (`NOTICES/GPLv3/`); the licence decision is still open. |
| import closure | Computed for the selected roots and checked into the promotion metadata. |

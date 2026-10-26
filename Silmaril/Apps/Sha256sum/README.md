# GNU sha256sum: specification and binary proofs

This subtree holds the executable specification of GNU coreutils 9.4
`sha256sum` (`Basic`, `Options`, `Run`, `StdinRef`, …) and the proofs about the
transcribed `sha256sum-min` image (`Binary`, `IOLayer`, `Lift`, `Stdout`,
`TV`, `X86Sys`). The end-to-end theorems are in
`Silmaril/Process/LPS/Problems/GnuSha256sum/Close.lean`.

GPLv3: see [`NOTICES/GPLv3/SHA256SUM-MIN.md`](../../../NOTICES/GPLv3/SHA256SUM-MIN.md).
The freestanding `apps/sha256-cli` filter has a separate image and does not
use this subtree.

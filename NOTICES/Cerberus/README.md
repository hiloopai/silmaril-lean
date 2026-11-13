# Cerberus-derived definitions

The Lean port of the Cerberus C semantics under `Silmaril/Raw/Cerberus/**`, its headers
`Silmaril/Cerberus/**` and proofs `Silmaril/Proofs/Cerberus/**`, and the Core elaboration
modules that transcribe Cerberus's `translation.lem` (`Silmaril/Cerberus/Elaboration/**`,
`Silmaril/Raw/Cerberus/Elab/**`) are derived from the Cerberus sources at commit
[`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`](https://github.com/rems-project/cerberus/tree/b3e11ea334e95359907d4abf9194f0e7fedc6c6a)
of [rems-project/cerberus](https://github.com/rems-project/cerberus). The Raw modules name
the upstream file (and often the line) each definition transcribes, for example
`frontend/model/core.lem`, `frontend/model/cabs_to_ail.lem`, `frontend/model/translation.lem`,
`frontend/model/core_reduction.lem`, `ocaml_frontend/ocaml_implementation.ml` and
`frontend/model/ail/integerImpl.lem`.

[LICENSE](LICENSE) is the exact upstream root licence at that revision: Cerberus is
distributed under the BSD 2-Clause licence, copyright (c) 2011-2022 the Cerberus authors
listed there, with the exceptions in [THIRD_PARTY_FILES.md](THIRD_PARTY_FILES.md) (also
exact at that revision).

Of those exceptions, only one reaches this port: the `memory_order` enumeration of
`Silmaril.Cerberus.Mem` follows `frontend/concurrency/cmm_csem.lem`, which Cerberus derives
from the Cppmem tool under the BSD 3-Clause licence. Its notice is retained in
[cppmem-cmm_csem-NOTICE.txt](cppmem-cmm_csem-NOTICE.txt) (the first 36 lines of that file at
the same revision). No GPL file (`runtime/bmc/*.cat`), musl-derived runtime library file or
SibylFS file of Cerberus is transcribed or bundled.

The Lean transcription changes the implementation language, makes the memory model a
parameter, restricts the supported profile (unsupported constructs are rejected explicitly)
and adds executable checks and correctness proofs. Copyright (c) 2026 Silmaril contributors
for modifications and original contributions. MIT applies to original contributions and does
not replace the upstream rights and notices attached to Cerberus-derived material.

The Cerberus OCaml implementation, its runtime library sources (`std.core`, `.impl` files,
libc) and its test corpus are not bundled.

`benchmarks/cerberus-elaboration/oracle` holds output of Cerberus at the same revision on 18
small C programs: Core documents (which carry Cerberus's Core runtime maps, derived from its
`std.core` and `.impl` files, in serialized form), typed Ail, listings and execution
observations. They are Cerberus output under the same licence; the only change is the
normalization of one installation prefix, described in that directory's README.

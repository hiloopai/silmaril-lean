# sail-riscv-derived definitions

The RV64 integer fragment `Silmaril/Raw/Machine/RiscV/{Basic,Encoding}.lean` (and the modules
built on it under `Silmaril/{,Raw/}Machine/RiscV/**`) is a handwritten, proof-friendly
normalization of clauses of the Sail RISC-V model (`ITYPE`, `RTYPE`, `SHIFTIOP`, `UTYPE` and
their encodings) at revision
[`27224ccb2290f022e46213c05b3e72e8a9ea635e`](https://github.com/riscv/sail-riscv/tree/27224ccb2290f022e46213c05b3e72e8a9ea635e)
of [riscv/sail-riscv](https://github.com/riscv/sail-riscv).

[LICENCE](LICENCE) is the exact upstream licence at that revision: the Sail RISC-V model is
distributed under the BSD two-clause licence, copyright the contributors listed there.

No generated Sail code is included, and the correspondence of these definitions with the
generated Sail model is not part of this repository.

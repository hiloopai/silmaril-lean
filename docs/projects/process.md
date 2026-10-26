# Linux process semantics

This promotion brings the reviewed process-model slice from source commit
`fc6be8f5e6f6de4c7795776842608dc9795c728f` into the public curated tree.  It
includes the syscall table and translated-arm checks, the x86-64 and RV64 LPS
models, ELF CST/`IsCST` facts, musl launch models, and the recorded probe
families.  The source snapshot contains 509 Lean modules in the selected
closure; the full upstream closure is larger and is intentionally staged.

```mermaid
flowchart LR
  ELF[ELF bytes] --> CST[ELF CST / IsCST]
  CST --> LOAD[loader and musl startup]
  LOAD --> SYSCALL[90-arm syscall table]
  SYSCALL --> X86[x86-64 LPS]
  SYSCALL --> RV[RV64 LPS]
  X86 --> PROBES[recorded Linux probes]
  RV --> PROBES
```

The public headers are `Silmaril.Process.Defs` and `Silmaril.Process.Thms`.
Long proofs remain in their source topic modules so reviewers can promote them
incrementally.  The source repository's full replay check is still pending
because its latest run exhausted the runner while checking the complete tree.

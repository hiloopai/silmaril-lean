# Process memory, I/O contracts, and observable traces

`Silmaril.Process` provides byte-addressed memory with read/write/execute
permissions and explicit stream I/O contracts. It has no instruction set,
register convention, ELF parser, or hardware page-table dependency. The RV64
register adapter is isolated in `Silmaril.RiscV.Linux.ABI`; another architecture
can reuse the memory, descriptors, streams, and trace contracts.

`Memory` checks the entire non-wrapping access span. Successful writes preserve
mapping metadata and all bytes outside the written interval. Its well-formedness
predicate requires disjoint aligned regions and backing for every mapped byte.
Both initial byte installation and checked writes preserve those properties.

`Syscall.Step` describes completed `read`, `write`, and `exit` interactions. It
admits positive short transfers, EOF, zero-length requests, and errors. An input
stream is immutable, with an explicit consumption cursor, and may be finite or
infinite. Output events record accepted bytes in order. Read errors may change
bytes within the requested buffer and consume an allowed input prefix; proofs
must therefore handle errors without assuming the buffer was untouched.
The contracts retain descriptor modes, other descriptors, and memory outside the
allowed write span. Exit is terminal and records the low eight status bits.

The intended Linux realization uses a single thread, private mappings and file
descriptors, no external memory mutation, and no asynchronously delivered
signals. SIGPIPE must be ignored or blocked for a broken-pipe write to return
an error. Calls may block: the transition system only records completed calls.
These are assumptions about the OS environment, not a verified Linux kernel.

The RV64 adapter uses a7 for syscall numbers (read 63, write 64, exit 93), a0–a5
for arguments, and a0 for raw results, including negative errno values. It
specifies a return to PC+4 with other integer registers restored. The generated
Sail ECALL trap and the Linux trap-handler implementation are separate from
this adapter contract.

The generated user-mode connection is developed in
[`RiscVUserspace.md`](RiscVUserspace.md). Its physical-memory relation retains
protected page tables while comparing only mapped user bytes, and reflects
every target syscall response through the same architecture-independent contract.

`Machine.Trace` provides finite observed runs and forward refinement that
quantifies over every admitted implementation step. The bounded summation
protocol in `RiscV.Linux.Protocol.Execution` exercises this boundary: stdin is
an eight-byte little-endian count at most 16, followed by that many 64-bit words
and EOF. Success emits the eight-byte modular sum and exits 0. Malformed input,
read failure, and write failure exit 2, 3, and 4 respectively; a failed write may
have emitted a strict prefix of the result. The prefix and exit theorems derive
these constraints from actual protocol events without assuming valid input.

A decreasing rank rules out infinitely many completed protocol transitions
and gives an initial bound of 149. This is a protocol bound, not an instruction
count or a guarantee that a blocked OS call returns. The complete machine-code
refinement is described in [`LinuxExecutable.md`](LinuxExecutable.md).

```sh
lake build Silmaril.Process Silmaril.Machine.Trace \
  Silmaril.RiscV.Linux.ABI Silmaril.RiscV.Linux.Protocol.Execution --wfail
```

The LPS translation (Theorem Labs' Rocq Linux process model, 90 syscall arms, the OSS Verify
statement shapes, parametric in the ISA) is described in [`LPSProcess.md`](LPSProcess.md).

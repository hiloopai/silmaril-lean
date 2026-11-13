# litmus-run

Hardware litmus harness for the x86 litmus corpus. It runs
every corpus test natively on the host CPU and checks that the observed final states lie in
the model-allowed sets.

## What it runs

The input is `tools/litmus-x86/export/corpus.json`, written by `litmus-x86 export`. The JSON
is produced in the same run as the Lean table `Silmaril/X86/MemoryModel/Litmus/Corpus/Defs.lean`,
and the export refuses to run unless the Lean file is byte-identical to its regeneration. The
cargo test `export_matches_lean_table` also checks, textually, that every instruction's bytes
and every verdict in the JSON appear in the Lean table.

Per test:

- **Memory.** The locations live at their fixed corpus addresses: a private anonymous RW
  write-back mapping of 64 KiB at `0x10000` (`MAP_FIXED_NOREPLACE`; `vm.mmap_min_addr` is
  65536 here). Before each iteration, the coordinator (thread 0) resets the locations to their
  initial bytes.
- **Code.** Each litmus thread's corpus bytes are copied unchanged and contiguously into an RX
  page, between a fixed prologue and epilogue (`src/wrap.rs`). The prologue loads the
  register file; the epilogue stores the final registers and returns. The corpus code has no
  branches and only absolute operands. A test whose threads have a `code_base` (the compiled
  C11 tests of `tools/litmus-x86/export/c11.json`, which use rip-relative operands) instead
  has its bytes and the epilogue mapped at that fixed address (`MAP_FIXED_NOREPLACE`), entered
  from a stub of the prologue and `jmp *0(%rip)`; the stack frame is the same. The wrapper touches only the thread's stack and
  register file. A cargo test checks the hand-encoded wrapper against GNU `as`.
- **Threads.** One `std` thread per litmus thread, each pinned with `sched_setaffinity` to a
  distinct physical core (one logical CPU per `(physical_package_id, core_id)`, never two
  SMT siblings).
- **Iteration.** Reset, spin barrier, a random delay of 0..=`--delay` loop iterations (default
  256; no memory accesses), the test code, publish the registers, spin barrier. The
  coordinator then reads the locations and the observed registers and adds the final state to
  the histogram. The barrier's `lock xadd` drains every store buffer, so the coordinator reads
  the coherence-final values.
- **Outcome.** The registers the thread may write or the condition names (`observe` in the
  JSON), plus every location's bytes. This is the same projection as the allowed sets.

## Checks

- **TSO-covered tests (60).** Every observed outcome must be in `allowed.tso`, the distinct
  final states of the consistent executions of `litmus-x86`'s checker (a transcription of
  herd's `x86tso.cat`; tested, not proved; not herd7 and not Lean output).
  `--model sc` checks against `allowed.sc` instead. That is a negative control: it must fail
  on SB-like tests.
- **XL-only tests (8).** There is no XL outcome set yet, only the recorded XL witness verdict.
  The run fails if that verdict is `forbidden` and the witness is observed. When XL allows a
  witness, observing it is not required: XL is deliberately weaker than this hardware.
- The report lists the TSO-allowed, SC-forbidden ("TSO-only") outcomes that were observed,
  and the TSO-allowed outcomes that never were.

Never observing a forbidden outcome is evidence, not proof.

## Usage

```sh
cd tools/litmus-run
cargo run --release -- --list
cargo run --release -- --test SB --test IRIW+mfences --time 5
cargo run --release --                      # whole corpus, 2 s per test, time-based seed
cargo run --release -- --ci --report hw.md        # fixed seed, 3,000,000 iterations per test
cargo run --release -- --model sc --test SB # negative control: must FAIL
cargo run --release -- --json ../litmus-x86/export/c11.json --time 1.5   # compiled C11 tests
cargo test --release                        # unit tests + cross-checks + short hardware smoke run
```

Options:

- `--json FILE`, and `--test NAME` (repeatable);
- `--time SECS` (default 2; a cap in every mode), `--iters N` and `--seed N`;
- `--delay N` (default 256), `--model tso|sc` and `--report FILE` (Markdown);
- `--ci`: seed `0x53696c4c69743500`, 3,000,000 iterations, 5 s cap per test. A capped run is
  reported as `CAPPED`, not as a failure. The seed fixes only the delay sequence: the outcomes
  depend on the hardware.

The exit status is 1 if any check fails. The tool requires Linux on x86-64 and as many
physical cores as the widest test has threads (4). The crate is std only and declares the five
libc symbols it uses (`mmap`, `munmap`, `mprotect`, `sched_setaffinity`, `sched_getaffinity`).

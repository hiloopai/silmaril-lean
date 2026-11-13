# litmus-hw: the multithreaded models against real hardware and real binaries

Experiments that check the memory models, the multithreaded process model and the simple
pthread model against this machine's CPU and against real runs of pthread binaries. The
method, the results and the limitations are in [docs/mt-validation.md](../../docs/mt-validation.md);
the recorded outputs are in [results/](results/).

| file | what it does |
|---|---|
| `lattice_hw.c` | Runs one litmus test per separating execution of the memory-model lattice (`Silmaril.X86.MemoryModel.Lattice`), 15 tests, with a chosen thread placement and delay range. |
| `lattice.py` | Compares `lattice_hw` counts with the verdict rows proved in `Silmaril.X86.MemoryModel.Lattice.Witness.Thms`. It checks TSO and XL soundness and that the rows respect the order, and reports which strict edges hardware crosses. |
| `simple_model.py` | Exhaustive explorer of the simple pthread model (`Silmaril.Process.Mt.Pthread.Simple`), with `p1`…`p8` transcribed from `scripts/pthread-hw/src`. It reports outcome sets, undefined behaviour, races (`Csl.Race`, read/read included, and write races) and deadlocks. |
| `perturb.c` | `LD_PRELOAD` shim that perturbs schedules around every pthread call and at thread start (random `sched_yield`, spins and migrations). The binary's bytes are unchanged. |
| `pthread_diff.py` | Differential test: runs the pthread binaries (pinned full-size binaries and small-bound rebuilds) under 16 configurations (host or pinned glibc, 4 placements, with or without perturbation) and checks every observed output against the model's outcome set. |
| `Silmaril/Proofs/Process/Mt/Explore.lean` | (in the library) Every schedule of four small raw-byte x86-64 programs under the multithreaded process model's executable SC scheduler (`Silmaril.Process.Mt.X86.exec1`). `#guard` checks the outcome sets. |
| `mtproc_hw.c` | The same bytes run natively, with two pinned threads, many times. |

The 68-test corpus uses `tools/litmus-run` from PR #143 (`oss-mm/models-litmus`) unchanged. It
is not duplicated here; its reports are in `results/corpus-*.md`.

```sh
# lattice witnesses: 50M iterations per test, physical cores 0-3, then SMT siblings 0,6,1,7
cc -O2 -Wall -pthread tools/litmus-hw/lattice_hw.c -o /tmp/lattice_hw
/tmp/lattice_hw 50000000 0,1,2,3 64 > cores-d64.txt
/tmp/lattice_hw 50000000 0,6,1,7 64 > smt-d64.txt
python3 -I tools/litmus-hw/lattice.py cores-d64.txt smt-d64.txt          # --markdown for a table

# the 68-test corpus (in a checkout of PR #143)
cd tools/litmus-run && cargo run --release -- --iters 30000000 --time 600 --report hw.md
cargo run --release -- --model sc --test SB --test R --test n6           # negative control: must FAIL

# simple pthread model, exhaustively, and the differential test
python3 -I tools/litmus-hw/simple_model.py p1:2 p5:3 p3 p7:10 p8
PINNED_LIBC_DIR=/path/to/glibc-2.39-0ubuntu8.9/usr/lib/x86_64-linux-gnu \
  python3 -I tools/litmus-hw/pthread_diff.py /tmp/diff 400 30

# multithreaded process model: native runs of the explored bytes
cc -O2 -Wall -pthread tools/litmus-hw/mtproc_hw.c -o /tmp/mtproc_hw && /tmp/mtproc_hw 1000000 0,1
```

The CPU numbers are for the recording machine, an i7-8700 where CPUs `n` and `n + 6` are SMT
siblings. Check `lscpu -e` before choosing placements elsewhere.

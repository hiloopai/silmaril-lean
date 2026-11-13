# Validating the multithreaded models experimentally

The multithreaded development has three kinds of model: the memory models and their lattice
(`Silmaril.X86.MemoryModel.{Axiomatic,Xl,Lattice}`), the multithreaded x86 process model
(`Silmaril.Process.Mt`, `Mt.X86`), and the POSIX thread specifications with the simple pthread
model (`Silmaril.Process.Mt.Pthread`, `Pthread.Simple`). This note records how they were
checked against one real CPU and real binaries, what was found, and what such checks cannot
show. The tools are in [tools/litmus-hw](../tools/litmus-hw/README.md); the raw outputs are in
`tools/litmus-hw/results/`.

**The rule.** If hardware shows an outcome that a model claims to cover and forbids, the model
is wrong. If a model allows an outcome that hardware never shows, that is expected for a model
meant to over-approximate (XL, RA, the catch-fire models), or a coverage gap of the
experiment. A run that never shows an outcome does not prove it impossible.

## Results at a glance

| check | runs | result |
|---|---|---|
| 68-test x86 corpus (`tools/litmus-run`), x86-TSO verdicts | 30 M iterations per test (2.04 G total), plus a 5 M run | **sound**: no TSO-forbidden outcome on any of the 60 TSO-covered tests, no XL-forbidden witness on the 8 XL-only tests |
| the same, checked against SC (negative control) | SB, R, n6 at 2 M | fails as it must: SC is not a model of this CPU |
| lattice witnesses (`lattice_hw.c`), 15 tests, 6 models | 50 M per test in each of 4 placement/delay configurations (3 G total) | **sound** for TSO and XL; hardware crosses `sc ⊏ tso` (SB) and, only with non-temporal or misaligned accesses, `tso ⊏ xl` and `cfPlain ⊏ top`; on TSO-covered tests it never shows the outcomes that separate `tso` from `ra` and `cf` |
| multithreaded process model, every schedule of 4 raw-byte programs vs. 1 M native runs each, two placements | 924 schedules for SB | MP, INC2, LOCKINC2: **the same outcome sets**. SB: hardware shows `r1 = r2 = 0` (6 568 and 662 times), which the model's SC runs never reach. That is expected, because SB is racy; see below |
| simple pthread model, exhaustive, 17 program instances | up to 1.14 M configurations | outcome sets equal the expected outputs; **`Csl.Race` finds read/read races in `p3`, `p4` and `p7`**, so `Simple.RaceFree` is false for them |
| pthread binaries vs. the simple model, 22 binaries × 16 configurations (host and pinned glibc, 4 placements, with or without perturbation) | 400 runs per configuration (small bounds), 30 (full size) | **no output outside the model's set**; the racy counter's rare outcomes need perturbation or larger bounds to appear |

**No model bug was found:** nothing the models claim to cover was contradicted. The findings
are a coverage limitation of the x86 process model under racy code, two harness defects, a
race definition stricter than the programs need, and the over-approximations listed below.

## Machine and software

Intel Core i7-8700 (Coffee Lake, family 6 model 158 stepping 10, microcode `0xfa`), 6 cores /
12 threads. CPUs `n` and `n + 6` are SMT siblings, and there is one NUMA node. The software was
Linux 6.8.0-139 (Ubuntu 24.04) and gcc 13.3.0. The host glibc is **2.39-0ubuntu8.12**
(`libc.so.6` SHA-256 `755a371e…`). It was upgraded after the pthread pins were taken against
**2.39-0ubuntu8.9** (`3a15d668…f7498bf`). The pthread binaries were therefore run under both:
the host's loader, and the pinned package's own `ld-linux-x86-64.so.2` (SHA-256 `c20a2dc8…`)
with `--library-path`. The pinned binaries rebuild byte-identically from `scripts/pthread-hw`
(the loop bounds are now overridable with `-DN`/`-DK`/`-DR`; the default build is unchanged).
Runs were taken on 2026-11-13.

## 1. Hardware litmus tests

### The corpus (68 tests)

`tools/litmus-run` (from #143) copies each corpus test's instruction bytes verbatim into an
executable page between a register-loading prologue and a register-storing epilogue. It pins
one thread per **physical** core, resets the locations, synchronises the threads with a
`lock xadd` barrier and a random delay, and records the registers and the final memory. Every
observed final state must lie in the test's TSO-allowed set, which the `litmus-x86` checker
(a transcription of herd's `x86tso.cat`) computes. For the 8 XL-only tests (non-temporal
stores, string stores, straddling and mixed-size accesses) there is only a witness verdict,
and the check is that an XL-forbidden witness never appears.

Results (`results/corpus-tso-30M.md`, 30 000 000 iterations per test; the 5 M run in
`results/corpus-tso.md` agrees):

* **Every check passed.** TSO-allowed, SC-forbidden ("TSO-only") outcomes were observed in
  13 tests: SB (1 179 167 times), SB+mfence+po, SB+rfi-pos, R, R+mfence+po, R+mfence+rfi-po,
  iwp2.3.a/amd4, iwp2.4/amd9, amd3, n6 (8 627), n7 (247), n1, rwc-unfenced (620).
* No TSO-forbidden outcome appeared, in particular none of MP, LB, S, 2+2W, IRIW+mfences,
  the fenced variants, and the locked-RMW tests (`SB+lock-*`, `RMW+*`).
* TSO-allowed outcomes never observed: one in amd3, eight in iwp2.6, two in n3 and one in n1.
  These are rare interleavings of three- and four-thread tests, not evidence against the
  model.
* XL-only tests: the MP+movnti reordering (249 978) and a torn straddling access in
  MIS+straddle (9) were observed. The XL-forbidden witnesses of MP+movnti+sfence,
  MP+movnti+lock and MP+stosb+sfence never were. Three XL-allowed witnesses never appeared:
  MS+halves, MP+stosb and STOS+internal. XL allows them, and this CPU never produced them.
* Negative control: `--model sc` on SB, R and n6 fails, with SC-forbidden outcomes 74 309,
  39 374 and 4 645 times in 2 M iterations (`results/corpus-sc-negative.log`).

### The lattice's witnesses

`Silmaril.X86.MemoryModel.Lattice` orders seven models: `sc ⊑ tso`, `tso ⊑ xl`,
`tso ⊑ ra ⊑ cfPlain`, `tso ⊑ cf ⊑ cfPlain`, and every model `⊑ top`. Each strict edge is
witnessed by an execution that the upper model allows and the lower one forbids.
`lattice_hw.c` runs one hardware test per witness, 15 tests in all. The new module
`Silmaril.X86.MemoryModel.Lattice.Witness` gives each test's witness outcome its candidate
execution, and **proves the verdicts of all six non-trivial models on it**
(`Witness.<name>_row`, by `decide` through the exact Boolean checks of
`Witness.verdict_of_row`). It adds three executions: `sbXchg`, `inc2`, and the two-writer CoWR
executions `coWR2` and `coWR2b`. `lattice.py` compares the counts with these rows.

Four configurations were run, 50 M iterations per test in each. Threads were placed on
distinct physical cores (`0,1,2,3`) or on pairs of SMT siblings (`0,6,1,7`), and the random
delay before each body was drawn from 0..63 or 0..511 loop iterations
(`results/lattice-*.txt`, table in `results/lattice-table.md`):

| test | witness outcome | sc | tso | ra | xl | cf | cfPlain | observed (cores/64, smt/64, cores/512, smt/512), of 50 M each |
|---|---|---|---|---|---|---|---|---|
| SB | `r0=0 r1=0` | ✗ | ✓ | ✓ | ✓ | ✓ | ✓ | 4 000 347, 1 768 369, 1 139 546, 364 784 |
| SB+mfences | `r0=0 r1=0` | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | 0, 0, 0, 0 |
| SB+xchgs | `r0=0 r1=0` | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | 0, 0, 0, 0 |
| MP | `r0=1 r1=0` | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | 0, 0, 0, 0 |
| LB | `r0=1 r1=1` | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | 0, 0, 0, 0 |
| IRIW | readers disagree | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | 0, 0, 0, 0 |
| 2+2W | `x=1 y=1` | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | 0, 0, 0, 0 |
| MP+movnti | `r0=1 r1=0` | ✗ | ✗ | ✗ | ✓ | ✗ | ✗ | 476 642, **0**, 26 429, **0** |
| MP+movnti+sfence | `r0=1 r1=0` | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | 0, 0, 0, 0 |
| SPLIT8 (8 bytes across a line) | torn | ✗ | ✗ | ✗ | ✓ | ✓ | ✓ | 251 933, 441 891, 15 951, 50 641 |
| TORN2-inline (2 bytes at offset 1) | torn | ✗ | ✗ | ✗ | ✓ | ✓ | ✓ | 0, 0, 0, 0 |
| TORN2-cross (2 bytes across a line) | torn | ✗ | ✗ | ✗ | ✓ | ✓ | ✓ | 13 970, 355 637, 1 296, 56 411 |
| INC2 (`inc` twice) | `x=1` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 3 708 352, 2 469 774, 1 771 320, 514 291 |
| LOCKINC2 (`lock inc` twice) | `x=1` | ✗ | ✗ | ✗ | ✗ | ✗ | ✓ | 0, 0, 0, 0 |
| CoWR (`x:=1; r0:=x` ∥ `x:=2`) | `r0=0`, or `r0=2 x=1` | ✗ | ✗ | ✗ | ✗ | ✓ | ✓ | 0, 0, 0, 0 |

What this says about the lattice:

* **TSO and XL are sound here.** No outcome forbidden by x86-TSO appeared on a TSO-covered
  test, and no outcome forbidden by XL appeared on any test. Since `tso ⊑ ra`, `tso ⊑ cf` and
  `cf ⊑ cfPlain` are proved, every observation on the TSO-covered tests is also allowed by
  `ra`, `cf` and `cfPlain`. The table checks this row by row.
* **`sc ⊏ tso` is crossed by hardware** (SB, up to 8 % of iterations): SC is not a model of
  this CPU.
* **`tso ⊏ xl` is crossed only outside TSO's coverage:** by the non-temporal store
  (MP+movnti) and by accesses that straddle a cache line (SPLIT8, TORN2-cross). A misaligned
  2-byte access inside a line never tore in 200 M iterations, which matches Intel's
  single-copy atomicity guarantee for accesses within a line. XL allows the tear for every
  misaligned access, so it over-approximates this CPU there.
* **`cfPlain ⊏ top` is crossed by MP+movnti**, a race-free execution that is not SC
  (`Lattice.mpNt_drf_not_sc`). This is the hardware counterpart of the tameness hypothesis of
  `drf_sc_xl_tame`: without it, DRF-SC really fails on x86.
* **`tso ⊏ ra`, `tso ⊏ cf` and `cf ⊏ cfPlain` are never crossed on TSO-covered tests.** IRIW,
  2+2W, SB with fences or `xchg`, a lost `lock inc` and the coherence violations never
  appeared. On this CPU the weaker models are strict over-approximations of hardware
  behaviour. That is their purpose: results proved under `ra` or `cf` transfer down to `tso`.
* MP+movnti's reordering never appeared when the two threads were SMT siblings, in 100 M
  iterations, while distinct cores showed it 503 071 times.

**DRF-SC, experimentally.** The DRF-SC theorems (`Lattice.drf_sc_tso`, `drf_sc_xl_tame`;
`Process.Mt.Drf.drf_sc`) say that race-free executions of tame accesses are SC. In every
race-free test above (MP, LB, MP+movnti+sfence, LOCKINC2, which is race-free modulo locked
accesses), and in the corpus's race-free tests, hardware showed only SC outcomes. The
non-SC outcomes appeared only in racy tests (SB, R, n6, …) and in the non-tame MP+movnti.

## 2. The multithreaded process model against native runs

`Silmaril/Proofs/Process/Mt/Explore.lean` builds four two-thread x86-64 programs as raw bytes
(SB, MP, two unlocked increments, two `lock add`s). Each ends with a raw `exit(0)` system
call. It explores **every schedule** with the model's executable scheduler
`Mt.X86.exec1`, whose runs are `MtProc X sc` runs (`run_sound`). `#guard` checks the outcome
sets, so the build fails if they change. `mtproc_hw.c` runs **the same bytes** natively. Each
iteration creates two threads (two physical cores, or two SMT siblings), meets at a barrier
with a random delay, and jumps into the bytes, which end the thread with the same system call.
There were 1 000 000 iterations per program and placement (`results/mtproc-*.txt`):

| program | model, every schedule | native, cores 0,1 | native, SMT siblings 0,6 |
|---|---|---|---|
| SB `[r1, r2]` | `{01, 10, 11}` (924 schedules) | `00`: **6 568**, `01`: 358 219, `10`: 633 489, `11`: 1 724 | `00`: **662**, `01`: 457 477, `10`: 539 703, `11`: 2 158 |
| MP `[flag, data]` | `{00, 01, 11}` | `00`: 623 308, `01`: 14 560, `11`: 362 132 | `00`: 509 489, `01`: 37 096, `11`: 453 415 |
| INC2 `x` | `{1, 2}` | `1`: 12 140, `2`: 987 860 | `1`: 115 648, `2`: 884 352 |
| LOCKINC2 `x` | `{2}` | `2`: 1 000 000 | `2`: 1 000 000 |

The exit status was 0 in every model run. MP, INC2 and LOCKINC2 have exactly the model's
outcome sets. MP's forbidden `10` never appeared, the lost update did, and the locked one never
did. **SB's `00` is outside the model**: the executable scheduler is SC. In the process model
this outcome is reachable only through the `tso` memory system's buffered plain steps, and
those need each instruction's access list. `mtX` does not emit access lists yet (`Task.x86Acc`
in `Mt/Drf/Defs`), so under `tso` every `mtX` instruction also behaves as a barrier. **For
racy programs, the x86 process model as instantiated today is not sound for this CPU.** For
race-free programs it is meant to be sound, through the DRF-SC theorem, which is still open
for this model (`Task.drfSc`). Programs whose correctness depends on the outcome of a race
(lock-free code with plain accesses) cannot be verified against it yet.

## 3. The simple pthread model, and pthread binaries against it

### Exhaustive exploration of the model

`simple_model.py` is an executable transcription of `Pthread.Simple` (`tisa`, `start`,
`Csl.Step`, `Csl.Fault`, `Csl.Race`) and of every `Op.spec` of `Pthread/Defs`, with the eight
programs of `scripts/pthread-hw/src` written in the model's instruction set and the loop bounds
as parameters. It explores all reachable configurations, deduplicating them. Three reductions
are used, and each is sound for what is reported: a fresh thread gets the least unused id,
`pthread_key_create` the least free key (no program prints either), and a thread at a
register-only instruction steps alone (such steps commute with everything and have no
footprint). The transcription is by review, not extracted from Lean. Its results agree with
every expected output and with the hardware.

| program (bound) | configurations | outcome set | UB | `Csl.Race` (write races) | deadlocks |
|---|---|---|---|---|---|
| p1 mutex counter (N=2, 3) | 275, 613 | `{2N}` | 0 | 0 | 0 |
| p2 producer/consumer, condvars (N=2, 3) | 177, 251 | `{N(N+1)/2}` | 0 | 0 | 0 |
| p3 `pthread_once`, 4 threads (full) | 54 251 | `{"1 4"}` | 0 | **7 200 (0)** | 0 |
| p4 TLS keys, 4 threads (K=1, 2) | 444 951, 695 080 | `{"4 4 0"}` | 0 | **11 890, 15 472 (0)** | 0 |
| p5 racy counter (N=1, 2, 3, 4) | 114 … 5 079 | `{1,2}`, `{2,3,4}`, `{2..6}`, `{2..8}` | 0 | 4 … 536 (3 … 423) | 0 |
| p6 spin-lock counter (N=2, 3) | 276, 614 | `{2N}` | 0 | 0 | 0 |
| p7 semaphores + barrier, 4 threads (R=1, 2, **10 = full**) | 1 143 555 … 1 144 091 | `{"abab…ab 4 1"}` | 0 | **183 620 (0)** | 0 |
| p8 error returns (full) | 67 | the POSIX/glibc codes | 0 | 0 | 0 |

* The outcome sets are the expected outputs (singletons), and `p5`'s is `[2, 2N]` for
  N ≥ 2. For p3, p7 and p8 the full program was explored exhaustively; for the others, the
  small bounds.
* **`Csl.Race` counts two reads of one cell by two threads as a race.** p3 (all threads read
  `value` after `pthread_once`), p4 (all workers read the key cell) and p7 (all threads read
  the barrier slots) have such read/read races and no write race. So `Simple.RaceFree p3`,
  `p4` and `p7` are **false**; race freedom holds for them only with races restricted to
  pairs with a write. The read-only sharing layer of #149 (`Csl.Ro`) addresses
  the same point for the decomposition.
* No reachable configuration faults (no undefined pthread use) or deadlocks, including p2 with
  spurious wake-ups.

### Differential testing of the binaries

`pthread_diff.py` runs each binary under 16 configurations: glibc (host 8.12 / pinned 8.9),
placement (any CPU / one CPU / two SMT siblings / two cores), and the schedule, either
unperturbed or perturbed by `perturb.so`. The shim yields, spins and migrates at random
around every pthread call and at thread start, without changing the binary. Small-bound
rebuilds ran 400 times per configuration and are compared with the exhaustive outcome sets
above. The eight pinned full-size binaries ran 30 times per configuration and are compared
with the explored sets (p3, p7, p8) or the problems' predicted sets. The full output is in
`results/pthread-diff.txt` and `results/pthread-diff.json`.

**Every observed output was in the model's outcome set**, in all 22 binaries and all 16
configurations: 89 600 small-bound runs and 3 840 full-size runs. Under both the host glibc
and the pinned glibc, each race-free program printed the same single output.

| binary | model outcome set | runs | observed |
|---|---|---|---|
| p1 (N=2, 3), p6 (N=2, 3) | `{2N}` (explored) | 6 400 each | `2N` only |
| p2 (N=2, 3) | `{N(N+1)/2}` (explored) | 6 400 each | that value only |
| p4 (K=1, 2) | `{"4 4 0"}` (explored) | 6 400 each | that only |
| p7 (R=1, 2) | `{"abab…ab 4 1"}` (explored) | 6 400 each | that only |
| p5 (N=1) | `{1, 2}` | 6 400 | `2`: 6 397, `1`: 3 |
| p5 (N=2) | `{2, 3, 4}` | 6 400 | `4`: 6 398, `2`: 2 |
| p5 (N=3) | `{2, …, 6}` | 6 400 | `6`: 6 398, `3`: 1, `4`: 1 |
| p5 (N=4) | `{2, …, 8}` | 6 400 | `8`: 6 399, `7`: 1 |
| p1, p2, p4, p6 (pinned, full size) | the predicted singleton | 480 each | the predicted output only |
| p3, p7, p8 (pinned, full size) | the explored singleton | 480 each | that output only |
| p5 (pinned, N = 100 000) | `[2, 200 000]` | 480 | 322 distinct values, from 86 178 up to 200 000 |

* The racy counter's lost updates at small bounds appeared only with the two threads on SMT
  siblings, in 8 of 25 600 runs, each with perturbation or under the pinned loader. Creating a
  thread takes longer than a loop of a few increments, so the two loops rarely overlap. Most of
  the model's outcomes (for example `2` and `5` at N=3) were never observed.
* At full size, the racy counter lost updates in every two-CPU run (median about 105 000 on
  two cores and 137 000 on SMT siblings). On one CPU it lost none in 119 of 120 runs: the
  scheduler rarely preempts inside the 100 000-iteration loop. The theoretical minimum, 2, was
  never seen.
* Perturbation never changed a race-free program's output, including p2 (condition
  variables, with spurious wake-ups possible) and p7 (semaphore ping-pong and barrier).

## Findings and harness defects

1. **No model bug**: no observed outcome contradicts x86-TSO on a TSO-covered test, XL on any
   test, the multithreaded process model on race-free programs, or the simple pthread model on
   any binary.
2. **The x86 process model is SC for racy code** (§2): it forbids SB's weak outcome, which
   this CPU shows in 0.07 % to 0.7 % of native runs. That is a known coverage gap (`Task.x86Acc`,
   `Task.drfSc`), and it now has a concrete witness.
3. **`Csl.Race` includes read/read pairs** (§3). `Simple.RaceFree` is false for three of the
   eight pthread programs, which only share read-only data.
4. **XL over-approximates** this CPU on misaligned accesses inside a cache line (never torn)
   and on `rep stosb` (never reordered). RA and the catch-fire models over-approximate it
   on IRIW, 2+2W, fenced SB and lost locked updates. These are allowances that were never
   observed. They are not errors.
5. Harness defects found and fixed while doing this:
   * `scripts/x86-litmus-hw/litmus_hw.c` pins thread `t` to CPU `2t mod 12`. On this machine
     CPU 6 is CPU 0's SMT sibling, so IRIW's threads 0 and 3 shared a core.
     `tools/litmus-hw/lattice_hw.c` takes the CPU list as an argument, and both placements
     were run.
   * An `LD_PRELOAD` wrapper of `pthread_cond_wait` that resolves the real function with
     `dlsym` gets glibc's `GLIBC_2.2.5` compatibility version, which uses another
     `pthread_cond_t` layout. The perturbed producer/consumer then hung. `perturb.c` uses
     `dlvsym(…, "GLIBC_2.3.2")` for the condition-variable functions.
6. The host glibc moved from the pinned 2.39-0ubuntu8.9 to 8.12 between the pthread pins and
   these runs. Both were run, and no difference in outputs was seen.

## Limitations

* **One CPU model.** An Intel Coffee Lake desktop part. x86 implementations differ in what
  they actually produce (for example, other microarchitectures may tear differently or reorder
  non-temporal stores differently), though not in what x86-TSO allows. AMD parts, servers with
  several sockets or NUMA nodes, and virtualised CPUs were not tested.
* **No weak-memory hardware.** Every model here is checked from below by an x86-TSO machine.
  Nothing exercises the outcomes that only RA or the catch-fire models allow (IRIW, 2+2W, …).
  Arm or POWER hardware would, but they are outside these models' x86 scope.
* **Testing, not proof.** Never observing an outcome does not show it impossible. Some
  TSO-allowed outcomes of three- and four-thread tests were never seen, and the racy counter's
  low values need schedules that perturbation reaches only at small bounds.
* **Transcriptions.** `simple_model.py` and the pthread programs are hand transcriptions,
  checked by review and by their agreement with the expected outputs. The corpus verdicts come
  from `litmus-x86`'s checker, a transcription of herd's `x86tso.cat`, not from Lean. The
  lattice verdicts are proved in Lean, but the correspondence between each hardware test and
  its Lean execution is by inspection (`Witness/Defs`).
* **Interposition.** Perturbation changes timing through the dynamic linker. It cannot reach
  inside glibc's functions or the racy counter's loop, which make no calls.
* **The full models are not executable.** The process model's `tso` memory system and the
  full pthread model (`Impl.model`) are relations without an executor. Only the SC scheduler
  and the simple model were explored.

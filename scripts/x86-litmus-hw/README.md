# x86 litmus tests on hardware

`litmus_hw.c` runs twelve litmus shapes on the host CPU and counts outcomes;
`check.py` compares the counts with the model verdicts proved in
`Silmaril.X86.MemoryModel.{Xl,Lattice}.Thms`.

```sh
cc -O2 -Wall -pthread litmus_hw.c -o litmus_hw
./litmus_hw 2000000 | python3 -I check.py
```

Each iteration resets the locations, meets at a spinning barrier (`lock xadd`),
waits a per-thread pseudo-random delay of up to 63 loop iterations, and runs
the test body: inline assembly with exactly the test's instructions. Threads
are pinned to CPUs 0, 2, 4 and 6. The outcome encodings are in `outcome()` in
`litmus_hw.c` and in the comments of `check.py`.

What the run checks:

* no outcome that x86-TSO forbids appears on a test that x86-TSO covers
  (aligned write-back accesses, locked RMWs, fences), and no outcome that XL forbids appears
  on any test;
* the separating outcomes appear: SB's weak outcome (SC ⊏ TSO), the reordered
  non-temporal store of MP+movnti and the torn cache-line-crossing 8-byte
  store (TSO ⊏ XL).

A run that never shows an outcome does not prove the outcome impossible. It shows
only that this CPU, under this harness, did not produce it.

## Recorded run

Intel Core i7-8700 (6 cores, 12 threads), Ubuntu 24.04, Linux 6.8, gcc 13.3,
2 000 000 iterations per test, 2026-11-13:

```
SB: 2000000 runs, outcomes {0: 141511, 1: 1719290, 2: 136289, 3: 2910}; separating outcome 0 seen 141511 times
SB+mfences: 2000000 runs, outcomes {1: 1749603, 2: 40960, 3: 209437}
SB+xchgs: 2000000 runs, outcomes {1: 1561318, 2: 302106, 3: 136576}
MP: 2000000 runs, outcomes {0: 279676, 1: 23668, 3: 1696656}
LB: 2000000 runs, outcomes {0: 130928, 1: 1774556, 2: 94516}
IRIW: 2000000 runs, outcomes {0: 255745, 1: 134937, 2: 36082, 3: 140436, 4: 46453, 5: 1178, 6: 65708, 7: 136024, 8: 136381, 9: 411247, 11: 46150, 12: 145004, 13: 150259, 14: 20483, 15: 273913}
2+2W: 2000000 runs, outcomes {5: 137666, 7: 1838174, 8: 24160}
MP+movnti: 2000000 runs, outcomes {0: 981779, 1: 1954, 2: 154680, 3: 861587}; separating outcome 2 seen 154680 times
MP+movnti+sfence: 2000000 runs, outcomes {0: 1409309, 1: 486686, 3: 104005}
SPLIT8: 2000000 runs, outcomes {0: 312243, 1: 1685327, 2: 2430}; separating outcome 2 seen 2430 times
INC2: 2000000 runs, outcomes {1: 105422, 2: 1894578}
LOCKINC2: 2000000 runs, outcomes {2: 2000000}
OK: every observed outcome is allowed by its model
```

Observed: SB's weak outcome (7.1 %), MP+movnti's reordering (7.7 %) and a torn
cache-line-crossing store (0.12 %), which is the tear that XL allows and the
byte-granular store-buffer machine `Tso.XFlush` (whole-span flush) forbids.
Never observed: any outcome that x86-TSO forbids on the TSO tests
(SB+mfences, SB+xchgs, MP, LB, IRIW, 2+2W, two `lock inc`), and MP+movnti+sfence's
reordering, which XL forbids. IRIW's and 2+2W's weak outcomes are allowed by
release/acquire, so those tests separate `tso ⊏ ra` in the models, but this
hardware never produced the outcomes. That is consistent with x86 being TSO.

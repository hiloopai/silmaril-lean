# C11 litmus programs

Small multithreaded C programs in litmus form, compiled to x86 and ingested into the litmus
corpus format by `tools/litmus-x86 c11` (see its README). Each directory holds one shape:

| dir | shape | condition |
|---|---|---|
| `sb` | store buffering | `r0=0 ∧ r1=0` |
| `mp` | message passing | `r0=1 ∧ r1=0` |
| `lb` | load buffering | `r0=1 ∧ r1=1` |
| `iriw` | independent reads of independent writes (4 threads) | `r0=1 ∧ r1=0 ∧ r2=1 ∧ r3=0` |
| `2+2w` | two writes per thread | final `x=1 ∧ y=1` |
| `corr` | coherence of two reads | `r0=1 ∧ r1=0` |
| `counter` | two `fetch_add(x, 1)`, one keeping the old value | final `x=1` (lost update) |
| `sb+fences` | SB with a seq_cst fence in each thread | `r0=0 ∧ r1=0` |

- `<name>.c`: thread functions `P0`, `P1`, ... over `int` globals, using the macros of
  `c11.h`. Every program is compiled in four variants (`-DMODE=0..3`): `na` plain accesses
  (racy, undefined behaviour in C11; kept to see what compilers do with them), `rlx`,
  `ra` (release stores, acquire loads, acq_rel RMWs) and `sc`. Fences are always seq_cst.
  Results go to plain globals `r0`, `r1`, ... written by one thread and read after join.
- `litmus.txt`: the specification (format in `tools/litmus-x86/src/cspec.rs`): locations,
  each thread's C-level accesses in program order, the condition, and the C11 verdict
  expected per variant. The expected verdicts are RC11's (Lahav et al., PLDI 2017) as
  recorded by hand from memory; no tool computes them. `litmus-x86 c11 cir` translation-validates
  the compiled objects into CIR with these modes (`Silmaril.X86.Concurrency.Cir.C11`).
- `obj/<variant>.<compiler>.o`: the compiled objects, pinned in `objects.sha256`.
  `toolchains.txt` pins the compilers (sha256 of the gcc driver, `cc1` and `as`, and of
  `clang-23`) and the flags `-O2 -fcf-protection=none -fno-asynchronous-unwind-tables -g0`.
  `litmus-x86 c11 compile --check` recompiles all 64 and compares bytes.

`tools/litmus-run --json tools/litmus-x86/export/c11.json` runs the compiled tests on
hardware.

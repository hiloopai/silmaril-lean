# litmus-x86

Imports a curated x86 litmus corpus into Lean. For each test the tool:

1. parses the herdtools7 `.litmus` file: the `X86` dialect (Intel-like, `MOV [x],$1`) or
   the `X86_64` dialect (AT&T, `movl $1,(x)`), the initial state, the program table and the
   final condition (`src/litmus.rs`);
2. reads each cell into a small instruction IR (`src/insn.rs`) and resolves locations to fixed
   absolute addresses and registers to the System V register file (`src/model.rs`). Locations
   start at `0x10000`, one 64-byte-aligned slot each, so no two share a cache line. herd's
   `EAX` is the low 32 bits of `rax`;
3. prints each instruction as canonical AT&T text, assembles it with GNU `as --64` (one ELF
   section per instruction) and records the bytes (`src/asm.rs`). Objects with relocations
   are rejected; memory operands are absolute 32-bit addresses;
4. on x86-TSO-covered tests, runs an exhaustive axiomatic checker for SC and x86-TSO
   (`src/checker.rs`, a transcription of herd's `x86tso.cat`). Generation fails unless the
   checker's TSO verdict equals the verdict recorded in `corpus/index.txt`. XL-only tests
   must fall outside the checker's scope;
5. writes `Silmaril/X86/MemoryModel/Litmus/Corpus/Defs.lean` (`src/emit.rs`). The data shapes
   are in `Silmaril/X86/MemoryModel/Litmus/Defs.lean`.

The crate has no dependencies (std only).

## Usage

```sh
cd tools/litmus-x86
cargo run --release -- generate   # rewrite the Lean module
cargo run --release -- --check    # regenerate in memory; fail unless byte-identical
cargo run --release -- list       # checker verdicts and execution counts, no assembling
cargo run --release -- export     # write export/corpus.json (fails unless the Lean module is fresh)
cargo run --release -- export --check  # both the Lean module and the JSON are up to date
cargo test                        # unit tests + whole-corpus verdict test (needs `as`)
```

`export` writes `export/corpus.json` for the hardware harness `tools/litmus-run`.
It contains, per test, the layout, the per-thread bytes and initial registers, the observed
registers, the witness, the recorded verdicts and, for TSO-covered tests, the checker's TSO and
SC final-state sets, projected onto the observed registers and the location bytes. The format
is documented in `src/export.rs`. The sets are the checker's, not herd7's and not Lean's.

Options: `--corpus DIR`, `--out FILE`, `--json FILE`, `--as PATH` and `--tmp DIR`. Scratch files go to
`$TMPDIR/litmus-x86-<pid>` and are removed afterwards. The generated module records the
assembler version, so `--check` is byte-identical only with the same binutils. The module
was generated with `GNU assembler (GNU Binutils for Ubuntu) 2.42`.

## C11 litmus programs (`c11`)

`examples/litmus-c` holds C litmus programs (SB, MP, LB, IRIW, 2+2W, CoRR, a fetch_add
counter, SB+fences), each compiled in four variants (`na` plain, `rlx`, `ra`, `sc`; see
`examples/litmus-c/c11.h`) by two pinned compilers. The tool ingests the thread functions
of the compiled objects into the same export format:

```sh
cargo run --release -- c11 compile            # rebuild the 64 objects (pinned compilers only)
cargo run --release -- c11 compile --check    # recompile; fail unless byte-identical
cargo run --release -- c11 ingest [--summary] # objects -> export/c11.json + export/c11-meta.json
cargo run --release -- c11 ingest --check     # both JSON files are up to date
cargo run --release -- ingest --obj F.o --spec litmus.txt --variant rlx  # one object, to stdout
```

`c11 ingest` (`src/ingest.rs`, `src/elf.rs`, `src/cspec.rs`, `src/c11.rs`) reads each ELF
relocatable object, places its data objects on the fixed data page (as for the herd corpus),
relocates thread `k`'s function to `0x400000 + 0x1000*k` (`R_X86_64_PC32`/`PLT32` against the
data objects only), disassembles it with GNU `objdump`, drops the final `ret`, lifts each
instruction into the IR of `src/insn.rs` (plus `lea`), matches every C11 access of the
specification with its x86 instruction(s), and runs the SC/TSO checker. It refuses code with
branches or calls, other relocations, memory operands other than `disp(%rip)`/`disp(%rsp)`,
registers read before they are written, and atomic accesses without an x86 counterpart in
program order. `export/c11.json` is read by `tools/litmus-run --json`; each thread has a
`code_base`, since the bytes are rip-relative. `export/c11-meta.json` is the sidecar for
`c11 cir` (`src/c11cir.rs`): per test the compiler and hashes, layout, relocations, instructions (bytes,
`objdump` text, lifted text), every C11 access with its mode, x86 instructions and form, and
the expected C11 verdict (recorded by hand from the literature, not computed); and a
per-compiler table of the x86 forms of each (access kind, mode). `ingest` needs only
`objdump`; `compile` needs the pinned compilers of `examples/litmus-c/toolchains.txt`.

## C11 objects, spawn/join and futex programs into CIR (`c11 cir`, `cir-c`, `cir-f`)

```sh
cargo run --release -- c11 cir [--check]        # Silmaril/X86/Concurrency/Cir/C11/Corpus/Defs.lean + kernel checks
cargo run --release -- cir-c compile [--check]  # spawn/join objects (pinned compilers only)
cargo run --release -- cir-c [--check]          # Silmaril/X86/Concurrency/Cir/Tv/CSpawn/Defs.lean + kernel checks
cargo run --release -- cir-f compile [--check]  # futex objects (pinned compilers only)
cargo run --release -- cir-f [--check]          # Silmaril/X86/Concurrency/Cir/Tv/CFutex/Defs.lean + kernel checks
```

`c11 cir` (`src/c11cir.rs`) proposes CIR certificates, with the C11 modes of the source, for
the objects of `export/c11.json`. `cir-c` (`src/cspawn.rs`) does the same for the spawn/join
programs of `examples/litmus-c/spawn`; `cir-f` (`src/cfutex.rs`) pairs the thread bytes of the
futex programs of `examples/litmus-c/futex` with their CIR programs for a bounded
trace-inclusion check. All three are untrusted: Lean checks everything they emit. The module
documentation of each source file describes its input and output.

## Translation validation into CIR (`cir`)

```sh
cargo run --release -- cir           # rewrite the two Lean modules below
cargo run --release -- cir --check   # regenerate in memory; fail unless byte-identical
```

`cir` (`src/cir.rs`) is the **untrusted** proposer of the x86 → CIR translation validation
(`Silmaril/X86/Concurrency/Cir/Tv`). It reads `export/corpus.json`, decodes every thread of the
60 x86-TSO-covered tests **from its bytes** (absolute `[disp32]` operands; `mov`, `xchg`,
`lock xadd`, `lock cmpxchg`, `lock add/or/and/sub/xor`, `[lock] inc/dec`, `mov r, imm`, fences;
anything else is refused), lifts each instruction to CIR statements, and writes
`Silmaril/X86/Concurrency/Cir/Tv/Corpus/Defs.lean` (one certificate per thread) and the
per-test kernel checks `Silmaril/Proofs/X86/Concurrency/Cir/TvCorpus.lean`. Lean's `tvRun`
re-decodes the bytes and checks every item; nothing the proposer emits is trusted. The test
`cir::fresh::cir_modules_up_to_date` fails if the modules are stale.

## Channel C programs with spin loops (`chan`)

```sh
cargo run --release -- chan compile [--check]   # build (or recompile and compare) the 8 objects
cargo run --release -- chan [--check]           # write (or check) the Lean module and export/chan.json
```

`src/chan.rs` compiles `examples/litmus-c/chan/{mailbox,ring}` with the pinned compilers of `c11`,
as written (`ok`) and with `-DSWAP` (the mutant), and cuts `P0`/`P1` into pieces for Lean's
`Cir.Tv.stvRun`: spin loops (`mov m, r; test|cmp; jcc` back), `nop` pads, and straight
segments lifted with the `cir` proposer. It writes `Silmaril/X86/Concurrency/Cir/Tv/Chan/Defs.lean`
and `export/chan.json` (input for `tools/litmus-run --json`). The proposer is untrusted: Lean
checks every certificate against the bytes. `chan::tests::outputs_up_to_date` checks freshness.

## Corpus (68 tests, `corpus/index.txt`)

| group | files | count | coverage |
|---|---|---|---|
| herdtools7 x86 catalogue | `corpus/herdtools7/catalogue/x86/tests/*.litmus` | 23 | tso |
| herd7 regression tests with recorded output | `corpus/herdtools7/herd/tests/instructions/X86_64/A01{1,3,4}.litmus{,.expected}` | 3 | tso |
| x86-TSO paper tests (transcribed) | `corpus/paper/*.litmus` | 24 | tso |
| hand-written, TSO-covered | `corpus/silmaril/{IRIW+mfences,SB+lock-*,RMW+*}.litmus` | 10 | tso |
| hand-written loose corners | `corpus/silmaril/{MS+halves,MIS+straddle,MP+movnti*,MP+stosb*,STOS+internal}.litmus` | 8 | xl |

Coverage `xl` means **not covered by x86-TSO; XL verdict only**.

- Required shapes and where they come from:
  - SB: catalogue `SB`, and paper `iwp2.3.a/amd4`.
  - SB+mfences: catalogue `SB+mfences`, and paper `amd5`/`amd10`.
  - SB+lock variants: paper `iwp2.8.a` (xchg), and own `SB+lock-adds`, `SB+lock-xadds`,
    `SB+lock-cmpxchgs`.
  - MP and MP+fences: catalogue `MP*`, and paper `iwp2.1/amd1`.
  - LB: catalogue `LB*`, and paper `iwp2.2/amd2`.
  - IRIW: paper `amd6` and `iwp2.7/amd7` (xchg), and own `IRIW+mfences`.
  - 2+2W: catalogue `2+2W*`, and herd `A013` (bytes) and `A014` (mixed sizes, disjoint).
  - R and S: catalogue.
  - WRC: paper `iwp2.5/amd8`, and `rwc-{unfenced,fenced}`.
  - n1–n8: paper (`n1` … `n8`).
  - RMW atomicity: herd `A011` (xchg against a store), and own `RMW+lock-xadds{,-final}`,
    `RMW+lock-cmpxchgs`, `RMW+xchgs`, `RMW+lock-inc+W`, and the unlocked contrast
    `RMW+inc+W`.
- Syntax extensions used only by the own tests: a memory operand may carry a constant
  offset (`(x+4)`), and a location may be a byte array (`uint8_t b[128];`). A register may be
  initialised to a location's address (`0:rdi=x`, as herd allows).

## Verdict provenance

The `expected` column of `corpus/index.txt` and its `basis` (copied into each test's `basis`
field):

- **herd7 recorded output** (`A011`, `A013`, `A014`): `herd/tests/instructions/X86_64/*.expected`
  at the pin below, `Observation … Never`, so the witness is forbidden.
- **x86-TSO paper**: Owens, Sarkar, Sewell, *A better x86 memory model: x86-TSO (extended
  version)*, Appendix A, which gives `Allow`, `Forbid`, `Require` or `tso : Allow/Forbid`
  for each test. The tests were transcribed by hand from the listings. Sources read:
  - <https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.pdf>, sha256
    `4c015f45bc5c8e297e7792d0c30f0347348903654850d0459f3208a1bcecec7b`, fetched 2026-10-31;
  - cross-checked against the TPHOLs 2009 version
    <https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.tphols.pdf>, sha256
    `ab396610d5365b5c726f1871bb18e0442f77fdd7bf52850cbf911cf2472fcb78`.

  The PDFs are not redistributed. `n8` is transcribed as printed (initial `0:EAX=1; [y]=1`,
  `Allow: 0:EAX=0 ∧ 1:EDX=0`). The paper's prose describes the outcome `EBX = EDX = 0`
  instead, and with `[y]=1` that outcome cannot occur. Under TSO the printed condition holds
  trivially.
- **checker**: for the 23 catalogue tests and the 10 TSO-covered own tests, herdtools7
  records no verdict at the pin: the catalogue's `shelf.py` lists tests and models but no
  results. The verdict is the tool checker's. Where a catalogue test has the same shape as a
  paper test, the basis says so, and the paper's verdict agrees.
- **XL design** (`xl` rows): stated from the XL design. It is not computed and not
  proved here. These are targets for the XL model.

herd7 itself was **not run**: no verdict here comes from a herd7 run. The checker is an
independent re-implementation. It agrees with every verdict recorded in the paper (24 tests)
and with herd's recorded outputs (3 tests). It is tested, not proved.

### Checker semantics (x86tso.cat transcription)

The checker's events are `Insn::events` (`src/insn.rs`): per instruction, the list of
`MemEvent.Event`s (`load`, `store`, `rmw`, `fence`, with address, size and `locked`) computed
from the IR. The same list is written into the Lean data, where `Corpus.events_match` proves
it equal to the events of the assembled bytes (see below). A `rmw` event becomes an R/W pair,
atomic when `locked`. Events are location-granular: every access must cover a whole location
of at most 8 bytes, otherwise the test is out of scope. It checks:

- `acyclic(po-loc ∪ rf ∪ fr ∪ co)`;
- `empty(rmw ∩ (fre; coe))`;
- `acyclic(mfence ∪ implied ∪ WW(po) ∪ RM(po) ∪ rfe ∪ fr ∪ co)`, where `implied` is the
  W→R program order with a locked access at either end.

SC is `acyclic(po ∪ rf ∪ fr ∪ co)` plus atomicity. Choices made:

- `xchg` with memory and every `lock`-prefixed RMW is a locked R/W pair.
- Unlocked `inc`/`xadd`/… is a plain R then W.
- A failing `cmpxchg` writes the old value back, which matches the SDM and `Atomic9`.
- `lfence` and `sfence` have no TSO effect, as in `x86tso.cat`.

## Generated Lean data

See the module documentation of `Silmaril/X86/MemoryModel/Litmus/Defs.lean`. Each test records:

- the name, source path and doc string;
- the locations (address, size, initial value);
- per thread, the instructions as `⟨asm text, bytes⟩` and the nonzero initial registers;
- `quant`/`cond`, plus `witness`;
- `coverage`;
- `tso` (recorded), `xl` (equal to `tso` on covered tests, by the XL design), `sc` (checker),
  and `basis`.

`Silmaril/X86/MemoryModel/Litmus/Corpus/Thms.lean` proves by kernel `decide` that every
instruction of every TSO-covered test decodes as exactly one `Atomic9` instruction. It also
proves that `movnti` and `rep stosb`, used only by the `xl` tests, are not decoded by
`Atomic9` today. `rep stosb` assumes `DF = 0`, as on System V function entry.

`Corpus.events_match` proves by `decide` that, on every test, every instruction's recorded
events (`Insn.events`, the checker's events) equal `MemEvent.atomic9Accesses` of its decoded
bytes, in the thread's initial state (all operands are absolute, so the state does not affect
the addresses); `Corpus.tso_has_events` says every instruction of a TSO-covered test records
its events. A changed byte that still decodes (a dropped `lock`, `mfence` turned into
`lfence`, another address or width) breaks the proof, so the checker's event *shapes* are the
bytes' events. The *values* the checker computes still come from the IR, not from the bytes.

## Third-party files and licence

`corpus/herdtools7/` contains files copied unmodified from <https://github.com/herd/herdtools7>
at commit `9f90176bdd6fc2ec3b34a7989c2ba011f538d821` ("Merge pull request #2093 from
herd/fix-litmus-empty-line"). The repository paths are kept below that directory:

- `catalogue/x86/tests/*.litmus` and `@all`;
- `catalogue/x86/cats/*.cat`;
- `catalogue/x86/shelf.py`;
- `herd/libdir/x86tso.cat` and `x86fences.cat`;
- `herd/tests/instructions/X86_64/A01{1,3,4}.litmus{,.expected}`.

They are distributed under **CeCILL-B** (`corpus/herdtools7/LICENSE.txt`, copied from the
same commit, sha256 `5d8a5818161ab38b77226b7caa758fde63f1aaabdf87ea773e1620b62a5b9537`).
Per-file sha256 values are in `corpus/herdtools7/SHA256SUMS`. Reproduce with:

```sh
git clone https://github.com/herd/herdtools7 && cd herdtools7
git checkout 9f90176bdd6fc2ec3b34a7989c2ba011f538d821
sha256sum catalogue/x86/tests/SB.litmus   # compare with SHA256SUMS
```

The files under `corpus/paper` and `corpus/silmaril`, and the tool itself, are under the repository licence (MIT), as
declared in `Cargo.toml`. The paper tests are transcriptions of published litmus tests,
with citation in each file's doc line.

## Not done

- The hardware harness is a separate crate, `tools/litmus-run`; this tool only
  exports its input.
- No herd7 run.
- Event extraction from the bytes is static only (per-instruction events, `events_match`);
  no execution of the bytes and no value semantics from the bytes.
- No Lean model or verdict proofs in this tool: those are in
  `Silmaril/Proofs/X86/MemoryModel/Litmus`.

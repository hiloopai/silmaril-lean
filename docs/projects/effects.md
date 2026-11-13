# Effects of x86 code: CFGs, call graphs, system-call sets

What can a function or program of an ELF file do to the outside world? This project answers
with **certificates**: a control-flow graph per function, decided over the function's bytes, and
a call graph whose reachable nodes are the calls, imports and system calls that any run can
make. One soundness theorem connects a checked certificate to every run of the most general
process around the image (any kernel, any library), on any machine that obeys the decoder's
flow law. Effects (`syscall_set`, `no_spawn`, `no_network`, `no_exec`, `foreign_calls`) are then
read off the reachable nodes.

## Layers

```
 effect shapes   syscall_set, no_spawn, no_network, no_exec, foreign_calls   (Elf.Effects.Shapes)
       ^  reachable nodes + import summaries
 call graph      Node = fn a | ext Ref | sys n | sysAny | unresolved          (Elf.Effects)
       ^  edges of every CFG's terminators (edgesOf)
 CFG             cfg_is / cfg_sub: blocks with their bytes, typed terminators (X86.Cfg)
       ^  meaning: the flow law of the machine for the decoder
 flow decoder    X64.dec: length decoder + classifier, stable by construction (X86.Flow)
```

## Module map

| Module | What |
| --- | --- |
| `Silmaril.X86.Flow.Defs` | `Kind` (where control goes), `RaxT` (the `rax` transfer), `FlowDec`, `FlowDec.Stable`, `UMach`, `Admits`, `FlowLaw` |
| `Silmaril.X86.Flow.X64.Defs` | `X64.dec`: an x86-64 length decoder and flow classifier (legacy, `0F`/`0F38`/`0F3A`, VEX, EVEX), in a reader monad the kernel can run |
| `Silmaril.X86.Flow.Str9.Defs` | `str9`: the single-threaded `Str9` machine as a `UMach`; `Task.flowLaw_str9` |
| `Silmaril.X86.Flow.Thms` | `at_unique` (one instruction per address for a stable decoder), `X64.stable`, `fetch_prefix`, decoder spot checks |
| `Silmaril.X86.Cfg.{Defs,Thms}` | `Block` (start, bytes, terminator), `Graph`, `walk` (the block decoder with the per-block `rax` dataflow), `Graph.sub` (`cfg_sub`), `Graph.exact` (`cfg_is`); `walk_cases`, `ofNat_wrap`; the `tiny` example |
| `Silmaril.Elf.Effects.Defs` | `Node`, `CallGraph`, `Reaches`, `edgesOf`, `Cert`, `Cert.check`, `Cert.union`; the process (`Cls`, `World`, `Ev`, `Step`, `Run`); `ReachIn`; the frame conditions (`CodeLoaded`, `CodeStable`, `ImageOk`, `KOk`, `LibOk`, `IndOk`, `RetOk`); `Setting`; `Summ`, `SyscallsOk`, `ForeignIn`, `spawnNrs`, `execNrs`, `netNrs` |
| `Silmaril.Elf.Effects.Thms` | `sound`, `task_sound`, `sound_str9`, `codeLoaded_of`, `reaches_mem`, `reaches_mono`, `reach_mono`, `syscalls_of_reach`, `noSpawn_of_reach`, `foreign_of_reach`, `check_union` |
| `Silmaril.Elf.Effects.Shapes.{Defs,Thms}` | the problem shapes `cfg_is`, `cfg_sub`, `callgraph_sub`, `syscall_set`, `no_spawn`, `no_network`, `no_exec`, `foreign_calls`, `prog_no_spawn`, `prog_syscall_set`; `Admissible`, `CertOk`; the shapes from a checked certificate (`*_of_cert`, `syscallSet_of_imports`, `noSpawn_of_callGraph`, `syscallSet_of_callGraph`, `syscallSet_mono`) |
| `Silmaril.Elf.Effects.Example.{Strlen,CoreutilsTrue,Sha256sum}` | generated certificates (`Defs`) and their theorems (`Thms`) |
| `tools/cfg-cert` | the Rust proposer: ELF reader, a port of `X64.dec`, CFG recovery, jump tables, GOT slots, non-returning calls, Lean output |

## The flow law and the CFG checker

A step from an instruction that `D` reads as `i` (of length `l`) must be admitted by its kind:
`seq` goes to the next instruction, `jcc r` to it or to `next + r`, `call r` to `next + r`
pushing `next`, `jmpInd`/`callInd` through `disp(%rip)` to the 8 bytes of the slot, `ret` to the
popped address; `syscall`, `int`/`sysenter` and traps have **no user step** (the kernel arm of
the process runs them). The step keeps `D.rax i` (`set n`, `keep`, or `clobber`).

`Graph.sub D` decodes each block from its own bytes: positive lengths inside the block, interior
instructions `seq`/`rep` (a `rep` must keep `rax`), the last one agreeing with the terminator
(targets modulo `2^64`), and the graph closed (the entry and every intraprocedural successor
start a block). **A direct system call** `sys nr ret` must carry the `rax` constant that the
block's own instructions establish before the `syscall` (`raxStep`, from *unknown* at the block
start); otherwise `nr = none`, the node `sysAny`. `Graph.exact` adds sorted, disjoint, maximal
and reachable blocks.

`X64.dec` returns the shortest prefix its reader consumes entirely, so it is stable by
construction (`X64.stable`): its answer depends only on the instruction's bytes, which makes the
instruction at an address unique (`at_unique`) between a machine step and a certificate block.

## Soundness

`Setting W D base P esc entry keep s₀ N` collects:

* `law : FlowLaw W.J D` and `stable : D.Stable`;
* `check : P.check D (entry :: esc) = true` (by `decide`);
* `N` holds `entry` and the escapes, is closed under `P.graph`'s edges, and does not hold
  `unresolved`;
* the frame conditions of the world: `CodeLoaded` (from `CodeAt` rows, the placement and
  `CodeStable`, `codeLoaded_of`), `ImageOk` (no import bound inside certified code), `KOk` (the
  kernel resumes after the system-call instruction), `LibOk` (library steps come back into the
  image only at a return site of a function of `N`, an escape, or not at all), `IndOk` (indirect
  transfers with listed targets land on one of them; for `got` the slot holds the import), and
  `RetOk` (a `ret` in the image lands where `LibOk` allows).

**`sound`** (proved, `Silmaril.Proofs.Elf.Effects.Sound`): `ReachIn W D base keep s₀ N`. Every
run from `s₀` enters only calls, imports, system calls and unknown steps covered by `N` (a known
system call is also covered by `sysAny`). The invariant is: `rip` is foreign, or the address of
an instruction of a block of a function of `N`, with the block's `rax` constant in `rax`.

`sound_str9` instantiates the machine with the single-threaded `Str9` (`Silmaril.X86.Str9`)
under its open flow law.

## Effects

`Node.SysOk summ ok`: a function node is fine, an import counts as its summary, `sys n` as `n`,
`sysAny` and `unresolved` fail. `syscalls_of_reach` reads `SyscallsOk` off `ReachIn`. The shapes
quantify over every admissible world; `CertOk` collects what a row proves (the check, a listed
node set closed under the edges, no `unresolved`, and the `CodeAt` rows). `syscallSet_of_imports`
gives `syscall_set` from the reachable direct system calls and the import summaries;
`noSpawn_of_callGraph` gives `no_spawn` from a call graph whose reachable nodes do not spawn.
`check_union` composes certificates (a library's with a program's).

## Examples

All three are generated by `scripts/cfg-cert/gen.sh` from pinned files (the sha256s are in the
modules and in `NOTICES/effects-examples`) and checked by `decide` (`decide +kernel` for the
large ones; `sha256sum` takes about 45 s).

| example | certificate | result |
| --- | --- | --- |
| glibc 2.39 `strlen` (`libc.so.6`, Ubuntu 2.39-0ubuntu8.9) | the IFUNC resolver `0xb4dc0` and the four implementations `0xc1a10` (SSE2), `0x18bac0` (AVX2), `0x194580` (AVX2+RTM), `0x19bc40` (EVEX): 5 functions, 87 blocks, 1497 bytes | every CFG is exact (`cfg_is`); no calls, no imports, no system calls: `sse2_syscalls : SyscallSet … [] []`, `sse2_foreign : ForeignCalls … []` |
| coreutils 9.4 `true`, from `main` (`0x1490`) | 19 functions, 155 blocks, 3202 bytes | no direct system call; the reachable imports are 17: `__cxa_atexit`, `__fprintf_chk`, `__printf_chk`, `__stack_chk_fail`, `abort`, `bindtextdomain`, `dcgettext`, `exit`, `fputc_unlocked`, `fputs_unlocked`, `fwrite`, `nl_langinfo`, `setlocale`, `strcmp`, `strncmp`, `strrchr`, `textdomain` (`foreign`); `syscalls` for any summaries of them |
| coreutils 9.4 `sha256sum`, from `main` (`0x2750`) | 72 functions, 1133 blocks, 17524 bytes, six jump tables (`.table`, under `IndOk`) | no direct system call; 54 reachable imports, among them `SHA256_Init`/`_Update`/`_Final` of `libcrypto.so.3`; `syscalls`: the system-call set is the union of the import summaries |

**`true` does not call only exit-family imports.** With one argument (`--help`, `--version`) its
`main` sets up the locale and prints usage or the version, so the honest result is the import set
above.

**`sha256sum`'s system calls through SysWrap.** Of its 54 imports, two are system-call wrappers
with a SysWrap contract in `Silmaril.Libc.SysWrap.Glibc.V239`: `close` (3, `spec_1169b0`) and
`lseek` (8, `spec_11b2a0`). The other 52 (stdio, `malloc`, `getopt_long`, `fcntl`,
`posix_fadvise`, OpenSSL's `SHA256_*`, …) need summaries from a followed call graph of the
library (planned). `syscalls` states the set for any summaries; with the SysWrap rows as
summaries for `close` and `lseek` it is `{3, 8} ∪` the others'.

## Status

Proved: the flow decoder's stability and instruction uniqueness; the block decoder lemmas; the
soundness theorem `sound` (and `Task.sound`); the derived lemmas (reachability against listed
sets, monotonicity, effects from nodes, imports, composition of certificates); the shapes from
checked certificates; the three examples' checks.

Open (named `Task`s or hypotheses):

* `Task.flowLaw_str9`: the flow law of `Str9` for `X64.dec`. Per tower layer, the plan is one
  lemma per new form (`seq` forms need only `rip = next`; branches, calls, returns and the
  `rax` whitelist need the semantics).
* `CodeStable`: the read-only segments stay loaded (W^X along the run) — a hypothesis of
  `Admissible`, to be derived from the machine's write permissions, `LibOk`, and the kernel's
  `mmap`/`mprotect` family.
* `IndOk` for `got` (RELRO with `BIND_NOW`, the relocation naming the import) and for `table`
  (read-only data): hypotheses; `RetOk` (return discipline) and `LibOk` (callbacks only into
  escapes): hypotheses of the world.
* `CodeAt` rows for the examples' blocks: hypotheses of the example theorems (the bytes are the
  generator's reads of the pinned files; the rows need the files as `Blob`s).
* The SysWrap bridge (`summ_of_syswrap`: a SysWrap contract gives the import's summary), the
  followed mode on `libc.so.6`, the MT bridge (`no_spawn` to the single-threaded process model),
  and the `.main`/`_start` program entry (`StdExe`).

## Caveats

* The semantics is the handwritten `Str9` tower, not hardware; and `X64.dec` is a classifier,
  tied to a machine only by the flow law.
* Shapes are relative to the certificate `P`: the world's frame conditions name its return sites
  and listed targets. An assumed jump table or summary is as good as the assumption.
* Signals, `longjmp`, self-modifying code and threads are out of scope (excluded by `LibOk`,
  `RetOk`, `CodeStable`; threads by `no_spawn`).
* `cfg-cert` is untrusted; Lean re-decodes every block and re-checks every edge.

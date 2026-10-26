# The LPS RISC-V model in Lean, and how it compares with `RiscV.Ext`

`Silmaril/RiscV/LPS/**` is a hand ("agentic") translation into Lean 4 of the RISC-V
instruction-set part of theorem-labs' Linux-process semantics, **LPS**
([`rocq-linux-process-semantics`](https://github.com/theorem-labs/rocq-linux-process-semantics),
commit `f1006fe8178338a499b5e5c41be83006c4edd058`, MIT licence, copied to
[`Silmaril/RiscV/LPS/LICENSE-LPS`](../Silmaril/RiscV/LPS/LICENSE-LPS)). LPS is the Rocq
process model under theorem-labs' OSS Verify proofs about compiled riscv64 OSS-Fuzz
binaries. The translation is executable and every upstream in-source check of the ported
files is re-proved by kernel `decide`. `LPS.Compare` places the model in the
`Compile.Category.Lattice` next to Silmaril's own `RiscV.Ext`, with proved
instruction-level agreement, and `LPS.DiffRun` tests the two machines against each other.

The machine translation (`tools/rocq2lean`) will be compared with this one later; the
definition-by-definition table [`RiscVLPS-correspondence.tsv`](RiscVLPS-correspondence.tsv)
is keyed by upstream file, line and name for that purpose.

## What was translated

| Upstream file (`theories/`) | Lean module | Content |
| --- | --- | --- |
| `Riscv/Prelude.v` | `LPS.Prelude` | bitvector helpers, signed/unsigned wrappers, radix-tree register map |
| `Riscv/Instr.v` | `LPS.Instr` | the RV64GC instruction syntax (immediates at encoded width) |
| `Riscv/Decode.v` | `LPS.Decode` | the 32-bit decoder (RV64IMAFD, Zicsr, Zifencei), objdump policies |
| `Riscv/DecodeC.v` | `LPS.DecodeC` | the RV64C decoder, expansion, `decodeAny`, defined-illegal parcels |
| `Riscv/Fpu.v` | `LPS.Fpu` | IEEE-754 binary32/64 with RISC-V flags, NaN rules, conversions |
| `Riscv/Sem.v` | `LPS.Sem` | core state, the first-order effect tree `Eff`, `exec`, `step` |
| `LinuxProcessSem/RiscvSemantics.v` (+ `BvBase.v`, `MemImageType.v`) | `LPS.Machine` | the user-mode step over Linux virtual memory: segments, overlay, fetch, fault classification |
| `Riscv/FpuTests.v`, the `Goal`s of `Decode.v`/`DecodeC.v`, `Checks/RiscvAlignment.v` | `LPS.Checks` | 140 kernel-checked examples |

Not translated: the syscall model, `Run.v` (the trace semantics that dispatches `ecall`),
`State.v`, the equivalence definitions and the proofs; they are outside the ISA. In the
table, 232 upstream definitions and lemmas are translated (7 of them with the rounding
kernel reused from Lean core, below) and 14 are not ported, each with a reason.

### Translation choices

* `bv n` is `BitVec n`; `bv_unsigned`/`bv_signed`/`Z_to_bv`/`bv_extract`/`bv_concat` are
  `toNat`/`toInt`/`ofInt`/`extractLsb'`/`++`. Upstream compares decoded fields as
  integers; the port compares `toNat`.
* The radix tree keeps Rocq's `positive` keys as Mathlib `PosNum`, so `get`/`set` are
  structural and register reads reduce in the kernel. Upstream's two lemmas are ported.
* `Section` variables (the loaded segments) are explicit arguments; `with_*` updaters are
  structure updates.
* A `Segment` holds `Process.Permissions` and an `Array Byte` instead of an `"rwx"` string
  and hex chunks, so fetches and loads reduce in the kernel. `Segment.ofHex` reads
  upstream's representation. The one behavioural consequence: upstream's
  "unreadable snapshot hex" reason for `MachineUnmodeled` cannot arise after `ofHex`.
* **Floating point.** `Fpu.v` (MIT) is translated, but its rounding kernel comes from the
  Rocq standard library's `SpecFloat` (LGPL-2.1) and Flocq (LGPL-3), which the repository
  does not copy (see `CompCertLessons.md`). Their role is taken by Lean core's own IEEE
  model `Float.Model.UnpackedFloat` (Apache-2.0), which has the same structure:
  `Accuracy` = `location`, `ExtendedMantissa` = `shr_record`, `shiftToTargetExponent` =
  `shr_fexp`, `divCore`/`sqrtCore` = `SFdiv_core_binary`/`SFsqrt_core_binary` (same
  exponent choices), `compare` = `SFcompare`. Lean core rounds only to nearest-even, so the
  mode-dependent choice (Flocq's `choice_mode`) and overflow result (`binary_overflow`)
  are written from IEEE 754 (`chooseMantissa`, `overflowResult`). Upstream's
  `round_aux_value` (agreement with Flocq) has no counterpart; instead all 83 FpuTests
  checks (ties under every mode, overflow per mode, tininess after rounding including the
  carry-to-normal cases, NaN canonicalisation, saturating conversions, fclass, NaN boxing)
  pass by kernel `decide`.
* Lean-only helpers: `Eff.leaf`/`EffKind` and `MachineResult.kind` (decidable shapes for
  checks), `digits2`, `signOf`, `xorSign`, `Segment.ofHex`, `hexChunksDecode`.

## The two RISC-V models compared

`RiscV.Ext` is Silmaril's local extended RV64 model (`Silmaril/RiscV/Ext/**`): RV64IM
integer subset, loads/stores, branches and jumps, `EBREAK` as a stop instruction, a 32-bit
codec, and a machine over `Process.Memory`. Silmaril also vendors a generated Sail-based
RV64IM model (`vendor/riscv-zkvm`, `RiscvZkvm.Rv64`, 49 operations) used for the clause
correspondences in `RiscV.Sail` and `RiscV.Ext.Sail`.

### Instruction coverage

| Extension | LPS | `RiscV.Ext` |
| --- | --- | --- |
| RV64I computational (LUI, AUIPC, OP-IMM, OP, \*W forms) | all | all |
| RV64I control (JAL, JALR, 6 branches) | all | all |
| RV64I loads/stores (LB…LD, LBU/LHU/LWU, SB…SD) | all | all |
| FENCE | yes (no-op; `fence.tso` and fm = 0 only, objdump policy) | no (undecodable) |
| ECALL / EBREAK | ECALL intercepted for the syscall model; EBREAK faults (SIGTRAP) | ECALL undecodable; EBREAK is the stop instruction |
| Zifencei (FENCE.I) | yes, exact word `0x0000100f` only | no |
| M (13 instructions) | all | all |
| A (LR/SC, 9 AMOs, .W/.D) | all, sequential single hart, reservation by address | no |
| F, D | all (arithmetic, FMA, sqrt, sign injection, min/max, compares, conversions, moves, fclass), flags in `fcsr` | no |
| C (RV64C) | all, including C.FLD/C.FSD/C.FLDSP/C.FSDSP and HINTs | no |
| Zicsr | CSRRW/S/C and immediate forms; only `fflags`, `frm`, `fcsr` exist | no |
| Privileged (MRET, WFI, SFENCE.VMA) | no (undecodable) | no |

### Decoding

* **Ext ⊆ LPS, proved.** `decode_of_ext_decode`: every word `Ext.decode` accepts, LPS's
  `decode` maps to the embedded instruction; `decodeAny_of_ext_decode` says the same for
  the fetch-level decoder. Ext's decoder accepts exactly the image of its encoder;
  LPS's accepts more.
* LPS follows binutils `objdump`: FENCE needs rd = rs1 = 0 and fm ∈ {0, the exact
  `fence.tso`}; FENCE.I only as `0x0000100f`; LR with rs2 ≠ 0 is rejected; `fcvt.d.w`,
  `fcvt.d.wu`, `fcvt.d.s` with rm ≠ 0 are rejected; reserved rounding modes 5/6 decode
  and are rejected at execution; `c.addi16sp` with nzimm = 0 decodes; HINTs decode.
* LPS treats the all-zero low parcel as architecturally illegal (a fault, SIGILL);
  anything else undecodable is "unmodeled". Ext calls every undecodable word "outside
  the subset".
* On 200 000 random words: 185 383 rejected by both, 9 416 accepted by both with the same
  meaning, 5 201 accepted only by LPS (F/D 3 965, Zicsr 1 118, A 118), none accepted only
  by Ext or decoded differently.

### Memory, alignment, traps, CSRs

| Aspect | LPS | `RiscV.Ext` |
| --- | --- | --- |
| Memory | ELF segments (r/w/x) as a read-only backing plus a writable overlay `Word → Option Byte` | `Process.Memory`: regions with permissions and a byte map |
| Load permission | overlay byte, else a readable segment | `read` permission and a backing byte |
| Store permission | every byte in the writable view (overlay or writable segment); the overlay creates no new mappings | `write` permission on every byte |
| Address wrap | per-byte `addr + 1` modulo 2^64 | the span must end at or below 2^64 |
| Misaligned plain load/store | performed (as qemu-user and Linux on hardware) | trap `dataMisaligned` (allowed by the ISA; Ext's choice) |
| Misaligned LR/SC/AMO | fault (SIGBUS), before the reservation check | not modelled |
| Fetch alignment | IALIGN = 16: pc must be even | IALIGN = 32: pc must be a multiple of 4 |
| Jump target ≡ 2 (mod 4) | retires (C present) | trap `targetMisaligned` on the jump, `rd` unwritten |
| Fetch | length-correct (16-bit parcels), x segments read from the image, w+x through the overlay | 4 executable bytes from current memory |
| Fault classification | `fault` (the process would die) vs `unmodeled` (the model gives up), fail-closed; no cause recorded | outcome with a cause (`fetchFault`, `dataFault`, …) |
| CSRs | `fflags`/`frm`/`fcsr`; a write to a read-only address (`csr[11:10] = 11`, e.g. `unimp`) is defined-illegal; every other CSR, including reads of `cycle`/`time`, is unmodeled | none |
| `ecall` | intercepted before decoding: a7 recorded, pc not advanced | undecodable |
| x0 | hardwired in `rget`/`rset`; a load to x0 still performs the access | the same |

## Differential testing

`LPS.Diff` runs both machines in lockstep on the same programs (code at `0x10000`, `r-x`;
64 data bytes at `0x20000`, `rw-`; random registers with pointers into the data and code),
compares x1..x31, pc and the data bytes after every retirement, and classifies the first
disagreement of each run. `LPS.DiffRun` re-runs a sample at build time with `#guard`.

| Batch | Runs | Agree to the end | Retired steps compared equal | Disagreements |
| --- | --- | --- | --- | --- |
| directed instruction-level tests | 32 | 23 | 53 | 4 misaligned access, 3 IALIGN, 2 `ebreak` |
| random valid Ext streams, 8 instructions, misaligned pointers allowed | 3000 | 955 | 10 581 | 1 425 misaligned access, 401 IALIGN, 219 `ebreak` |
| random valid Ext streams, 12 instructions, aligned | 3000 | 2 766 | 13 207 | 228 `ebreak`, 6 IALIGN |

Every disagreement has one of three root causes, and none is unexplained:

1. **Misaligned plain load/store**: Ext traps (`dataMisaligned`), LPS performs the access.
   Both are allowed by the ISA (the execution environment chooses).
2. **Jump to a target ≡ 2 (mod 4)**: Ext (no C extension, IALIGN = 32) traps on the jump;
   LPS (RV64GC, IALIGN = 16) retires and fetches there. A configuration difference.
3. **`ebreak`**: Ext reports a stop (its halt convention), LPS a fault (SIGTRAP under
   Linux). Both are traps; `Compare` observes both as `trapped`.

The directed tests cover division by zero and overflow (64- and 32-bit), `divw` operand
truncation (the case upstream records riscv-coq getting wrong), `mulh`/`mulhsu`/`mulhu`
extremes, shift amounts at and above the width, `addiw` wrap, `lui`/`auipc` sign
extension, signed and unsigned loads, misaligned loads and stores, stores to code, loads
from unmapped and partly unmapped memory, x0, branches and jumps to 2-aligned and odd
targets, `jalr` with `rd = rs1`, falling off the code, and `ebreak`.

LPS-only one-step coverage, 4 000 random words in the extensions Ext lacks: C 1 834
retired / 1 130 faulted; F/D 520 retired / 129 faulted / 155 declined (reserved rounding
mode); A 12 retired / 22 faulted (misaligned or unmapped); Zicsr 54 faulted (read-only
CSR writes) / 144 declined (unimplemented CSRs).

## The model lattice

`LPS.Compare` gives both models a common syntax `programs` (the test-case shape) and
observations (final state, or a trap or syscall with the state before it). A model that
declines is read as *every* behaviour. Three semantics result: `lpsSem`, `extSem`, and
`extLooseSem` (Ext♯), which is Ext with the misalignment choices left open.

| Statement | Fragment | Status |
| --- | --- | --- |
| Ext ⊑ Ext♯ | all programs | proved, `extSem_le_extLooseSem` |
| LPS ⊑ Ext♯ | where Ext♯ declines (C, A, F, D, Zicsr, fence, ecall; misalignment) | proved, `lps_refinesOn_extDeclines` |
| LPS and Ext decode every Ext word to the same instruction | all 32-bit words | proved, `decode_of_ext_decode` |
| LPS and Ext retire every register-only Ext instruction to the same state | RV64I + RV64M register forms, all operands | proved, `exec_embedCompute` |
| whenever Ext retires a non-memory instruction, LPS retires to an agreeing state | branches, jumps, register-only | proved, `refines_retire` |
| LPS retires every branch and jump | including where Ext traps on the target | proved, `lps_retires_jump` |
| LPS issues loads and stores at Ext's effective address, with no alignment test | loads, stores | proved, `exec_embed_load`, `exec_embed_store`, `incomparable_misaligned_load` |
| LPS ⊑ Ext♯ (and equality where Ext♯ answers) | all programs | conjectured (`CleanAgreement`); differentially tested |

So on their common syntax LPS and Ext are incomparable (misaligned accesses and 2-aligned
targets go opposite ways), both refine Ext♯, and where Ext♯ answers they are conjectured
equal. All proofs are kernel-checked: no `sorry`, no `bv_decide`, no `native_decide`.

## Open items

* Prove `CleanAgreement`: it needs a simulation between LPS's segments-plus-overlay memory
  and `Process.Memory` for the `Diff` layout, and the load-value lemma (`leBytesToWord`
  against `LoadOp.value`).
* Compare with the machine translation (`tools/rocq2lean`) using the correspondence table.
* Rocq was not installed and LPS was not compiled locally: the translation is checked
  against upstream's own in-source checks (ported), not against the Rocq build.
* Extend the differential test to the generated Sail model (`RiscvZkvm`) for RV64IM, and
  to LPS's floating point against Berkeley SoftFloat or Sail (upstream tests it against
  Sail).

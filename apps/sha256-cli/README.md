# Retained SHA-256 CLI targets

The historical `build.sh` / `manifest.json` target is the GCC 13.3.0 `-O2`
freestanding Linux filter transcribed in
`Silmaril/Process/CLI/Sha256Cli/Binary.lean`. It is unchanged.

The new named variants compile the **driver** at normal `-O3`, retaining the
same Clang 18.1.3 `-O2` compression assembly generated from
`Silmaril/Crypto/X86/Sha256O2/Image.lean`. Neither variant recompiles the
compression function at `-O3`, nor has either new executable been transcribed
or proved correct. No scalar-only/vectorizer-disabling flags are substituted.

| Variant | Driver compiler | Linker | ELF bytes | ELF SHA-256 |
| --- | --- | --- | ---: | --- |
| `gcc-o3` | GCC 13.3.0, Ubuntu package `13.3.0-6ubuntu2~24.04.1` | GNU ld 2.42 | 9,656 | `05fd7f70f202353177c364563519e0a540adeba2581dc58016e95ccd4feb3f13` |
| `clang-o3` | Apple Clang 21.0.0, `clang-2100.1.1.101`, target `x86_64-linux-gnu` | Rust-bundled LLD 20.1.5 | 2,800 | `c8a90ab96318b415eb7649eedaee8be543799dd8f47bdb0f8f93780478f5bb60` |

`variants/*/manifest.json` records exact executed argument arrays, compiler
and linker versions/executable hashes, GCC's external `cc1`/assembler hashes,
source hashes, preprocessed source, object hashes, architecture, artifact
hash/size, build time and named model-source fingerprints. Commands run in
an isolated temporary directory containing `src/`; generated paths in the
generator command are the recorded temporary paths. The model fingerprints
are an explicitly named snapshot, not an import closure or checked proof
binding. Lossless full ELF/object bytes are retained as reviewable hex.
Compiler dynamic libraries, resource-directory closure and host kernels are
not archived, so the recorded toolchains must be supplied to reproduce them.

## Reproduction

On Linux x86-64 with the recorded GCC/binutils:

```sh
python3 apps/sha256-cli/build_variants.py build \
  --family gcc --cc gcc --out /tmp/sha-gcc-o3
python3 apps/sha256-cli/test/variants.py /tmp/sha-gcc-o3 \
  --output /tmp/sha-gcc-o3/runtime.json
```

For Clang, pass the compiler, target, and a GNU-compatible ELF linker. The
retained build used the macOS compiler and Rust 1.88.0's bundled `rust-lld`:

```sh
python3 apps/sha256-cli/build_variants.py build --family clang --cc clang \
  --target x86_64-linux-gnu --linker /path/to/rust-lld \
  --linker-arg=-flavor --linker-arg=gnu --out /tmp/sha-clang-o3
```

Verification is portable; execution requires Linux x86-64:

```sh
python3 apps/sha256-cli/build_variants.py verify \
  apps/sha256-cli/variants/clang-o3 --materialize /tmp/sha-clang
python3 apps/sha256-cli/test/variants.py apps/sha256-cli/variants/clang-o3
```

Output directories and materialized binaries must be fresh. The builder
rejects a mislabeled compiler (in particular, macOS `/usr/bin/gcc` is Clang),
a non-x86-64 target, and compression-assembly drift. Verification rejects
changed artifact/object/preprocessed bytes, source/producer hashes or model snapshots.
It does not execute a compiler or grant proof status.

Both variants passed 24 native runtime/control checks on Linux x86-64:
empty/`abc`, 14 deterministic lengths including padding boundaries and 1 MiB,
a producer-chunked input pipe, read `EBADF`, write `ENOSPC`, an executed
wrong-hex-table mutant, and rejected artifact/source/producer/model hash mutations. Each
success checks exit 0, exactly 64 lowercase digest bytes plus newline, and
empty stderr. Producer chunk sizes do not prove an observed syscall schedule;
arbitrary short reads/writes and late errors remain formal proof obligations.
Each variant was rebuilt with identical ELF and object hashes. Exact single-run
times are in the manifests/runtime reports; no solver or generated Lean proof
was used (zero new Lean certificate bytes). These are compiled-byte/runtime
observations, not source-equivalence, graph, decoded-byte, prefix-safety or
completed-result theorems. Totality/crash-freedom is optional and unproved.

The driver uses fixed global buffers and no heap allocation or `brk`. This
avoids a heap/OOM premise for this target, while loader permissions,
code/data/stack separation, adequate mapped stack, compiler instructions,
compression ABI framing and syscall behavior still need the machine proof.
Unknown/unsupported instructions are residual obligations; they are never
treated as hardware crashes by this tooling.

## `sha256sum-min` provenance boundary

The different research executable `sha256sum-min` is pinned at SHA-256
`22fa6345cc5bed08f07d4d5a0836885118259a73402470e4d7f7a7a81ad42817`
(35,512 bytes) by `Silmaril/Apps/Sha256sum/Binary/{Compress,Image,Layout}.lean`.
`scripts/sha256sum/regen-binary.sh` checks that identity before regeneration.
The original recipe, C/ASM, generated tables, input files, manifest and exact
ELF were subsequently found at
`/home/jad/recovered-originals-20261023/campaigns/research/sha256sum` on the
research host. The earlier bounded search had not inspected that directory.
Exact original sources and recipe are now retained under
[`apps/sha256sum-min`](../sha256sum-min/README.md); every recorded input hash
matches the historical manifest. A new offline reproduction, run entirely
from existing host-local recovered inputs without source upload, rebuilt both
original executable hashes exactly. Current compiler/component executable
hashes are recorded as new observations; original compiler executable hashes
were not present in the historical receipt. See the
[`recovery evidence`](../../scripts/sha256sum/recovered-provenance.json) for
commands, checks and limits. This source recovery adds no binary correctness
theorem. The smaller CLI above remains an independent target.

Follow-up: [SHA track #3029](https://github.com/hiloopai/silmaril/issues/3029),
[contract slice #3035](https://github.com/hiloopai/silmaril/pull/3035), and
[actual driver slice #3059](https://github.com/hiloopai/silmaril/pull/3059).
The latter proves a complete empty-input successful execution of the original
transcribed O2 filter, through the explicit compression dependency
[#3040](https://github.com/hiloopai/silmaril/pull/3040). Neither new O3 variant
inherits that proof. Full CI/replay belongs to CI; no local replay was run.

## Driver proof handoff

`Silmaril/Process/CLI/Sha256.lean` now exposes `completed`, `prefixes` and
`partialCorrect` independently. The last is exactly the conjunction of the
first two at `Agrees`; `strict` implies it. Nonzero exits need no explanation
in the partial contract. Successful exit still requires complete input,
explicit EOF and exactly `CLI.Sha256.expected`, including its newline.
The binary's `completedGoal`, `prefixGoal` and `partialGoal` remain targets.
`Apps.Sha256sum.Plan` similarly separates completion/safety from `FullGoal`'s
optional progress, while retaining the idealized allocator boundary.

`Sha256Cli/Driver.lean` proves 64-byte stream accounting and compression-fold
preservation, positive read counts, padding zero count, normalization of the
canonical padded-block fold to the existing `SHA256.hash`, the lowercase hex
table, and digest-output invariants under every accepted write split and error.
It rejects incomplete answers, including a missing newline. `Spec.step_at_of_frame`
reuses memory framing to retain checked instruction fetch after data/stack
writes. These helpers have explicit premises; they do not prove the C stores,
registers or CFG establish those premises. A refused read can consume input
and clobber memory in the syscall model; the C driver exits immediately rather
than reusing that buffer. Failure after output retains the separate prefix goal.

Targeted ordinary Lean checks passed without warnings:

```sh
lake build Silmaril.Process.CLI.Sha256 \
  Silmaril.Process.CLI.Sha256Cli.Driver \
  Silmaril.Process.CLI.Sha256Cli.Spec Silmaril.Apps.Sha256sum.Plan
lake env lean scripts/sha256sum/DriverControls.lean
```

The controls include arbitrary write splits, exact completion, missing newline,
missing EOF, empty-read EOF, a failed run admitted by completion alone but
rejected by prefix safety, and stream/compression boundaries. Exact source
hashes, Lean version, observed checking times, `.olean`/source sizes, automatic
versus assisted stages and residuals are retained in
`scripts/sha256sum/driver-validation.json`. Checking times combine elaboration
and ordinary kernel checking; separate replay time and total agent cost are
unmeasured. All pending machine obligations stay outside the certified imports;
no unfinished lemma, admitted proof or new axiom was added.

## Actual empty-input execution

`Sha256Cli.Empty.successful_exit` now constructs, from the concrete initialized
loaded image, an actual `Proc.Runs` witness with events
`[read(0, []), write(1, expected []), exit(0)]`, a real exited stop, and
`Sha256.Success`. No complete execution, hash cut point, or output bytes are
assumed. The proof executes the real entry CALL and initialization stores,
requests 64 input bytes and receives genuine EOF, writes the complete padded
block, establishes every compression ABI/backing/disjointness premise,
consumes the existing compression execution theorem, executes all 32 hex
iterations, stores the newline, and chooses an admitted full write and exit.
Code/table preservation follows from explicit stack, H, block and output
frames. The final answer is exactly the existing digest specification.

This is an existential execution in the checked x86/Linux model, including
loader initialization. It does **not** prove `completedGoal`, `prefixGoal`,
`partialGoal`, source-to-binary compiler correctness, or actual Linux/hardware
realization. In particular, existence of a successful answer supplies no
universal prefix guarantee. The input/environment and full-transfer choices
are explicit; no driver totality or no-crash premise is required.

`EmptyUniversal.completed` now proves the independent universal result: for
**every** finite `Proc.Runs` execution from that concrete loaded empty-input
launch, a real exit-0 stop implies `Sha256.Success`. `exact_stdout` and
`successful_length` give exactly the canonical empty digest/newline and 65
accepted bytes. The theorem quantifies every admitted syscall response and
arbitrary R11 resume; it does not select a full write or assume termination.
Actual zero/error returns take exit1, while positive short writes traverse
the checked offset/add/compare/retry instructions. Errors on the first read
may clobber the entire input buffer, but preserve code and cannot later exit0.

This universal theorem is about the stated inhabited fixed launch. The
global `completedGoal` over every loader/environment state, nonempty inputs,
independent prefix safety, and hardware/Linux realization remain separate.
`EmptyReduction` reuses #3052's exact silent completed-observation transport;
`OutputUniversal.completed` is reusable for any canonical digest buffer and
input/output ledger, with every output transfer choice retained.

`ShortUniversal.completed` extends this result to **every message of length
0 through 55**, from its concrete initialized launch. It retains all read
chunking, EOF/error choices and arbitrary R11 values. The actual first read,
repeated-read counter/pointer instructions and copied-memory prefix establish
the input ledger; actual padding, full bit-length stores and the prepared
compression CALL/reference bridge establish the hash. The generic actual hex
loop and universal output loop give exactly `Sha256.expected message` on
exit0. No global termination or coverage premise is added.

`ShortWitness.successful_ab` independently constructs a whole initialized
nonempty execution: `read [a]`, `read [b]`, genuine positive-request EOF,
canonical digest/newline write, exit0. It executes the real startup, stores,
branches, compression CALL/body/RET and output path, with different R11 values
on the reads. Nothing installs a precomputed padded block or answer. Separate
55-byte padding-to-exit and zero/error/truncation controls remain checked.

The short-input extension is [draft #3092](https://github.com/hiloopai/silmaril/pull/3092),
stacked on #3059. Exact source/proof hashes, sizes, timings and controls are in
`short-universal-validation.json`, `short-read-loop-validation.json` and
`short-witness-validation.json`. The bounded checker accepts explicit targets
and controls for these modules. Inputs56+, other loader states, optional
prefix safety and actual OS/hardware realization remain further obligations.

Reusable local premises include `ReadPrefix.launch_read`,
`Padding.empty_block`, `CompressionEntry.empty_call`, `HexLoop.loop_to`
(arbitrary 32-byte digest state), `OutputSetup.setup`, and
`Output.answer_from_cutpoint`. `PaddingStream.after_message` additionally
executes the actual zero-fill loop while preserving any supplied message and
its 0x80 byte, for message lengths below 55; the supplied-prefix/read binding
is a separate obligation. `PaddingShort.single_block_prefix` supplies the
real pad-byte store and handles the distinct 55-byte branch as well.
`ReadPadding.single_block` prepends the actual streaming read's genuine EOF
path for every supplied message of length 0 through 55, preserving total/RSP
and reaching length setup with the exact first 56 padded bytes. Earlier
read/copy/count accounting and length-field serialization remain explicit
premises. `OutputTransfer.successful_ledger` binds every admitted successful
write at the actual syscall site to the exact canonical suffix and the
existing output invariant, including zero and short writes;
`error_ledger` covers every admitted write-error profile without changing
accepted bytes or memory. The actual loop's counter/branch refinement is
still separate. These are suitable inputs to #3047's existing
institutional adapter, not a new institution or an assumed `Agrees` theorem.

Ordinary targeted Lean builds and positive/mutation controls passed. Exact
per-stage costs, source/artifact fingerprints and residuals are in
`scripts/sha256sum/*-validation.json`; the combined empty-driver receipt is
`empty-driver-validation.json`. The dependency is pinned to #3040 commit
`aa4a173c2c9ad83c56062ae8200ecb14d1824b79`, materialized only in a private
local validation directory. Its patch is neither copied into this branch nor
merged. The draft remains explicitly dependent on #3035 and #3040.
[`check_empty.py`](../../scripts/sha256sum/README-empty-check.md) prepares a
fresh private source closure and optionally repeats only targeted ordinary
Lean checks using supplied public dependency artifacts. It performs no
dependency fetch, feature merge, repository build or replay.

Next establish arbitrary streaming read/copy/count and padding-branch
invariants, and actual short-write/error-loop refinement. The full Linux
heap/refusal/loader claims for the separate `sha256sum-min` target retain their
known bounds and disjointness residuals; this fixed-buffer target uses no heap.
New O3 variants still need complete transcription and image binding. No
follow-up merge is authorized.

For a concrete next checkpoint, `ReadPadding.lengthCore` is at `0x400211`
with RAX=56 and the original RBX total/RSP retained. Bind RBX's modular total
to accepted input, then prove the actual SHL/BSWAP/length store before the
compression CALL. The earlier read loop's R8 fill and memory copy/count
invariant, the 56–63-byte two-block path, and the output loop's accepted-count
branches remain independent obligations. Existing `StreamInv`/`fold_paddedBlocks`
and the compression owner's general reference bridge should supply the hash
reasoning through explicit dependencies.

CI integration status is recorded in `scripts/sha256sum/integration-ci-status.json`.
Runs for merged #3043 and prior #3035 completed their ordinary builds, then
were cancelled during full replay without a Lean compiler failure. The
replacement main run [39997739942](https://github.com/hiloopai/silmaril/actions/runs/39997739942)
at `5d172e7ce` passed, including its Lean job (completed 2026-10-24 00:21 UTC).
#3059 remains draft with #3035/#3040/#3052 dependencies explicit; main's
successful CI does not validate those unmerged feature sources.

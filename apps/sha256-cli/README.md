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

## `sha256sum-min`

The separate `sha256sum-min` executable (35,512 bytes, SHA-256
`22fa6345cc5bed08f07d4d5a0836885118259a73402470e4d7f7a7a81ad42817`) is
transcribed in `Silmaril/Apps/Sha256sum/Binary/{Compress,Image,Layout}.lean`.
`scripts/sha256sum/regen-binary.sh` checks that identity before regeneration.
Its sources and build recipe are in [`apps/sha256sum-min`](../sha256sum-min/README.md);
build receipts are in
[`recovered-provenance.json`](../../scripts/sha256sum/recovered-provenance.json).

## Proofs about the `-O2` filter

The `-O2` filter transcribed in `Silmaril/Process/CLI/Sha256Cli/Binary.lean`
is proved end to end in the LPS process model:
`Silmaril.Process.LPS.Problems.Sha256Cli.sha256cli_lps_total`, restated as
`Silmaril.Process.sha256Cli_total`. On every standard input, every run that
exits 0 has written exactly the lowercase SHA-256 digest of the input followed
by a newline. The proof is split into the read loop, tail, output and launch
bridge segments in `Silmaril/Process/LPS/Problems/Sha256Cli/`.

`Silmaril/Process/CLI/Sha256.lean` states the contract (`completed`,
`prefixes`, `partialCorrect`). The modules under
`Silmaril/Process/CLI/Sha256Cli/` prove the machine-level pieces: stream
accounting, padding, the compression call, the hex loop and the output loop
under every admitted write split and error.

## Scope

- The `-O3` variants above are built and run, not transcribed or proved.
- Compiler correctness and realization on actual Linux/hardware are outside
  the model.

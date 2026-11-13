# Staged ELF parsing on a multi-megabyte executable

A benchmark and worked example for `Silmaril.Elf.Staged` (`docs/projects/elf.md`, section
"Staged parsing"). `run.sh` fetches the subject, checks its digest, runs every stage natively,
emits a Lean module with kernel-checked stage certificates and times them one stage at a time.

```sh
benchmarks/elf-staged/run.sh            # everything (~3 minutes after the library is built)
benchmarks/elf-staged/run.sh --native   # only the native (fast-mode) part
benchmarks/elf-staged/gen-example.sh    # regenerate Silmaril/Elf/Staged/Example/Thms.lean
```

Outputs go to `build/elf-staged/` (git-ignored): `native.txt`, `kernel.txt`, the emitted
`Bench.lean` and the per-stage files under `split/`.

## Subject and provenance

ripgrep 14.1.1, the upstream `x86_64-unknown-linux-musl` release binary: a stripped,
**static-pie** x86-64 executable of 6,597,984 bytes with no interpreter and no needed
libraries. It is not committed; `run.sh` downloads

    https://github.com/BurntSushi/ripgrep/releases/download/14.1.1/ripgrep-14.1.1-x86_64-unknown-linux-musl.tar.gz

checks the tarball against the SHA-256 upstream publishes beside it
(`4cf9f274…ae4d8e`), extracts `rg` and checks it against `SHA256SUMS`. The digest pins the
bytes, so every number and theorem below is about exactly this file. To rebuild it from source
instead, use upstream's release workflow at tag `14.1.1` (`cargo build --release --target
x86_64-unknown-linux-musl` with the toolchain of `.github/workflows/release.yml`); that build
is not bit-for-bit reproducible across toolchains, which is why the pin is the release asset.

Shape (`elf-staged layout`): 7 program headers, 27 sections, a 4.0 MiB `.text`
(981,080 instructions) and a 506 KiB `.rela.dyn` (21,594 `R_X86_64_RELATIVE` entries).

## Disassemblers

`boundaries-objdump.sh` (GNU objdump's linear sweep) and `iced-boundaries/` (iced-x86 1.21,
an independent decoder; `Cargo.lock` pins it) each print the instruction boundaries of
`.text` as `offset length` lines. On this file they agree on all 981,080 boundaries. Both are
untrusted: they only propose tiles; the tiles are checked against the file (`tilesOk`) and,
per tile, against Silmaril's own x86 model (`Silmaril.X86.Ext.decode`).

## Measurements

One run on a 2-vCPU sandbox (x86-64, Lean `nightly-2026-11-05`); `run.sh` prints its own.

Fast mode (compiled reader on a `ByteArray`, `fastRead`; trusted computation):

| stage | time |
|---|---|
| stage 1 layout (header, 7 phdrs, 27 shdrs, names) | 0.17 ms |
| stage 2 all section bodies (21,594 RELA entries) | 9.6 ms |
| whole-file specification `Silmaril.Elf.read` | 12.2 ms |
| existing checker `Check.file` on the parse | 9.5 ms |
| stage 3: `.rela.dyn` as 22 windows of 1,024 | 8.3 ms |
| 981,080 `.text` tiles: bounds (`tilesOk`) | 52 ms |
| 981,080 tiles through `Silmaril.X86.Ext.decode` | 2.55 s (896,390 accepted, 91.3 %) |

Paranoid mode (`decide +kernel` on the 1,611 page literals; each stage in its own file, the
time is `lake env lean` of that file; the shared prefix (imports, the 6.6 MB `include_bytes`,
the layout literal) costs about 7 s of each):

| stage | wall time | over prefix |
|---|---|---|
| prefix only | ≈ 6.9 s | — |
| stage 1 `layout` | ≈ 9.1 s | ≈ 2.2 s |
| `bounds` | ≈ 6.7 s | ≈ 0 |
| stage 2' `loader` | ≈ 7.2 s | ≈ 0.2 s |
| stage 3 one RELA window of 1,024 (separate run) | ≈ 8.7 s | ≈ 1.8 s |
| stage 3 all 22 RELA windows (the whole table) | ≈ 49 s | ≈ 42 s |
| 1,024 tiles from the entry point, bounds | ≈ 7.9 s | ≈ 1.0 s |
| first 98 of them through the x86 decoder | ≈ 7.5 s | ≈ 0.6 s |

The monolithic alternative, one `decide +kernel` on `Parses F A` with the whole AST `A` as a
literal, did not get as far as the kernel: elaborating the 2.5 MB literal for `A` hit
`maxRecDepth` (at 100,000) after 11 minutes. Windows keep each statement small.

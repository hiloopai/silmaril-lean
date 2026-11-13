# WASI 0.3 command components in Rust

Three small `wasi:cli@0.3.0` command components, written in Rust and compiled with a pinned
toolchain, as inputs for reasoning about Rust programs compiled to the WASI 0.3 component target.
The Lean side, the decode certificates and the theorem statements are described in
[tools/wasm-tools/README.md](../../tools/wasm-tools/README.md).

| crate | does | export | imports (all `@0.3.0`) |
|---|---|---|---|
| `hello` | writes `Hello, WASI 0.3!\n` to stdout through a `stream<u8>` | `wasi:cli/run.run: async func() -> result` | `cli/types`, `cli/stdin`, `cli/stdout` |
| `echo` | writes its arguments after the program name, joined by spaces, then `\n` | same | `cli/environment` and the above |
| `cat` | copies stdin to stdout through the guest, at most 4096 bytes per `stream.read` | same | `cli/types`, `cli/stdin`, `cli/stdout` |
| `p3rt` | the `no_std` runtime: `dlmalloc` global allocator, trapping panic handler, `cabi_realloc` | — | — |

`run` is an **async export** (`canon lift … async (callback …)`): every component uses the
component-model async ABI (`task.return`, `waitable-set.*`, `stream.*`, `future.*`,
`context.get/set`). `hello` imports `wasi:cli/stdin` although it never reads: wit-bindgen's
`wit_stream::new` for `u8` is the stream type of `stdin.read-via-stream`.

## Committed binaries (`dist/`)

| file | build | size | SHA-256 |
|---|---|---|---|
| `hello.wasm` | release | 42914 | `7e63f5692593514594ac742530f848d2ced1df94639e501cca9d09a44e4a39f2` |
| `echo.wasm` | release | 45906 | `86e1b4d49af1c3cd798754a1282a9e05491ec42825f9785a21bcc14d86d72c72` |
| `cat.wasm` | release | 47930 | `a86ce3eee5faba14b27a1912842768e9acdc2860b7d57badefea145a16d99bd7` |
| `cat-debug.wasm` | debug (DWARF) | 3140228 | `7a8401014533176715777004b61ff1c340db67a131703a6738ff1e0119f91b6c` |

`dist/SHA256SUMS` holds the same digests. Two builds in different target directories gave
byte-identical files; `build.sh` remaps the checkout, `CARGO_HOME` and `RUSTUP_HOME` paths so the
debug info does not depend on where the repository lives.

## Why `wasm32-wasip2` and `no_std`

Rust 1.99.1 has no prebuilt standard library for a WASI 0.3 target: its channel manifest lists
`rust-std` for `wasm32-wasip1`, `wasm32-wasip1-threads` and `wasm32-wasip2` only
(`wasm32-wasip3` is a tier 3 target, which would need a nightly toolchain and `-Zbuild-std`).
The path documented by the `wasip3` crate is the `wasm32-wasip2` target, whose linker
`wasm-component-ld` (0.5.27, shipped with rustc 1.99.1) turns the core module into a component
from the component-type sections that `wit-bindgen` (0.62.0, through `wasip3`
0.9.0+wasi-0.3.0) embeds. Those sections carry the p3 imports and the async lift.

With `std`, the result is **not** a pure WASI 0.3 component: `std` links wasi-libc, whose
startup and stdio import 14 `wasi:*@0.2.12` interfaces (`wasi:io/streams`, `wasi:cli/exit`,
`terminal-*`, …) next to the p3 ones (observed on a first `std` build of `cat`: 100 KB, world
with both versions). The crates here are therefore `#![no_std]` with `alloc`. No wasi-libc symbol
is linked, so the world contains `@0.3.0` interfaces only, and `p3rt` supplies what libc would
otherwise provide: the allocator, the panic handler and `cabi_realloc`. wit-bindgen links its
own `cabi_realloc` only on `wasm32-wasip1` and `wasm32-unknown-unknown`.

## Pins and provenance

All tools are under `~/.cache/silmaril-tools` (nothing system-wide), at versions at least two weeks
old on 2026-11-09:

| tool | version | release date | SHA-256 |
|---|---|---|---|
| `rustup-init` | 1.29.2 | 2026-10-21 | `5be191e8c70a5007074254cb74d78dbfdd25cd5a61c27de7b8e5410122ec24f4` (matches the published `.sha256`) |
| Rust | 1.99.1 (`58cf8f9c3 2026-10-13`) | manifest 2026-10-15 | `channel-rust-1.99.1.toml` `fb152be80975c194aa5fc684b2aec3a6e14e2b855efe2faa4e5f8ae6e590f463`; rustup checks every component's hash against it: `rustc` `2ff05ff9…091f`, `cargo` `53f35219…bd8a`, `rust-std` x86_64 `109b0742…d958`, `rust-std` wasm32-wasip2 `15d54cff…b4f3` (`.tar.xz`) |
| wasm-tools | 1.262.0 | (already pinned in the repository) | `fe6a056dc03269b06f53e0cff926101c17d4f4ea37fbaa077d049c0d18acb211` |
| wasmtime | 50.0.0 (`ebe5e8df1 2026-10-20`) | (already pinned) | `f95e5beba6d176b447c2939607bae968ea47f87b156ddf559762f1bb3c00e9b7` |

Crates (exact versions in `Cargo.lock`, which also holds each crate's SHA-256): `wasip3`
0.9.0+wasi-0.3.0 (2026-09-10; 0.10.0 was 13 days old and excluded), `wit-bindgen` 0.62.0,
`dlmalloc` 0.2.14, `futures` 0.3.34, and for the proc macros `syn` 3.0.9 (3.0.10 was released
on 2026-11-09 and is excluded with `cargo update -p syn --precise 3.0.9`), `proc-macro2`
1.0.107, `quote` 1.0.47, `unicode-ident` 1.0.27. Building runs the crates' build scripts and
proc macros (Cargo has no way to avoid that); the crates come from crates.io with the
checksums in `Cargo.lock`.

## Licences

The example sources are Silmaril's (Apache-2.0 WITH LLVM-exception). The binaries in `dist/` also
contain code of Rust's `core`, `alloc` and `compiler_builtins` (MIT OR Apache-2.0), `dlmalloc`
(MIT/Apache-2.0), `futures-*` (MIT OR Apache-2.0), `wasip3` and `wit-bindgen`
(Apache-2.0 WITH LLVM-exception OR Apache-2.0 OR MIT). `licenses/` has the licence texts as
shipped in the `wasip3` crate: Apache-2.0, Apache-2.0 WITH LLVM-exception and MIT, with
`licenses/SHA256SUMS`.

## Scripts

```sh
examples/wasip3-rust/toolchain.sh install   # rustup-init 1.29.2 -> ~/.cache/silmaril-tools/rust-1.99.1
examples/wasip3-rust/build.sh               # rebuild, compare with dist/SHA256SUMS
examples/wasip3-rust/build.sh --update      # rebuild and refresh dist/
examples/wasip3-rust/test.sh                # validate (wasm-tools), check worlds, run (wasmtime)
```

`test.sh` and `build.sh` print `SKIP` when a pinned tool is absent.

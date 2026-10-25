# Development environments

Use Nix or a development container for Lean, a native C compiler, GNU Make,
Python and Node. Both read the Lean version from `lean-toolchain`. Lean library
dependencies remain pinned by Lake.

## Nix shell

Install Nix with flakes enabled, then run from the repository root:

```sh
nix develop
lake --version
make help
```

`flake.lock` pins the tool packages. Elan downloads the repository's Lean
toolchain on first use and keeps it in its usual per-user cache. The shell is
available for x86-64 and ARM64 Linux and macOS. Native macOS linking targets
macOS 15 to match the pinned Lean distribution's static libraries.

For upstream Binaryen and Wasmtime as independent comparison tools:

```sh
nix develop .#cross-test
sh .devcontainer/smoke-test.sh --cross-test
```

The Nix reference-tool versions come from the pinned Nixpkgs revision. Check
`wasm-opt --version` and `wasmtime --version` when comparing results; published
benchmark receipts name their own exact versions.

## Development container

Install Docker and the VS Code Dev Containers extension, then select **Reopen in
Container**. The default configuration includes Lean, Python 3, Node 24 and the
native build tools. The Lean VS Code extension is included. Dependencies and build
artifacts are downloaded or built inside the workspace when you request them.

Select the **Silmaril with cross-testing tools** configuration to add Binaryen
133 and Wasmtime 37.0.3. These upstream executables are reference tools;
Silmaril's executables are produced separately in `build/bin/`.

The image supports ARM64 and x86-64 Linux. Its base image is pinned by digest;
Node, Elan, Binaryen and Wasmtime release downloads are checked by SHA256. Ubuntu
packages receive the updates available when the image is built, so the complete
image is not a byte-for-byte reproducible artifact.

Build and check the same image without VS Code:

```sh
docker build -f .devcontainer/Dockerfile --target cross-test -t silmaril-dev .
docker run --rm -v "$PWD:/workspaces/silmaril:ro" silmaril-dev \
  sh .devcontainer/smoke-test.sh --cross-test
```

The smoke check interprets and natively compiles a Lean program, compiles and runs
a small C program, checks Python and Node, and assembles and executes a small Wasm
module with the optional reference tools. It checks the environment; the [Wasm project guide](projects/wasm.md)
describes the toolkit's own build and release tests. The development-environments
CI workflow runs this check on Linux for both the container and Nix shell.

## Why Python and Node?

- **Python 3.11+** orchestrates subprocesses, temporary files, fixture discovery
  and JSON reports using the standard library.
- **Node 24+** independently validates and runs WebAssembly produced by the tools.
- **Lean and Lake** compile the library and executables. GNU Make stages the
  tools in `build/bin/` and provides short project commands.

Shared test libraries can grow alongside the other tool families.

## S3-compatible build cache

`make cache` fetches public Mathlib artifacts, then checks the optional Silmaril
S3 cache. A normal clone needs no credentials. When a cache is configured, Lake
restores outputs whose input hashes match the current build.

The cache uses Lake's native `.art` files and revision mapping files, including
all included library modules, correctness theorem roots, seven public tools and
the test-only shell helper. The namespace separates this repository, native
platform, Lean version, dependency pins and Lake configuration. A latest-main
pointer also supports shallow clones and branches with a rewritten root commit.
These are trusted build artifacts; `make check` still runs its native tests.

To fetch from an authorized private cache, configure:

```sh
export SILMARIL_CACHE_ENDPOINT=https://your-s3-endpoint
export SILMARIL_CACHE_BUCKET=your-bucket
export SILMARIL_CACHE_PREFIX=silmaril-lean/v1
export SILMARIL_CACHE_REGION=auto  # use the bucket's region for AWS S3
export SILMARIL_CACHE_READ_KEY='access-id:secret'
make cache
```

`SILMARIL_CACHE_PUBLIC_URL` can instead name an anonymous read endpoint for the
bucket; the same release prefix is appended. No key is needed in that case.
A missing configuration or mapping leaves Lake to build from source.

CI restores before builds and uploads after the native release checks pass on
`main`. The writer key, `SILMARIL_CACHE_KEY`, belongs to the GitHub environment
`artifact-cache-publish`, whose deployment policy permits only `main`. Pull
requests use `artifact-cache-read` and can use a separately provisioned
**read-only** `SILMARIL_CACHE_READ_KEY`; fork jobs receive no secrets. Endpoint,
bucket, prefix, region and optional public URL are repository variables with the
same names. Cache network failures are reported without failing the proof/test job.

The helper uses Python's standard library, curl's S3 SigV4 support and the pinned
Lake executable. It does not copy an entire `.lake` directory or install a new
cache client. Run its offline protocol tests with:

```sh
python3 -m unittest discover -s scripts -p test_lake_cache.py
```

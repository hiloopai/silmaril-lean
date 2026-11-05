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

Install `cov-lake-cache` from the [Covalence releases](https://github.com/hiloopai/covalence/releases).
The revision and archive checksum used by CI are in `.github/actions/lake-cache-tool`.
`make cache` fetches public dependency artifacts. If `LAKE_CI_BUCKET` is set, it
also restores the available project artifacts. A normal clone needs no credentials.

For an authorized S3-compatible cache, configure:

```sh
export AWS_ENDPOINT_URL=https://your-s3-endpoint
export AWS_REGION=auto  # use the bucket's region for AWS S3
export LAKE_CI_BUCKET=your-bucket
export LAKE_CI_PREFIX=silmaril-lean/v1
export AWS_ACCESS_KEY_ID=your-access-id
export AWS_SECRET_ACCESS_KEY=your-secret
make cache
```

For AWS S3, omit `AWS_ENDPOINT_URL` and use the standard AWS credential chain.
The shared tool uses Covalence's S3 transport. It compresses Lake's native
artifacts and records mappings for the successful build. Cache keys include the
repository, platform, Lean version, dependency pins and Lake configuration.
Lake validates restored artifacts; `make check` still runs every native test.

`LAKE_CACHE_RECORD=build/lake-cache/root make check` records a successful build
from a clean checkout. After all checks pass, trusted main CI calls
`cov-lake-cache put --repository hiloopai/silmaril-lean`. Publication does not
run another build. Old uncompressed entries are not used by this cache format.

CI keeps its existing repository variables (`SILMARIL_CACHE_ENDPOINT`,
`SILMARIL_CACHE_BUCKET`, `SILMARIL_CACHE_PREFIX`, `SILMARIL_CACHE_REGION`) and
translates them to the shared tool's configuration. The combined writer secret,
`SILMARIL_CACHE_KEY`, stays in the `artifact-cache-publish` environment, whose
deployment policy permits only `main`. Pull requests use `artifact-cache-read`
and can use a separately provisioned **read-only** `SILMARIL_CACHE_READ_KEY`;
forks receive no secrets. Without a read credential, CI uses the disk cache or
builds normally. Remote failures remain visible and do not suppress proof checks.

Covalence owns the transfer, corruption and real-Lean integration tests. This
repository tests its CI time guard and runs the complete release checks.
Thomas owns this adapter. Remove it when Lake provides recorded-build
publication with bounded authenticated S3 transfers. Remove the dependency
adapter when the pinned upstream releases support the standard cache command.

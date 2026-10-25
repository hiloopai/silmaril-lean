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

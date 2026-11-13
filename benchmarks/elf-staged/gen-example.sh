#!/usr/bin/env bash
# Regenerate Silmaril/Elf/Staged/Example/{Defs,Thms}.lean from the pinned
# examples/dyn/pinned/hello-gcc: the shared objects (layout, bodies, loader view, symbol
# indexes, the instruction boundaries of `main`) and the leaf theorems that check them.
# Needs objdump (for the boundaries of `main`); untrusted: a wrong object fails its leaf.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$ROOT"
lake build elf-staged >/dev/null
mkdir -p build/elf-staged
exe=examples/dyn/pinned/hello-gcc
"$ROOT/benchmarks/elf-staged/boundaries-objdump.sh" "$exe" .text > build/elf-staged/hello.tiles
.lake/build/bin/elf-staged emit-example "$exe" Silmaril.Elf.Staged.Example.Defs \
  Silmaril/Elf/Staged/Example/Defs.lean Silmaril/Elf/Staged/Example/Thms.lean \
  --bytes-const Silmaril.Elf.Link.Dyn.PinBytes.helloGcc --import Silmaril.Elf.Link.Dyn.Pin.Bytes \
  --namespace Silmaril.Elf.Staged.Example --tiles build/elf-staged/hello.tiles --function main

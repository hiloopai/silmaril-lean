#!/usr/bin/env bash
# Regenerate Silmaril/Elf/Staged/Example/Thms.lean: every stage of the pinned
# examples/dyn/pinned/hello-gcc, kernel-checked, and the parse assembled from them.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$ROOT"
lake build elf-staged >/dev/null
out=Silmaril/Elf/Staged/Example/Thms.lean
.lake/build/bin/elf-staged emit examples/dyn/pinned/hello-gcc "$out.tmp" --bodies --rela-windows 0 \
  --bytes-const Silmaril.Elf.Link.Dyn.PinBytes.helloGcc --import Silmaril.Elf.Link.Dyn.Pin.Bytes \
  --namespace Silmaril.Elf.Staged.Example >/dev/null
{
  echo module
  echo
  sed -e 's/^import /public import /' \
      -e '/^set_option maxHeartbeats 0$/d' \
      -e 's/^namespace Silmaril.Elf.Staged.Example$/@[expose] public section\n\nnamespace Silmaril.Elf.Staged.Example/' \
      "$out.tmp"
} > "$out"
rm "$out.tmp"
echo "wrote $out"

#!/usr/bin/env bash
# Check the full, ordinary unstripped GCC -O2 artifact from the comparison matrix.
set -euo pipefail
if [[ $# != 1 ]]; then
  printf 'Usage: %s MATRIX_GCC_O2_LIBSQLITE3_SO\n' "$0" >&2
  exit 2
fi

tool_dir=$(cd -- "$(dirname -- "$0")" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
cp -- "$1" "$scratch/libsqlite3.so"
cp -- "$tool_dir/MatrixReplay.lean" "$scratch/MatrixReplay.lean"
(
  cd -- "$scratch"
  printf '%s  libsqlite3.so\n' 31d32767089dadc634fc6b07f5975fe8371a2c2d5765e35cea6fe0a82166ac06 |
    sha256sum -c -
)
cd -- "$tool_dir/../.."
lake build --wfail +Silmaril.Elf.Corpus.SqliteOneByteVarint.Checks +Silmaril.Elf.Staged.Reader.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true --root="$scratch" \
  -o "$scratch/MatrixReplay.olean" "$scratch/MatrixReplay.lean"
lake env bash -c '
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  export SILMARIL_REPLAY_MODULE=MatrixReplay
  lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
' matrix-replay "$scratch"

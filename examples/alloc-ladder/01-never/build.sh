#!/usr/bin/env bash
# Builds the rung at -O1 and -O2 under build/ and runs its self-test.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/flags.sh"
EXTRA_CFLAGS=(-DNEVER)
ladder_rung "$HERE" alloc "$HERE/alloc.c" "$HERE/../common/driver.c"

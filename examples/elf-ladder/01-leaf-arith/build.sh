#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "$HERE/../common/flags.sh"
ladder_rung "$HERE" leaf-arith "$HERE/arith.c" "$HERE/main.c"

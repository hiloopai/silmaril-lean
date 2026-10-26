#!/bin/sh
# Deterministic probe build: build.sh <probe.s> <output-elf> [rx|rwx]
# GNU as + ld, static, no libc, no build-id, symbols stripped, and one R+X
# PT_LOAD at 0x400000 that covers the ELF header, the program headers and the code
# (see probes/probe.ld). With rwx the PT_LOAD is also writable (probes/probe-rwx.ld),
# so a probe can read into a buffer of its own image at a fixed address.
# Rebuilding the same source with the same binutils gives the same bytes; tools/verification-projects/lps_probes.py checks SHA256SUMS.
set -eu
src=$1
out=$2
image=${3:-rx}
case $image in
  rx) script=probe.ld; warn= ;;
  rwx) script=probe-rwx.ld; warn=--no-warn-rwx-segments ;;
  *) echo "build.sh: image must be rx or rwx" >&2; exit 2 ;;
esac
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
obj=$out.o
LC_ALL=C as --64 -o "$obj" "$src"
LC_ALL=C ld -static -nostdlib --build-id=none -s -z noexecstack -z noseparate-code $warn \
  -T "$here/probes/$script" -o "$out" "$obj"
rm -f "$obj"

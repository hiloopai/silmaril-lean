#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export LC_ALL=C SOURCE_DATE_EPOCH=1792161920

if (( $# > 1 )); then
  echo "usage: $0 [directory containing the four pinned ELFs]" >&2
  exit 2
fi
if (( $# == 1 )); then
  for file in client libsqlite3.so.0 libc.so.6 ld-linux-x86-64.so.2; do
    cp "$1/$file" "$scratch/$file"
  done
else
  (
    cd "$scratch"
    curl -fsSL https://sqlite.org/2026/sqlite-amalgamation-3540100.zip -o sqlite.zip
    curl -fsSL https://snapshot.debian.org/file/27904cc1b58dd79f0768ba6aa6dd993edc411b97 -o libc6.deb
    sha256sum -c <<'SUMS'
0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9  sqlite.zip
967aa62605721081c3eb2a17650611a792aa802d76a6511d1840242623d204c9  libc6.deb
SUMS
    unzip -q sqlite.zip
    dpkg-deb -x libc6.deb runtime
    cp runtime/usr/lib/x86_64-linux-gnu/{libc.so.6,ld-linux-x86-64.so.2} .
    src=sqlite-amalgamation-3540100
    flags=(-O2 -g0 -march=x86-64 -mtune=generic -pthread -DSQLITE_THREADSAFE=1
      -DSQLITE_OMIT_LOAD_EXTENSION=1 -DSQLITE_MAX_MMAP_SIZE=0 -DSQLITE_DEFAULT_MMAP_SIZE=0)
    gcc "${flags[@]}" -fPIC -c "$src/sqlite3.c" -o sqlite3.o
    gcc -shared -pthread -Wl,-soname,libsqlite3.so.0 -o libsqlite3.so.0 sqlite3.o -lm
    ln -s libsqlite3.so.0 libsqlite3.so
    gcc "${flags[@]}" -Wall -Wextra -Werror -fPIE -pie -I"$src" "$here/client.c" \
      -L. '-Wl,-rpath,$ORIGIN' -Wl,--enable-new-dtags -lsqlite3 -lm -o client
  )
fi

(
  cd "$scratch"
  sha256sum -c "$here/pins.sha256"
)
(
  cd "$repo"
  corpus=corpus/variants/sqlite/3.54.1/default/x86_64/O2/unstripped/libsqlite3.so
  printf '%s  %s\n' fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8 "$corpus" | sha256sum -c
  if cmp -s "$scratch/libsqlite3.so.0" "$corpus"; then
    echo 'unexpected equality between campaign and corpus DSO' >&2
    exit 1
  fi
  cp "$here/Replay.lean" "$scratch/Replay.lean"
  lake build --wfail +Silmaril.Data.IncludeBytes.Kernel +Silmaril.Elf.Link.Dyn.Image.Thms \
    +Silmaril.Elf.Staged.Reader.Thms
  lake env lean -DautoImplicit=false -DwarningAsError=true "$scratch/Replay.lean"
)

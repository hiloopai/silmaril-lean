#!/usr/bin/env bash
# The pinned clang JSON ASTs of examples/headers/clang/, and the zlib.h excerpt the Lean
# subset reader reads (examples/headers/zlib-1.3.1/zlib.h).
#
#   examples/headers/recipe.sh           regenerate the committed files
#   examples/headers/recipe.sh --check   regenerate into a temporary directory and compare
#                                        byte for byte with the committed files
#
# Every artifact is `clang -Xclang -ast-dump=json -fsyntax-only` of one header, run by the clang
# of the image below (pinned by digest), filtered by clang/filter.py (also run in that image,
# by its python3) to the top-level declarations located in the header's own files, each
# projected to the keys the Lean import reads. The provenance of each artifact (image, clang
# version, exact command, defines, include paths, SHA-256 of every input file, of the filter
# and of the JSON) is written next to it as `<name>.prov` and read by
# Silmaril.Data.Layout.Header.Import.Pinned. The JSON is a pinned tool output: the Lean import
# normalizes it and never assumes that clang is correct.
#
# Last, emit.lean (compiled Lean, `lake env lean --run`; needs `lake` on PATH) writes the
# normalized header of each artifact as a literal, Silmaril/Data/Layout/Header/Import/Pinned/
# <Name>/Defs.lean. The kernel checks that literal against the JSON (Pinned.import_<name>).
#
# Inputs: the repository's examples/elf-ladder/01-leaf-arith/arith.h and
# examples/elf-ladder/common/rt.h; examples/headers/probe/probe.h; zlib 1.3.1's zlib.h and
# zconf.h from the release tarball (fetched, SHA-256 checked, not committed; set ZLIB_TARBALL
# to a local copy to skip the download); glibc's string.h as installed in the image.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
IMAGE=silkeh/clang@sha256:3914c93a02e866795aafc80737488e515b96390eff3d2787cf8c5095997baea9  # silkeh/clang:18 (Debian clang 18.1.8)
ZLIB_URL=https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz
ZLIB_SHA256=9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23
TARGET=x86_64-unknown-linux-gnu
STD=gnu11

check=0
[ "${1:-}" = --check ] && check=1
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
if [ $check = 1 ]; then out=$work/out; else out=$HERE; fi
mkdir -p "$out/clang" "$out/zlib-1.3.1"

# zlib 1.3.1, checked against the release tarball's SHA-256.
tarball=${ZLIB_TARBALL:-}
if [ -z "$tarball" ]; then
  tarball=$work/zlib-1.3.1.tar.gz
  curl -fsSL -o "$tarball" "$ZLIB_URL"
fi
echo "$ZLIB_SHA256  $tarball" | sha256sum -c --quiet
mkdir -p "$work/zlib"
tar -xzf "$tarball" -C "$work/zlib" zlib-1.3.1/zlib.h zlib-1.3.1/zconf.h

sha() { sha256sum "$1" | cut -d' ' -f1; }

# run NAME MOUNT CWD "FILTER FILES" CLANG-ARGS... : one artifact. MOUNT is mounted read-only
# at /in; CWD is relative to it; the filter keeps the declarations of FILTER FILES (as clang
# prints them, relative to CWD).
run() {
  local name=$1 mount=$2 cwd=$3 files=$4; shift 4
  local cmd=(clang -target "$TARGET" -x c -std="$STD" "$@" -Xclang -ast-dump=json -fsyntax-only)
  docker run --rm --network none -v "$mount:/in:ro" -v "$HERE/clang/filter.py:/recipe/filter.py:ro" \
    -w "/in/$cwd" "$IMAGE" bash -c \
    'set -euo pipefail; files=$1; shift; "$@" > /tmp/full.json; python3 -I /recipe/filter.py $files < /tmp/full.json' \
    recipe "$files" "${cmd[@]}" > "$out/clang/$name.json"
  local version
  version=$(docker run --rm --network none "$IMAGE" clang --version | head -n1)
  {
    echo "artifact: $name.json"
    echo "image: $IMAGE"
    echo "clang: $version"
    echo "target: $TARGET"
    echo "std: $STD"
    echo "cwd: $cwd"
    echo "command: ${cmd[*]}"
    for a in "$@"; do
      case $a in
        -D*) echo "define: ${a#-D}" ;;
        -I*) echo "include: ${a#-I}" ;;
      esac
    done
    echo "filter: python3 -I filter.py $files"
    echo "filter-sha256: $(sha "$HERE/clang/filter.py")"
    for f in $files; do
      if [ -e "$mount/$cwd/$f" ]; then
        echo "input: $f $(sha "$mount/$cwd/$f")"
      else
        echo "input: $f $(docker run --rm --network none -w "/" "$IMAGE" sha256sum "$f" | cut -d' ' -f1) (in the image)"
      fi
    done
    echo "json-sha256: $(sha "$out/clang/$name.json")"
    echo "json-bytes: $(wc -c < "$out/clang/$name.json")"
  } > "$out/clang/$name.prov"
}

run arith "$ROOT/examples/elf-ladder" 01-leaf-arith "arith.h ../common/rt.h" \
  -ffreestanding -fno-builtin -I../common arith.h
run probe "$ROOT/examples/headers/probe" . "probe.h" -ffreestanding -fno-builtin probe.h
run zlib-solo "$work/zlib" zlib-1.3.1 "zlib.h ./zconf.h" -ffreestanding -fno-builtin -DZ_SOLO zlib.h
run zlib-hosted "$work/zlib" zlib-1.3.1 "zlib.h ./zconf.h" zlib.h
run glibc-string "$work" . "/usr/include/string.h" /usr/include/string.h
sed -i "s|^input: zlib.h|source: zlib-1.3.1.tar.gz $ZLIB_SHA256 $ZLIB_URL\ninput: zlib.h|" \
  "$out/clang/zlib-solo.prov" "$out/clang/zlib-hosted.prov"

# The excerpt of zlib.h that the Lean subset reader reads: verbatim line ranges of the
# tarball's zlib.h (the checksum API), each under a comment giving its lines.
z=$work/zlib/zlib-1.3.1/zlib.h
{
  cat <<EOF
/* zlib.h, excerpt: the checksum API of zlib 1.3.1, for Silmaril.Data.Layout.Header.read.

   Generated by examples/headers/recipe.sh from zlib.h of
   $ZLIB_URL
   (SHA-256 $ZLIB_SHA256; zlib.h SHA-256 $(sha "$z")).
   Every line below a "zlib.h:N" comment is line N of that file, verbatim; nothing else of the
   file is here. The configuration it includes as "zconf.h" is zconf-solo.h or zconf-hosted.h.
   The declarations of adler32_combine, crc32_combine and crc32_combine_gen are lines
   1907-1909 (the Z_SOLO branch); lines 1900-1902 (the hosted branch without Z_WANT64) are the
   same text.

   The zlib licence (zlib.h lines 4-23):

EOF
  sed -n '4,23p' "$z"
  echo "*/"
  for r in 31,38 220,220 1179,1179 1692,1692 1712,1713 1730,1730 1748,1749 1771,1771 \
      1907,1909 1916,1916 1934,1938; do
    a=${r%,*} b=${r#*,}
    if [ "$a" = "$b" ]; then echo "/* zlib.h:$a */"; else echo "/* zlib.h:$a-$b */"; fi
    sed -n "${r}p" "$z"
  done
} > "$out/zlib-1.3.1/zlib.h"

# The normalized headers as Lean literals.
pinned=Silmaril/Data/Layout/Header/Import/Pinned
if [ $check = 1 ]; then lean_out=$out/lean; else lean_out=$ROOT/$pinned; fi
( cd "$ROOT" && lake build -q Silmaril.Data.Layout.Header.Import.Defs > /dev/null &&
  lake env lean --run examples/headers/emit.lean "$out/clang" "$lean_out" )

if [ $check = 1 ]; then
  status=0
  for f in "$out"/clang/*.json "$out"/clang/*.prov "$out/zlib-1.3.1/zlib.h"; do
    rel=${f#"$out/"}
    if cmp -s "$f" "$HERE/$rel"; then echo "ok $rel ($(wc -c < "$f") bytes)"
    else echo "DIFFERS $rel" >&2; status=1; fi
  done
  for f in "$lean_out"/*/Defs.lean; do
    rel=$pinned/${f#"$lean_out/"}
    if cmp -s "$f" "$ROOT/$rel"; then echo "ok $rel ($(wc -c < "$f") bytes)"
    else echo "DIFFERS $rel" >&2; status=1; fi
  done
  # Lake does not track files read by `include_str`: the modules that read the header texts
  # name their SHA-256, so that a change to a text changes (and rebuilds) the module.
  for pair in "$pinned/Defs.lean examples/elf-ladder/01-leaf-arith/arith.h" \
      "$pinned/Defs.lean examples/elf-ladder/common/rt.h" \
      "Silmaril/Data/Layout/Header/Zlib/Defs.lean examples/headers/zlib-1.3.1/zlib.h" \
      "Silmaril/Data/Layout/Header/Zlib/Defs.lean examples/headers/zlib-1.3.1/zconf-solo.h" \
      "Silmaril/Data/Layout/Header/Zlib/Defs.lean examples/headers/zlib-1.3.1/zconf-hosted.h" \
      "Silmaril/Data/Layout/Header/Demo/Defs.lean examples/headers/layout/demo.h"; do
    set -- $pair
    if grep -q "$(sha "$ROOT/$2")" "$ROOT/$1"; then echo "ok $1 names the SHA-256 of $2"
    else echo "STALE $1 does not name the SHA-256 of $2" >&2; status=1; fi
  done
  exit $status
fi

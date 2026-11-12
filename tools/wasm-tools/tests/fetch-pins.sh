#!/usr/bin/env bash
# Install the pinned reference tools and corpora of tools/wasm-tools/tests/pins.sh into
# $SIL_TOOLS (default ~/.cache/silmaril-tools).
#
#   tools/wasm-tools/tests/fetch-pins.sh [--check] [wasm-tools] [src] [spec] [adapters] [binaryen]
#     [wasi-sdk]
#
# With no names, installs wasm-tools, src, spec and adapters (what the differential suites
# need); binaryen
# (the e-graph corpus runs) and wasi-sdk (the DWARF and libc++ samples) only when named.
# Each download goes to a fresh empty directory and is checked against its pinned SHA-256 before
# anything is unpacked; the unpacked binaries are checked again. Nothing inside an archive is run.
# Items already installed are only re-checked. `--check` downloads nothing: it reports each item
# as ok, missing or MISMATCH and exits 1 on a mismatch.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=pins.sh
source "$here/pins.sh"

check_only=0
items=()
for a in "$@"; do
  case $a in
    --check) check_only=1 ;;
    wasm-tools|src|spec|adapters|binaryen|wasi-sdk) items+=("$a") ;;
    *) echo "usage: fetch-pins.sh [--check] [wasm-tools] [src] [spec] [adapters] [binaryen] [wasi-sdk]" >&2; exit 2 ;;
  esac
done
[[ ${#items[@]} -gt 0 ]] || items=(wasm-tools src spec adapters)

need() { command -v "$1" >/dev/null 2>&1 || { echo "fetch-pins: needs $1 on PATH" >&2; exit 1; }; }
need sha256sum; need tar
verify() { # path sha
  local got; got=$(wt_sha256 "$1")
  [[ $got == "$2" ]] || { echo "fetch-pins: SHA-256 mismatch for $1: $got, want $2" >&2; return 1; }
}

dl=$(mktemp -d /tmp/wasm-tools-pins.XXXXXX)
trap 'rm -rf "$dl"' EXIT
fetch() { # url sha -> prints the path of the checked download
  need curl
  local d; d=$(mktemp -d "$dl/d.XXXXXX")
  curl -sSfL -o "$d/archive" "$1"
  verify "$d/archive" "$2"
  printf '%s\n' "$d/archive"
}
keep() { # archive sha destination: copy a checked archive into the cache (as the tests read it)
  mkdir -p "$(dirname "$3")"; cp "$1" "$3"; verify "$3" "$2"
}

status=0
report() { printf '%-10s %s\n' "$1" "$2"; }

for it in "${items[@]}"; do
  case $it in
    wasm-tools)
      if [[ -x $WT_UPSTREAM ]]; then
        verify "$WT_UPSTREAM" "$WT_UPSTREAM_SHA256" && report "$it" "ok $WT_UPSTREAM" || { report "$it" MISMATCH; status=1; }
      elif [[ $check_only == 1 ]]; then report "$it" "missing $WT_UPSTREAM"
      else
        a=$(fetch "$WT_URL" "$WT_ARCHIVE_SHA256")
        tar -xzf "$a" -C "$(dirname "$a")" "wasm-tools-$WT_VERSION-x86_64-linux/wasm-tools"
        b=$(dirname "$a")/wasm-tools-$WT_VERSION-x86_64-linux/wasm-tools
        verify "$b" "$WT_UPSTREAM_SHA256"
        mkdir -p "$WT_UPSTREAM_DIR"; install -m 755 "$b" "$WT_UPSTREAM"
        report "$it" "installed $WT_UPSTREAM"
      fi ;;
    src)
      if [[ -f $WT_SRC_ARCHIVE ]]; then
        verify "$WT_SRC_ARCHIVE" "$WT_SRC_SHA256" && report "$it" "ok $WT_SRC_ARCHIVE" || { report "$it" MISMATCH; status=1; }
      elif [[ $check_only == 1 ]]; then report "$it" "missing $WT_SRC_ARCHIVE"
      else
        a=$(fetch "$WT_SRC_URL" "$WT_SRC_SHA256"); keep "$a" "$WT_SRC_SHA256" "$WT_SRC_ARCHIVE"
        report "$it" "installed $WT_SRC_ARCHIVE"
      fi
      if [[ $check_only == 0 && -f $WT_SRC_ARCHIVE && ! -d $WT_SRC_DIR ]]; then
        mkdir -p "$(dirname "$WT_SRC_DIR")"; tar -xzf "$WT_SRC_ARCHIVE" -C "$(dirname "$WT_SRC_DIR")"
        report "$it" "unpacked $WT_SRC_DIR"
      fi ;;
    spec)
      if [[ -f $WASM_SPEC_ARCHIVE ]]; then
        verify "$WASM_SPEC_ARCHIVE" "$WASM_SPEC_SHA256" && report "$it" "ok $WASM_SPEC_ARCHIVE" || { report "$it" MISMATCH; status=1; }
      elif [[ $check_only == 1 ]]; then report "$it" "missing $WASM_SPEC_ARCHIVE"
      else
        a=$(fetch "$WASM_SPEC_URL" "$WASM_SPEC_SHA256"); keep "$a" "$WASM_SPEC_SHA256" "$WASM_SPEC_ARCHIVE"
        report "$it" "installed $WASM_SPEC_ARCHIVE"
      fi
      if [[ $check_only == 0 && -f $WASM_SPEC_ARCHIVE && ! -d $WASM_SPEC_DIR ]]; then
        mkdir -p "$WASM_SPEC_DIR"
        tar -xzf "$WASM_SPEC_ARCHIVE" -C "$WASM_SPEC_DIR" --wildcards '*/test/core/*'
        report "$it" "unpacked $WASM_SPEC_DIR"
      fi ;;
    adapters)
      for pair in "$WASI_ADAPTER_COMMAND:$WASI_ADAPTER_COMMAND_SHA256" \
                  "$WASI_ADAPTER_REACTOR:$WASI_ADAPTER_REACTOR_SHA256"; do
        sha=${pair##*:}; f=${pair%:*}
        if [[ -f $f ]]; then
          verify "$f" "$sha" && report "$it" "ok $f" || { report "$it" MISMATCH; status=1; }
        elif [[ $check_only == 1 ]]; then report "$it" "missing $f"
        else
          a=$(fetch "$WASI_ADAPTER_URL/$(basename "$f")" "$sha"); keep "$a" "$sha" "$f"
          report "$it" "installed $f"
        fi
      done ;;
    binaryen)
      if [[ -x $BINARYEN_WASM_OPT ]]; then
        verify "$BINARYEN_WASM_OPT" "$BINARYEN_WASM_OPT_SHA256" && report "$it" "ok $BINARYEN_WASM_OPT" || { report "$it" MISMATCH; status=1; }
      elif [[ $check_only == 1 ]]; then report "$it" "missing $BINARYEN_WASM_OPT"
      else
        a=$(fetch "$BINARYEN_URL" "$BINARYEN_ARCHIVE_SHA256")
        mkdir -p "$(dirname "$BINARYEN_DIR")"; tar -xzf "$a" -C "$(dirname "$BINARYEN_DIR")"
        verify "$BINARYEN_WASM_OPT" "$BINARYEN_WASM_OPT_SHA256"
        report "$it" "installed $BINARYEN_WASM_OPT"
      fi ;;
    wasi-sdk)
      if [[ -x $WASI_SDK/bin/clang-20 ]]; then
        verify "$WASI_SDK/bin/clang-20" "$WASI_SDK_CLANG_SHA256" && report "$it" "ok $WASI_SDK" || { report "$it" MISMATCH; status=1; }
      elif [[ $check_only == 1 ]]; then report "$it" "missing $WASI_SDK"
      else
        a=$(fetch "$WASI_SDK_URL" "$WASI_SDK_ARCHIVE_SHA256")
        mkdir -p "$WASI_SDK"; tar -xzf "$a" -C "$WASI_SDK" --strip-components=1
        verify "$WASI_SDK/bin/clang-20" "$WASI_SDK_CLANG_SHA256"
        report "$it" "installed $WASI_SDK"
      fi ;;
  esac
done
exit $status

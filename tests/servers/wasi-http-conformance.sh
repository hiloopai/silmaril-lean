#!/usr/bin/env bash
# Conformance of wasi:http proxy components against a runtime that serves them.
#
# For each example server of Silmaril.Servers.WasiExamples, serve its wasi:http/proxy component
# (built from tests/servers/wasi-http/*.wat by tests/servers/wasi-http/build.sh) with
# `wasmtime serve` and compare the responses to the specification (`helloResp`, `routeResp`,
# echo's `200` with the request's content), whose expected status and content are listed below.
#
# Usage: nix develop .#http-test -c tests/servers/wasi-http-conformance.sh
#    or: HELLO_WASM=hello.wasm ROUTE_WASM=route.wasm ECHO_WASM=echo.wasm \
#          tests/servers/wasi-http-conformance.sh
#
# Without HELLO_WASM, ROUTE_WASM and ECHO_WASM the components are built (with wasm-tools) into
# a temporary directory. The runtime is pinned to WASMTIME_VERSION (default: 49.0.2, the
# wasmtime of the flake's `http-test` shell). The check is skipped (exit 0, with a message)
# when `wasmtime` or `curl` is missing, when the components can be neither found nor built, or
# when `wasmtime --version` differs from the pin (WASMTIME_VERSION=any accepts every version).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)

skip() { echo "skip: $*"; exit 0; }
command -v wasmtime >/dev/null 2>&1 || skip "wasmtime not found"
command -v curl >/dev/null 2>&1 || skip "curl not found"
pin=${WASMTIME_VERSION:-49.0.2}
have=$(wasmtime --version | awk '{print $2}')
[[ "$pin" == any || "$have" == "$pin" ]] || skip "wasmtime $have, pinned $pin"
if [[ -z "${HELLO_WASM:-}${ROUTE_WASM:-}${ECHO_WASM:-}" ]]; then
  command -v wasm-tools >/dev/null 2>&1 || skip "no component given and wasm-tools not found"
  built=$(mktemp -d)
  "$here/wasi-http/build.sh" "$built" >/dev/null
  HELLO_WASM=$built/hello.wasm ROUTE_WASM=$built/route.wasm ECHO_WASM=$built/echo.wasm
fi
echo "wasmtime $have"

port=${PORT:-8089}
status=0
pid=
stop() { [[ -n "$pid" ]] && kill "$pid" 2>/dev/null && wait "$pid" 2>/dev/null || true; pid=; }
trap 'stop; [[ -n "${built:-}" ]] && rm -rf "$built"' EXIT

serve() {
  wasmtime serve --addr "127.0.0.1:$port" "$1" >/dev/null 2>&1 &
  pid=$!
  for _ in $(seq 50); do
    curl -s -o /dev/null "http://127.0.0.1:$port/" && return 0
    sleep 0.1
  done
  echo "error: $1 did not start" >&2
  return 1
}

# expect PATH STATUS BODY [CURL-ARGS...]
expect() {
  local out code body path=$1 want=$2 wbody=$3
  shift 3
  out=$(curl -s -w '\n%{http_code}' "$@" "http://127.0.0.1:$port$path")
  code=${out##*$'\n'}
  body=${out%$'\n'*}
  if [[ "$code" == "$want" && "$body" == "$wbody" ]]; then
    echo "ok   $path -> $code ${body:0:40}"
  else
    echo "FAIL $path -> $code ${body:0:40} (expected $want ${wbody:0:40})"
    status=1
  fi
}

if [[ -n "${HELLO_WASM:-}" ]]; then
  serve "$HELLO_WASM"
  expect / 200 hello          # helloResp
  expect /anything 200 hello
  stop
fi
if [[ -n "${ROUTE_WASM:-}" ]]; then
  serve "$ROUTE_WASM"
  expect / 200 home           # routeResp
  expect /hello 200 hello
  expect /missing 404 "not found"
  stop
fi
if [[ -n "${ECHO_WASM:-}" ]]; then
  serve "$ECHO_WASM"
  expect / 200 ""             # a GET has no content
  expect /e 200 abc --data-binary abc
  big=$(head -c 3000 /dev/zero | tr '\0' x)
  expect /e 200 "$big" --data-binary "$big"
  stop
fi
exit $status

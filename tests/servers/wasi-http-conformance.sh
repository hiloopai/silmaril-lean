#!/usr/bin/env bash
# Conformance of wasi:http proxy components against a runtime that serves them.
#
# For each example server of Silmaril.Servers.WasiExamples, serve a component built for the
# wasi:http/proxy world with `wasmtime serve` and compare the responses to the specification
# (`helloResp`, `routeResp`), whose expected status and content are listed below.
#
# Usage: HELLO_WASM=path/to/hello.wasm ROUTE_WASM=path/to/route.wasm \
#          tests/servers/wasi-http-conformance.sh
#
# The check is skipped (exit 0, with a message) when `wasmtime` or `curl` is missing, when no
# component is given, or when WASMTIME_VERSION is set and differs from `wasmtime --version`.
# No component binaries are checked in yet: the example servers are Lean programs over the
# imports, not compiled Wasm (see docs/projects/http-servers.md).
set -euo pipefail

skip() { echo "skip: $*"; exit 0; }
command -v wasmtime >/dev/null 2>&1 || skip "wasmtime not found"
command -v curl >/dev/null 2>&1 || skip "curl not found"
if [[ -n "${WASMTIME_VERSION:-}" ]]; then
  have=$(wasmtime --version | awk '{print $2}')
  [[ "$have" == "$WASMTIME_VERSION" ]] || skip "wasmtime $have, pinned $WASMTIME_VERSION"
fi
[[ -n "${HELLO_WASM:-}${ROUTE_WASM:-}" ]] || skip "no component given (HELLO_WASM, ROUTE_WASM)"

port=${PORT:-8089}
status=0
pid=
stop() { [[ -n "$pid" ]] && kill "$pid" 2>/dev/null && wait "$pid" 2>/dev/null || true; pid=; }
trap stop EXIT

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

# expect PATH STATUS BODY
expect() {
  local out code body
  out=$(curl -s -w '\n%{http_code}' "http://127.0.0.1:$port$1")
  code=${out##*$'\n'}
  body=${out%$'\n'*}
  if [[ "$code" == "$2" && "$body" == "$3" ]]; then
    echo "ok   $1 -> $code $body"
  else
    echo "FAIL $1 -> $code $body (expected $2 $3)"
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
exit $status

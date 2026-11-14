#!/usr/bin/env bash
# Runtime experiments: a wasi:http server with a modeled nondeterministic import, run under
# replayable host policies.
#
# The dice servers of Silmaril.Servers.Examples.Dice (tests/servers/policies/dice.wat, and
# dice-buggy.wat with a planted bug) import wasi:random/random@0.2.12 `get-random-u64`. Each host
# policy is a component exporting that interface; `wac plug` composes it with a server, and
# `wasmtime serve` serves the composition `server ∘ policy` on 127.0.0.1. Policies (all
# deterministic, replayable from their parameters; see tests/servers/policies/README.md):
# * zero:         every draw is 0;
# * seeded SEED:  the splitmix64 stream of SEED: draw k (from 0, per instance) is
#                 mix(SEED + (k + 1) * 0x9E3779B97F4A7C15);
# * chaos SEED:   schedule chaos-v1: h = draw k of `seeded SEED`; by h mod 8: 0..3 -> h,
#                 4 -> 0, 5 -> 0xFFFFFFFFFFFFFFFF, 6 -> 5, 7 -> 6.
# For each server in {dice, dice-buggy} and policy in {zero, seeded 1, seeded 42, chaos 7}, a
# bounded request sequence (N_ROLL `/roll`, N_PAIR `/pair`, then other paths) is served twice,
# by two fresh `wasmtime serve` processes, and checked:
# * must:   `/roll` and each component of `/pair` is in 1..6, other paths are `404 not found`;
#           dice must pass under every policy; dice-buggy must pass under zero and fail under
#           at least one policy (a planted negative: passing under one policy is no proof);
# * replay: both traces are identical;
# * may:    the observed values, and whether the trace is the one predicted when every request
#           gets a fresh policy instance (the per-request instantiation observation).
# Then negative cases, each an expected rejection: (a) a core module, (b) an export named
# wasi:http/incoming-handler@0.2.12 of the wrong type, (c) a start function that traps
# (`initFail`), (d) a handler that never returns (a bounded `timeout`).
#
# Every run writes a JSON evidence record (schema silmaril.servers.runtime-evidence.v1,
# `"evidence": "runtime-test"`: testing evidence, not a Lean proof) to EVIDENCE_DIR (default:
# build/servers-policies/evidence), with summary.json and negatives.json.
#
# Usage: tests/servers/wasi-http-policies.sh
# Environment: EVIDENCE_DIR, PORT (default 8090), WASMTIME_VERSION (default 49.0.2, the pin of
# tests/servers/wasi-http-conformance.sh; `any` accepts every version), N_ROLL (32), N_PAIR (8),
# CURL_TIMEOUT (5 s per request), START_TIMEOUT (10 s for a server to listen), LOOP_TIMEOUT (3 s,
# negative case (d)). Skipped (exit 0, with a message) when wasmtime, wasm-tools, wac, curl or
# jq is missing, or when `wasmtime --version` differs from the pin.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
pol=$here/policies

skip() { echo "skip: $*"; exit 0; }
for t in wasmtime wasm-tools wac curl jq; do
  command -v "$t" >/dev/null 2>&1 || skip "$t not found"
done
pin=${WASMTIME_VERSION:-49.0.2}
have=$(wasmtime --version | awk '{print $2}')
[[ "$pin" == any || "$have" == "$pin" ]] || skip "wasmtime $have, pinned $pin"

out=${EVIDENCE_DIR:-$root/build/servers-policies/evidence}
port=${PORT:-8090}
n_roll=${N_ROLL:-32}
n_pair=${N_PAIR:-8}
others=(/nope /nope "/roll?x=1" /rolls /)
curl_timeout=${CURL_TIMEOUT:-5}
start_timeout=${START_TIMEOUT:-10}
loop_timeout=${LOOP_TIMEOUT:-3}
mkdir -p "$out"
rm -f "$out"/*.json

sha() { sha256sum "$1" | awk '{print $1}'; }
bytes() { wc -c < "$1" | tr -d ' '; }
wasmtime_bin=$(command -v wasmtime)
wasm_tools_bin=$(command -v wasm-tools)
wac_bin=$(command -v wac)
tools_json=$(jq -nc \
  --arg wv "$have" --arg ws "$(sha "$wasmtime_bin")" \
  --arg tv "$(wasm-tools --version)" --arg ts "$(sha "$wasm_tools_bin")" \
  --arg av "$(wac --version)" --arg as "$(sha "$wac_bin")" \
  '{runtime: {name: "wasmtime serve", version: $wv, binary_sha256: $ws},
    wasm_tools: {version: $tv, binary_sha256: $ts}, wac: {version: $av, binary_sha256: $as}}')
commit=$(git -C "$root" rev-parse HEAD 2>/dev/null || echo unknown)
dirty=$( [[ -n "$(git -C "$root" status --porcelain 2>/dev/null)" ]] && echo true || echo false)
date=$(date -u +%Y-%m-%dT%H:%M:%SZ)
echo "wasmtime $have, $(wasm-tools --version), $(wac --version)"

work=$(mktemp -d)
pid=
stop() {
  if [[ -n "$pid" ]]; then
    kill "$pid" 2>/dev/null || true
    for _ in $(seq 50); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
    kill -9 "$pid" 2>/dev/null || true
    wait "$pid" 2>/dev/null || true
  fi
  pid=
}
trap 'stop; rm -rf "$work"' EXIT

# --- build ------------------------------------------------------------------------------------

wit=$work/wit
mkdir -p "$wit/deps"
cp "$pol/world.wit" "$wit/"
for p in http io clocks random cli filesystem sockets; do
  cp -r "$root/specs/wasi/0.2.12/$p" "$wit/deps/"
done

# component NAME WIT WORLD PARTS...: the component of the module of the PARTS (WAT fragments)
component() {
  local name=$1 w=$2 world=$3
  shift 3
  { echo "(module"; cat "$@"; echo ")"; } > "$work/$name.core.wat"
  wasm-tools parse "$work/$name.core.wat" -o "$work/$name.core.wasm"
  wasm-tools component embed "$w" -w "$world" "$work/$name.core.wasm" -o "$work/$name.embed.wasm"
  wasm-tools component new "$work/$name.embed.wasm" -o "$work/$name.wasm"
  wasm-tools validate "$work/$name.wasm"
}

# policy_part NAME SEED: the policy part with the seed substituted (zero has none)
policy_part() {
  local name=$1 seed=$2
  case $name in
    zero) cat "$pol/zero.wat" ;;
    seeded | chaos)
      [[ "$seed" =~ ^[0-9]+$ ]] || { echo "error: seed $seed is not a decimal u64" >&2; exit 2; }
      sed "s/@SEED@/$seed/g" "$pol/$name.wat.in" ;;
  esac
}

servers=(dice dice-buggy)
policies=("zero -" "seeded 1" "seeded 42" "chaos 7")
for s in "${servers[@]}"; do
  component "$s" "$wit" dice-server "$pol/random-import.wat" "$root/tests/servers/wasi-http/common.wat" \
    "$pol/dice-common.wat" "$pol/$s.wat"
done

# --- reference model of the policies (bash arithmetic: 64-bit, wrapping) -----------------------

gamma=$((0x9E3779B97F4A7C15))
mix() {
  local z=$1
  z=$(( (z ^ ((z >> 30) & 0x3FFFFFFFF)) * 0xBF58476D1CE4E5B9 ))
  z=$(( (z ^ ((z >> 27) & 0x1FFFFFFFFF)) * 0x94D049BB133111EB ))
  echo $(( z ^ ((z >> 31) & 0x1FFFFFFFF) ))
}
# umod X M: X read as unsigned u64, modulo M
umod() {
  local x=$1 m=$2
  if ((x >= 0)); then echo $((x % m)); else
    echo $(( ((x & 0x7FFFFFFFFFFFFFFF) % m + 0x7FFFFFFFFFFFFFFF % m + 1) % m )); fi
}
# draw POLICY SEED K: draw K (from 0) of a fresh instance of the policy
draw() {
  local h
  case $1 in
    zero) echo 0 ;;
    seeded) mix $(( $2 + ($3 + 1) * gamma )) ;;
    chaos)
      h=$(mix $(( $2 + ($3 + 1) * gamma )))
      case $((h & 7)) in
        4) echo 0 ;; 5) echo -1 ;; 6) echo 5 ;; 7) echo 6 ;; *) echo "$h" ;;
      esac ;;
  esac
}
face() { echo $(( $(umod "$1" "$2") + 1 )); }

# --- serving ----------------------------------------------------------------------------------

listening() { (exec 3<>"/dev/tcp/127.0.0.1/$port") 2>/dev/null; }

# start COMPONENT LOG: start `wasmtime serve`; status 0 once it listens, 1 if it exits first
# (or does not listen within START_TIMEOUT). The readiness probe only opens a TCP connection, so
# it never invokes the handler.
start() {
  local c=$1 log=$2
  if listening; then echo "error: port $port is already in use" >&2; exit 2; fi
  wasmtime serve --addr "127.0.0.1:$port" "$c" >"$log" 2>&1 &
  pid=$!
  for _ in $(seq $((start_timeout * 10))); do
    listening && return 0
    kill -0 "$pid" 2>/dev/null || { wait "$pid" 2>/dev/null || true; pid=; return 1; }
    sleep 0.1
  done
  return 1
}

# request PATH [TIMEOUT]: one GET, as a JSON trace entry (status 0 when no response arrived)
request() {
  local o e=0 code body
  o=$(curl -s --max-time "${2:-$curl_timeout}" -w '\n%{http_code}' "http://127.0.0.1:$port$1") || e=$?
  code=${o##*$'\n'}
  body=${o%$'\n'*}
  [[ "$o" == *$'\n'* ]] || body=
  jq -nc --arg p "$1" --argjson s "$((10#${code:-0}))" --arg b "$body" --argjson e "$e" \
    '{method: "GET", path: $p, status: $s, body: $b, curl_exit: $e}'
}

# trace COMPONENT FILE: serve the request sequence, the trace as a JSON array in FILE
trace() {
  local c=$1 f=$2 i p
  start "$c" "$f.log" || { echo "error: $c did not start" >&2; cat "$f.log" >&2; exit 1; }
  {
    for i in $(seq "$n_roll"); do request /roll; done
    for i in $(seq "$n_pair"); do request /pair; done
    for p in "${others[@]}"; do request "$p"; done
  } | jq -s . > "$f"
  stop
}

# predicted SERVER POLICY SEED: the trace bodies predicted when each request gets a fresh policy
# instance (draws 0 and 1 of the policy), one per line
predicted() {
  local rs=6 d0 d1 i
  [[ $1 == dice-buggy ]] && rs=7
  d0=$(draw "$2" "$3" 0)
  d1=$(draw "$2" "$3" 1)
  for i in $(seq "$n_roll"); do face "$d0" "$rs"; done
  for i in $(seq "$n_pair"); do echo "$(face "$d0" 6) $(face "$d1" 6)"; done
  for p in "${others[@]}"; do echo "not found"; done
}

# predicted_shared SERVER POLICY SEED: the bodies predicted if one policy instance served every
# request of a run in order (draw k of the run at the k-th draw)
predicted_shared() {
  local rs=6 k=0 i a
  [[ $1 == dice-buggy ]] && rs=7
  for i in $(seq "$n_roll"); do face "$(draw "$2" "$3" $k)" "$rs"; k=$((k + 1)); done
  for i in $(seq "$n_pair"); do
    a=$(face "$(draw "$2" "$3" $k)" 6)
    echo "$a $(face "$(draw "$2" "$3" $((k + 1)))" 6)"
    k=$((k + 2))
  done
  for p in "${others[@]}"; do echo "not found"; done
}

art() { jq -nc --arg f "$(basename "$1")" --arg s "$(sha "$1")" --argjson b "$(bytes "$1")" \
  '{file: $f, sha256: $s, bytes: $b}'; }

status=0
runs=()
for s in "${servers[@]}"; do
  for ps in "${policies[@]}"; do
    read -r pname seed <<< "$ps"
    id=$s--$pname${seed#-}
    [[ $seed == - ]] && id=$s--$pname
    pid_name=policy-$pname${seed#-}
    [[ $seed == - ]] && pid_name=policy-$pname
    if [[ ! -f "$work/$pid_name.wasm" ]]; then
      policy_part "$pname" "$seed" > "$work/$pid_name.part.wat"
      component "$pid_name" "$wit" random-host "$pol/policy-common.wat" "$work/$pid_name.part.wat"
    fi
    wac plug "$work/$s.wasm" --plug "$work/$pid_name.wasm" -o "$work/$id.wasm"
    wasm-tools validate "$work/$id.wasm"
    # the composition is deterministic: composing again gives the same octets
    wac plug "$work/$s.wasm" --plug "$work/$pid_name.wasm" -o "$work/$id.again.wasm"
    recompose=$(cmp -s "$work/$id.wasm" "$work/$id.again.wasm" && echo true || echo false)
    # the random import is satisfied by the policy: the runtime's own wasi:random is not used
    imports=$(wasm-tools component wit "$work/$id.wasm" | grep -E '^\s*import ' | sed -E 's/^\s*import //; s/;$//' | jq -Rsc 'split("\n") | map(select(. != ""))')
    trace "$work/$id.wasm" "$work/$id.1.json"
    trace "$work/$id.wasm" "$work/$id.2.json"
    replay=$(cmp -s "$work/$id.1.json" "$work/$id.2.json" && echo true || echo false)
    predicted "$s" "$pname" "$seed" | jq -Rsc 'split("\n") | map(select(. != ""))' > "$work/$id.pred.json"
    predicted_shared "$s" "$pname" "$seed" | jq -Rsc 'split("\n") | map(select(. != ""))' > "$work/$id.shared.json"
    sched=null schedule=null
    case $pname in
      zero) schedule='"every draw is 0"' ;;
      seeded) sched='"splitmix64-v1"'
        schedule='"draw k (from 0, per instance) = mix64(SEED + (k + 1) * 0x9E3779B97F4A7C15)"' ;;
      chaos) sched='"chaos-v1"'
        schedule='"h = mix64(SEED + (k + 1) * 0x9E3779B97F4A7C15), k the call counter (from 0, per instance); by h mod 8: 0..3 -> h, 4 -> 0, 5 -> 0xFFFFFFFFFFFFFFFF, 6 -> 5, 7 -> 6"' ;;
    esac
    jq -n \
      --argjson tools "$tools_json" --arg commit "$commit" --argjson dirty "$dirty" --arg date "$date" \
      --arg server "$s" --arg pname "$pname" --arg seed "$seed" --argjson sched "$sched" \
      --argjson schedule "$schedule" \
      --argjson sa "$(art "$work/$s.wasm")" --argjson pa "$(art "$work/$pid_name.wasm")" \
      --argjson ca "$(art "$work/$id.wasm")" --argjson recompose "$recompose" \
      --argjson imports "$imports" --argjson replay "$replay" \
      --slurpfile t1 "$work/$id.1.json" --slurpfile t2 "$work/$id.2.json" \
      --slurpfile pred "$work/$id.pred.json" --slurpfile shared "$work/$id.shared.json" \
      --argjson nr "$n_roll" --argjson np "$n_pair" --argjson ct "$curl_timeout" \
      --argjson st "$start_timeout" --arg others "${others[*]}" '
      ($t1[0]) as $t |
      def ok: if .path == "/roll" then .status == 200 and (.body | test("^[1-6]$"))
        elif .path == "/pair" then .status == 200 and (.body | test("^[1-6] [1-6]$"))
        else .status == 404 and .body == "not found" end;
      ([$t[] | select(ok | not)]) as $bad |
      ($bad | length == 0) as $must |
      ([$t[] | .body]) as $bodies |
      {
        schema: "silmaril.servers.runtime-evidence.v1",
        evidence: "runtime-test",
        note: "testing evidence, not a Lean proof",
        spec: "Silmaril.Servers.Examples.Dice",
        date: $date, git: {commit: $commit, dirty: $dirty},
        tools: $tools,
        server: $server,
        policy: {name: $pname, seed: (if $seed == "-" then null else ($seed | tonumber? // $seed) end),
          schedule_id: $sched, schedule: $schedule},
        artifacts: {server: $sa, policy: $pa, composed: ($ca + {recompose_identical: $recompose,
          imports: $imports})},
        bounds: {roll: $nr, pair: $np, other_paths: ($others | split(" ")),
          curl_timeout_s: $ct, start_timeout_s: $st, serve_runs: 2},
        trace: $t,
        checks: {
          must: {pass: $must, property: "/roll and each /pair component in 1..6; other paths 404 not found",
            violations: $bad,
            expected: (if $server == "dice" then "pass"
              elif $pname == "zero" then "pass" else "pass or fail (planted bug, revealed only by draws with x % 7 == 6)" end)},
          replay: {pass: $replay, identical_traces: $replay},
          may: {
            roll_values: ([$t[] | select(.path == "/roll") | .body | tonumber] | unique),
            pair_values: ([$t[] | select(.path == "/pair") | .body] | unique),
            roll_constant_across_requests: ([$t[] | select(.path == "/roll") | .body] | unique | length == 1),
            fresh_instance_per_request_prediction_matches: ($bodies == $pred[0]),
            shared_instance_prediction_matches: ($bodies == $shared[0])
          }
        }
      }' > "$out/$id.json"
    must=$(jq -r .checks.must.pass "$out/$id.json")
    rolls=$(jq -c .checks.may.roll_values "$out/$id.json")
    pairs=$(jq -c .checks.may.pair_values "$out/$id.json")
    fresh=$(jq -r .checks.may.fresh_instance_per_request_prediction_matches "$out/$id.json")
    shared=$(jq -r .checks.may.shared_instance_prediction_matches "$out/$id.json")
    printf '%-22s must=%-5s replay=%-5s fresh=%-5s shared=%-5s rolls=%s pairs=%s\n' \
      "$id" "$must" "$replay" "$fresh" "$shared" "$rolls" "$pairs"
    [[ $replay == true && $recompose == true ]] || status=1
    [[ $s == dice && $must != true ]] && status=1
    runs+=("$out/$id.json")
  done
done

# --- negative cases ---------------------------------------------------------------------------

# tool_obs CMD...: {exit, output} of a tool run (output truncated)
tool_obs() {
  local o e=0
  o=$("$@" 2>&1) || e=$?
  jq -nc --argjson e "$e" --arg o "${o:0:600}" '{exit: $e, accepted: ($e == 0), output: $o}'
}

# serve_obs COMPONENT [TIMEOUT] [N]: what `wasmtime serve` does: exits at startup (with its
# message), or listens; then the answers to N (default 2) GET / within TIMEOUT each (a second
# request shows whether a failure recurs per request)
serve_obs() {
  local c=$1 t=${2:-$curl_timeout} n=${3:-2} log=$work/neg.log rs i
  if start "$c" "$log"; then
    rs=$(for i in $(seq "$n"); do request / "$t"; done | jq -sc .)
    sleep 0.2
    stop
    jq -nc --argjson rs "$rs" --arg l "$(head -c 600 "$log")" '
      def out: if .curl_exit == 28 then "timeout" elif .status == 0 then "no-response"
        else "status \(.status)" end;
      {startup: "listening", requests: ($rs | map(.body |= .[0:80])),
        outcome: ($rs[0] | out), same_outcome_every_request: ($rs | map(out) | unique | length == 1),
        log: $l}'
  else
    stop
    jq -nc --arg l "$(head -c 600 "$log")" '{startup: "failed", outcome: "rejected at startup", log: $l}'
  fi
}

negs=()
# (a) a core module, not a component
neg_a=$(jq -nc --argjson v "$(tool_obs wasm-tools validate "$work/dice.core.wasm")" \
  --argjson w "$(tool_obs wasm-tools component wit "$work/dice.core.wasm")" \
  --argjson s "$(serve_obs "$work/dice.core.wasm")" --argjson a "$(art "$work/dice.core.wasm")" \
  '{case: "a", name: "core module (dice, not a component)", artifact: $a,
    expected: "wasmtime serve rejects it (it serves components only)",
    observed: {wasm_tools_validate: $v, wasm_tools_component_wit: $w, wasmtime_serve: $s},
    as_expected: ($s.startup == "failed")}')
negs+=("$neg_a")

# (b) an export named wasi:http/incoming-handler@0.2.12 of the wrong type
bw=$work/bad-wit
mkdir -p "$bw"
cp "$pol/negative/bad-handler.wit" "$bw/"
wasm-tools parse "$pol/negative/bad-handler.wat" -o "$work/bad-handler.core.wasm"
wasm-tools component embed "$bw" -w bad-handler "$work/bad-handler.core.wasm" -o "$work/bad-handler.embed.wasm"
wasm-tools component new "$work/bad-handler.embed.wasm" -o "$work/bad-handler.wasm"
neg_b=$(jq -nc --argjson v "$(tool_obs wasm-tools validate "$work/bad-handler.wasm")" \
  --argjson w "$(tool_obs wasm-tools component wit "$work/bad-handler.wasm")" \
  --argjson t "$(tool_obs wasm-tools component targets "$wit" "$work/bad-handler.wasm" -w dice-server)" \
  --argjson tc "$(tool_obs wasm-tools component targets "$wit" "$work/dice.wasm" -w dice-server)" \
  --argjson s "$(serve_obs "$work/bad-handler.wasm")" --argjson a "$(art "$work/bad-handler.wasm")" \
  '{case: "b", name: "export named wasi:http/incoming-handler@0.2.12 with handle: func(x: u32)",
    artifact: $a,
    expected: "well-formed (validate accepts, wit prints the wrong type); rejected by a type check against the world (component targets; wasmtime serve: no 200 from the handler)",
    observed: {wasm_tools_validate: $v, wasm_tools_component_wit: $w,
      wasm_tools_component_targets_dice_server: $t,
      control_dice_component_targets_dice_server: $tc, wasmtime_serve: $s},
    as_expected: ($v.accepted and $w.accepted and ($t.accepted | not) and $tc.accepted and
      ($s.startup == "failed" or ($s.requests | all(.status != 200))))}')
negs+=("$neg_b")

# (c) initialisation failure: the start function traps
component start-trap "$wit" dice-server "$root/tests/servers/wasi-http/common.wat" "$pol/negative/start-trap.wat"
neg_c=$(jq -nc --argjson v "$(tool_obs wasm-tools validate "$work/start-trap.wasm")" \
  --argjson s "$(serve_obs "$work/start-trap.wasm")" --argjson a "$(art "$work/start-trap.wasm")" \
  '{case: "c", name: "start function traps (initFail)", artifact: $a,
    expected: "no response from the handler: the failure is observed at startup or per request (initFail)",
    observed: {wasm_tools_validate: $v, wasmtime_serve: $s},
    as_expected: ($s.startup == "failed" or ($s.requests | all(.status != 200)))}')
negs+=("$neg_c")

# (d) a handler that never returns
component loop "$wit" dice-server "$root/tests/servers/wasi-http/common.wat" "$pol/negative/loop.wat"
neg_d=$(jq -nc --argjson v "$(tool_obs wasm-tools validate "$work/loop.wasm")" \
  --argjson s "$(serve_obs "$work/loop.wasm" "$loop_timeout" 1)" --argjson a "$(art "$work/loop.wasm")" \
  --argjson lt "$loop_timeout" \
  '{case: "d", name: "handler loops forever", artifact: $a, bound_s: $lt,
    expected: "timeout: no response within the bound (divergence itself is not observable)",
    observed: {wasm_tools_validate: $v, wasmtime_serve: $s},
    as_expected: ($s.outcome == "timeout")}')
negs+=("$neg_d")

printf '%s\n' "${negs[@]}" | jq -s --argjson tools "$tools_json" --arg commit "$commit" \
  --argjson dirty "$dirty" --arg date "$date" \
  '{schema: "silmaril.servers.runtime-evidence.v1", evidence: "runtime-test",
    note: "testing evidence, not a Lean proof", date: $date, git: {commit: $commit, dirty: $dirty},
    tools: $tools, negatives: .}' > "$out/negatives.json"
for n in "${negs[@]}"; do
  jq -r '"negative (\(.case)) \(.name): as_expected=\(.as_expected); serve: \(.observed.wasmtime_serve.outcome)"' <<< "$n"
  [[ $(jq -r .as_expected <<< "$n") == true ]] || status=1
done

# --- summary ----------------------------------------------------------------------------------

jq -s --argjson tools "$tools_json" --arg commit "$commit" --argjson dirty "$dirty" --arg date "$date" \
  --slurpfile neg "$out/negatives.json" '
  (map(select(.server == "dice-buggy"))) as $b |
  ([$b[] | select(.policy.name == "zero")][0].checks.must.pass) as $bz |
  ([$b[] | select(.checks.must.pass | not) | .policy | "\(.name) \(.seed // "")" | rtrimstr(" ")]) as $bf |
  (all(.[] | select(.server == "dice"); .checks.must.pass)) as $dice |
  (all(.[]; .checks.replay.pass)) as $replay |
  {schema: "silmaril.servers.runtime-evidence.v1", evidence: "runtime-test",
   note: "testing evidence, not a Lean proof", date: $date, git: {commit: $commit, dirty: $dirty},
   tools: $tools,
   runs: map({server, policy: .policy.name, seed: .policy.seed, must: .checks.must.pass,
     replay: .checks.replay.pass, roll_values: .checks.may.roll_values,
     pair_values: .checks.may.pair_values,
     fresh_instance_per_request_prediction_matches: .checks.may.fresh_instance_per_request_prediction_matches,
     shared_instance_prediction_matches: .checks.may.shared_instance_prediction_matches,
     composed_sha256: .artifacts.composed.sha256}),
   expectations: {
     dice_must_passes_under_every_policy: $dice,
     replay_identical_everywhere: $replay,
     dice_buggy_passes_under_zero: $bz,
     dice_buggy_fails_under: $bf,
     planted_negative_detected: ($bz and ($bf | length > 0)),
     negatives_as_expected: all($neg[0].negatives[]; .as_expected)},
   observation: "per-request instantiation: every /roll of a run is the same value, and each trace is the one predicted when each request gets a fresh policy instance (draws 0 and 1 only), and for the seeded and chaos policies not the one predicted for one instance shared by all requests; an observation of wasmtime serve, not a proof",
   ok: ($dice and $replay and $bz and ($bf | length > 0) and all($neg[0].negatives[]; .as_expected))}' \
  "${runs[@]}" > "$out/summary.json"
jq -r '"dice-buggy passes under zero: \(.expectations.dice_buggy_passes_under_zero); fails (expected, planted bug) under: \(.expectations.dice_buggy_fails_under | join(", "))"' "$out/summary.json"
[[ $(jq -r .ok "$out/summary.json") == true ]] || status=1
echo "evidence: $out"
exit $status

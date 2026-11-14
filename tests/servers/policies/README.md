# Runtime policies: a server with a modeled nondeterministic import

Status: **tested**, not proved. Everything here is testing evidence from one runtime
(`wasmtime serve`); none of it is a Lean proof.

`tests/servers/wasi-http-policies.sh` serves a wasi:http server that imports
`wasi:random/random@0.2.12` `get-random-u64`. Each run composes it with a host policy, a
component that exports that interface, and checks the responses.

## The servers

The dice server is specified in Lean as `Silmaril.Servers.Examples.Dice`. The WAT here
must match that spec exactly.

| path-with-query | response |
|---|---|
| `/roll` | `200`, content: the decimal digits of `(x % 6) + 1`, where `x` is one `get-random-u64` result read as an unsigned u64 |
| `/pair` | `200`, content: `"<a> <b>"`, from two draws in order, each `(x % 6) + 1` |
| anything else, or none | `404`, content: `not found` |

The comparison covers the whole path-with-query, so `/roll?x=1` gets `404`.

- `dice.wat` is the dice server.
- `dice-buggy.wat` is dice with a planted bug: `/roll` returns `(x % 7) + 1`. Only a draw with
  `x % 7 == 6` reveals the bug, as a roll of `7`.

Each server's core module is built from `random-import.wat`, `../wasi-http/common.wat`,
`dice-common.wat` and `dice.wat` (or `dice-buggy.wat`). The runner embeds it against the
`dice-server` world of `world.wit` and makes it a component. That world is the `server`
world of `../wasi-http/world.wit` plus `import wasi:random/random@0.2.12`.

## Host policies

A policy is a component of the `random-host` world: it exports `wasi:random/random@0.2.12`
and imports nothing. Its core module is `policy-common.wat` plus one of `zero.wat`,
`seeded.wat.in` or `chaos.wat.in`. For the `.wat.in` templates, the runner substitutes the
seed as a constant, so each `(policy, seed)` gives one fixed component with a recorded hash.

`wac plug server.wasm --plug policy.wasm` composes them into `server ∘ policy`. The composition
no longer imports `wasi:random`; each evidence record lists the remaining imports. So the
runtime's own randomness is never used.

`mix64` is the splitmix64 finaliser:

```
z := (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
z := (z ^ (z >> 27)) * 0x94D049BB133111EB
z ^ (z >> 31)
```

`γ` is `0x9E3779B97F4A7C15`, and `k` counts the calls of one instance, starting from 0.

| policy | `get-random-u64`, call `k` | host interpretation |
|---|---|---|
| `zero` | `0` | a pure deterministic host |
| `seeded SEED` (schedule `splitmix64-v1`) | the state starts at SEED and each call does `state += γ`, returning `mix64(state)`. So call `k` returns `mix64(SEED + (k+1)·γ)` | one deterministic host per seed. The set of seeds models the user-visible nondeterminism |
| `chaos SEED` (schedule `chaos-v1`) | `h = mix64(SEED + (k+1)·γ)`, which is call `k` of `seeded SEED`. Then, by `h mod 8`: `0..3` → `h`, `4` → `0`, `5` → `0xFFFFFFFFFFFFFFFF`, `6` → `5`, `7` → `6` | a stateful, effectful host that is still replayable. It favours extreme answers: `6` gives the buggy roll `7`, and `5` and `0xFF…FF` are boundary cases of the modulo |

`get-random-bytes` is outside the supported scope: every policy traps on it. The dice servers
do not import it. The policies do not implement `wasi:random/insecure` or `insecure-seed`
either.

## What the runner checks

The runner covers each server in {dice, dice-buggy} under each policy in {`zero`,
`seeded 1`, `seeded 42`, `chaos 7`}. Every run sends the same bounded sequence: 32 `/roll`,
8 `/pair`, then `/nope`, `/nope`, `/roll?x=1`, `/rolls` and `/`. Each curl request has a 5 s
timeout, and each server has 10 s to start listening. The startup probe only opens a TCP
connection, so it never invokes the handler.

- **must**: every `/roll`, and each component of every `/pair`, is in `1..6`. Every other path
  gets `404 not found`.
  - dice must pass under every policy.
  - dice-buggy must pass under `zero` and fail under at least one policy. It fails under
    `chaos 7`, which answers `6` on the first draw.
  - This failure is the expected outcome. It is a planted negative: passing the tests under
    one policy proves nothing.
- **replay**: the runner serves each `(server, policy, seed)` twice, from two fresh
  `wasmtime serve` processes, and the two traces must be identical. It also composes each
  pair twice, and the two compositions must be identical octet for octet.
- **may**: the runner records which values were observed. For example, `zero` only ever
  rolls `1`.

### Negative cases

Each negative case is an expected rejection, recorded in `negatives.json`:

- **(a) A core module instead of a component.**
  - `wasm-tools validate` accepts it, as a valid core module.
  - `wasm-tools component wit` rejects it, because it has no component type.
  - `wasmtime serve` refuses to start: "The serve command currently requires a component".
- **(b) An export named `wasi:http/incoming-handler@0.2.12` with the wrong type**
  (`handle: func(x: u32)`, from `negative/bad-handler.wit` and `negative/bad-handler.wat`).
  - `wasm-tools validate` accepts it. It only checks that the component is well formed.
  - `wasm-tools component wit` prints the wrong interface under the right name.
  - `wasm-tools component targets` against the `dice-server` world rejects it with a type
    mismatch for that export. The control run accepts `dice.wasm`.
  - `wasmtime serve` *starts listening* and then answers `500` to every request, logging
    "instantiation error: failed to convert function to given type".
  - So a matching export name is not a type check against the world. wasmtime 49.0.2
    checks the type only when it instantiates the component, once per request.
- **(c) A start function that traps** (`negative/start-trap.wat`).
  - The component validates.
  - `wasmtime serve` starts listening and answers `500` to every request, logging an
    instantiation error with a trap in `boom`.
  - This is the `initFail` observation, and it happens per request, not at startup.
- **(d) A handler that never returns** (`negative/loop.wat`).
  - No response arrives within the 3 s bound (curl exit 28), so the runner records a
    `timeout`.
  - Divergence itself is not observable; only the bounded timeout is.

## Lean counterparts

The same claims as Lean theorems are in `Silmaril.Servers.Examples.Dice` and
`Silmaril.Servers.Problems`, which arrive in the companion pull request
`servers/observational-refinement`:

- `dice_mustAll`: the must property holds under every stateful host.
- `buggy_not_mustAll`: the planted bug fails it under the host that draws `6`.
- `buggy_mustAll_zero`: the planted bug passes it under the zero host.
- `perRequest_roll_const`: a fresh instance per request answers every `/roll` alike.

`Problems.catalogue` marks each runtime check here as `runtimeTest` or `validatorCheck`, never
`proof`.

## Per-request instantiation (an observation, not a proof)

`wasmtime serve` makes a new instance of the composed component, and so of the policy, for
every request. The runs show this in three ways:

- Under every policy, all 32 `/roll` of a run return the same value.
- Each trace equals the one predicted when every request gets a fresh policy instance, so
  only calls 0 and 1 are ever reached. The runner computes this prediction with a bash
  model of the policies (`fresh_instance_per_request_prediction_matches`).
- Under `seeded` and `chaos`, no trace equals the one predicted if one instance served all
  requests in order (`shared_instance_prediction_matches: false`). Under `zero` the two
  predictions coincide.

As a result, a stateful policy can show its state only within one request. Here that means
the two draws of `/pair`. Whether the dice-buggy bug shows up depends on the first draw of
the seed. With `seeded 1` and `seeded 42` it does not show up (rolls `3` and `6`).

## Evidence records

Every run writes one JSON file to `build/servers-policies/evidence/`, or to `$EVIDENCE_DIR`
if set, along with `summary.json` and `negatives.json`. All of them use the schema
`silmaril.servers.runtime-evidence.v1` and contain `"evidence": "runtime-test"` and
`"note": "testing evidence, not a Lean proof"`. Each record contains:

- the runtime, `wasm-tools` and `wac` versions and binary sha256;
- sha256 and size of the server, policy and composed components;
- the policy name, seed and schedule;
- the bounds;
- the full request/response trace;
- the must/replay/may results;
- the date and git commit (with a dirty flag).

`evidence/` holds one representative set: `summary.json`, `negatives.json`, and the two
`chaos 7` runs. That set came from a clean checkout of the commit named in each record.

## Pins and reproduction

The runner uses these pinned release binaries (x86_64-linux):

| tool | version | archive | archive sha256 |
|---|---|---|---|
| wasmtime | 49.0.2 (pin of `../wasi-http-conformance.sh`) | `wasmtime-v49.0.2-x86_64-linux.tar.xz` | `a4d6e9e3a5a60f527cf7793d674c48930c80c2e8977995b8a275cad3254b9322` |
| wasm-tools | 1.263.0 | `wasm-tools-1.263.0-x86_64-linux.tar.gz` | `21c036c1740a0552124c79c6e2170cb61c5b016005671a6d5bc06cf642165431` |
| wac (`wac-cli`) | 0.12.0 | `wac-cli-x86_64-unknown-linux-musl` (a bare binary) | `7cd490edbd452221ef89e6750fc43eacc9b71b1242095eb577cb9a3bf0d3beda` |

They come from the GitHub releases of bytecodealliance/wasmtime, wasm-tools and wac. To
reproduce, put the binaries on `PATH` together with `curl` and `jq`, then run:

```
tests/servers/wasi-http-policies.sh
```

The runner also accepts these environment variables:

| variable | default |
|---|---|
| `PORT` | `8090` |
| `N_ROLL` | `32` |
| `N_PAIR` | `8` |
| `CURL_TIMEOUT` | `5` |
| `START_TIMEOUT` | `10` |
| `LOOP_TIMEOUT` | `3` |
| `WASMTIME_VERSION` | `49.0.2` (`any` disables the check) |

The script exits 0 with a `skip:` message when a tool is missing or wasmtime is not the
pinned version. Servers only listen on 127.0.0.1, and the script kills them on exit.

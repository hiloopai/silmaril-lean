# Compiled corpus replay execution

`make check` and `make process-check` explicitly execute the two unchanged
cJSON caller IO regression drivers through `run_compiled_replays.py`. Building
an executable does **not** execute its checks. These are finite observations,
never semantic proofs; no `#eval`, `native_decide` or cached pass is involved.
The original case matrices, negative tests, assertions and source files remain.

The runner always requests a fresh `lake build --wfail` of both targets, validates
the actual generated initializer/callback ABI and link inputs, then executes
both programs sequentially. It retains complete stdout/stderr, exit status,
source/generated-C/executable/link-response hashes and per-step resources under
`build/compiled-replay-results`. A failure stops the command with a nonzero
exit. Success still requires the original168/420 count summaries.

Both child streams are teed live to their normal output streams while retaining
byte-identical logs and hashes. No timestamps or compilation markers are added.
The existing CI parser reconstructs compile intervals from each genuine Lake
line's arrival timestamp minus its reported duration. Re-emitting a complete
build log after exit would shift these intervals and collapse their union; the
runner therefore drains and joins both output relays before reporting a phase
or starting the next one. Relay errors fail closed and stop the child group.
Focused tests use an in-memory logical clock and child acknowledgements to
check live delivery, the unchanged parser's interval union, and zero compilation
credit throughout runtime. Synthetic fixture lines never reach real CI output.

The CLI resolves sibling imports from its own repository directory, including
under Python `-P`/`-I`; it does not enable cwd/PYTHONPATH lookup or disable the
worker's safe-path behavior.

The ordinary Lean driver/import/object/toolchain dependencies belong to Lake.
The bootstrap C file is an actual `input_file` in `moreLinkObjs`, so Lake tracks
its content as a link input and compiles it during the normal link invocation,
retaining the experiment's C warning, optimization and hardening flags.
The planner/validator, runner, sampler and focused tests are additional named
Lake input dependencies; edits also select these targets through `make scope`.
Identical generated objects can remain reusable after a validator-only edit:
validation runs from the current Python source every time, before any replay.
No handwritten freshness manifest or previously passing executable bypasses
Lake or runtime validation.

The original drivers use `public meta import`/`public meta section`. Their
unwrapped generated native entry initializes only runtime imports and faults
on its first meta-import global access on the pinned toolchain. The external
bootstrap uses documented ELF `--wrap=main`, the real generated full initializer,
then unchanged generated `run_main` through Lean IO. No generated C, driver,
Core, global, result, header or runtime implementation is patched. All full
initialization occurs **after** the measured runtime starts. The native aliases
include this bootstrap in their normal Lake link. Compiler ABI drift or missing
link inputs fail closed; changed initializer symbols also fail linking.

Execution is sequential, with at most eight inherited CPUs and no increase to
an inherited tighter `LEAN_NUM_THREADS`. Build/replay children each have a
900-second deadline, preserving stricter outer job deadlines and inherited
cgroup/rlimit restrictions. Each measured process group has a32GiB sampled
aggregate descendant-RSS guard; sampler errors fail closed. Timeout, failure,
parent cancellation and normal exit clean up remaining children in that group.
Linux `Tgid` deduplication avoids counting sibling threads as separate processes;
distinct-process shared pages can still be counted more than once. Sampling
and affinity are **not** hard cgroup/physical-memory isolation.

Run the focused actual-Lake invalidation, ABI, cancellation, cleanup and sampler
regressions with the repository's pinned toolchain:

```sh
python3 -m unittest discover -s tools/corpus -p 'test_replay*.py'
python3 tools/corpus/run_compiled_replays.py
```

The tiny dependency fixture executes its own clearly separate test program. It
checks C/driver/import edits, validator trace invalidation, an unchanged no-op
build and failed initialization/linking. Its fresh, fixture-owned artifact
cache exercises both initial compilation and actual cached restoration; it
asserts dependency-key changes and program output rather than log verbosity. It is not an added corpus problem or
semantic proof. ABI and runtime-preflight regressions ensure rejection happens
before any replay binary can execute.

## Full observation comparison

Use an isolated checkout with the exact Lean/dependency pins. Record acquisition,
restore and imported-module preparation separately; the interpreted controls
need imported OLeans. The standalone measurement harness runs both interpreted
originals, builds the native targets, explicitly executes each native driver
twice, and times a no-op build:

```sh
python3 tools/corpus/benchmark_compiled_replays.py --out build/replay-measurement --audit
```

Its complete ordinary stdout/stderr and168/420 summary comparisons are not
full observation digests. `--audit` additionally creates instrumentation-only
copies under `build/corpus-replay-audit`, retaining every assertion and case.
Removing the instrumentation reconstructs each original exactly. The one source
negative-execution expression is named/logged once before its original match.
Interpreted/native audit programs both execute at runtime; complete transcripts
must match byte for byte, with168/420 records,3 missing-allocation negatives and
336 forged-pointer projection values. The optional audit aliases use the same
tracked bootstrap and ABI validation as ordinary execution. Instrumentation
costs are separate from ordinary-driver timings.

Source transcripts record terminal output; observed caller allocation/lifetime,
byte/provenance fields; private cleanup; registrations/output preservation; and
rejected projections. Enum/function preservation logs the original Boolean
comparisons, not raw table dumps. The machine transcript records registers,
flags/RIP/FS, mappings/key counts and every byte checked outside the existing
72-byte private frame. These follow existing diagnostic/currentLocation/private
observation limits; they do not establish arbitrary-continuation adequacy,
full-record source-memory equality or semantic refinement.

## Measurement limits

Record toolchain acquisition, dependency restore, module preparation, native
objects, C compilation/linking, full startup and execution. Bootstrap C compilation
is included in the ordinary Lake link invocation, not a separately timed phase.
Keep native dependency-object compilation distinct from pure final linking.
A warm no-op build or runtime is not a cold build. No cache is flushed; label
restored/built artifacts and filesystem pages honestly. Staged arithmetic is
not one end-to-end measurement or a CI acceptance result.

The standalone benchmark uses per-child32GiB `RLIMIT_AS`, unlike the pipeline
runner's sampled aggregate RSS guard. Neither is a hard aggregate cgroup claim.
Both preserve stricter inherited host/job restrictions; do not compare their
resource limits as identical. Complete per-step argv and logs remain available.

Existing timing accounting, original acceptance target, current CI budget and
historical failures remain unchanged. Build/link/startup/runtime output and costs
must remain visible under those rules. Local benefit does not certify a CI
pass; security analysis success does not certify vulnerability freedom.

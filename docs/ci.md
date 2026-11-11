# Continuous integration

`CI` is the automatic entry point. Small reusable workflows keep each check
readable. The [path filters](../.github/paths-filter.yml) select the checks; a
manual `CI` run selects all of them. Its optional `seed` input permits a cold
build; normal runs keep the automatic time limits. Draft pull requests run helper, probe and
development-environment checks, but defer the full Lean build until ready.

| Check | Work | Automatic timeout |
| --- | --- | --- |
| Lean and native | `make check` on what the diff can change, staged CLI smoke | 15 minutes |
| Nightly | The full `make check` on main | 15 minutes |
| LPS reality probes | Offline fixtures, 49 native probes, mutation/live tests | 5 minutes |
| Development environments | Docker and Nix cross-tool smoke, in parallel | 10 minutes each |
| CI helpers | Cache credential/path tests and timing tests | 2 minutes |
| CI | Require every selected check to pass | 1 minute |
| CI time budget | Fail separately when the attempt exceeds four minutes | 2 minutes |

`make check` builds the full Lean library and native tools with `--wfail`. It runs
the layout, process facts, header, SHA artifact, x86 catalogue and offline LPS
checks, then all 18 native release suites. These checks use one build tree.
Independent jobs run in parallel.

On main and nightly, `make check` runs in full. A pull request runs it on the Lake
targets `scripts/ci-scope.py --base HEAD^1` chooses: each changed module and every
module importing it, a module whose `include_str` or `include_bytes` file changed,
and a library whose `needs` input changed. The executables and the 18 release
suites run when the diff touches `tools/binaryen-lean/`, an executable root or a
release proof root. A change to `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, the `Makefile`, the scope script or `.github/` checks everything.
With no Lake target, the job installs no Lean and runs only the source checks.
The timing check waits for all selected correctness jobs. It includes their
setup, cache transfer, tests and publication, plus waits after the attempt
starts. GitHub's wait before `run_started_at` and final workflow teardown are
outside this measurement. Reruns use the current attempt's start time.

## Cache and first run

1. `make cache` restores the dependencies and this repository's packages from the
   shared Lake pool: main's build at `HEAD`, else at its nearest published
   first-parent ancestor. The pool is shared with every repository on the same
   platform, Lean version and archive tool. Lake keeps the artifacts in one
   artifact cache, so the build compiles only what changed since that commit.
2. Lake checks the current input traces. Cache presence never counts as a
   passing test, and all native regression suites still run.
3. After successful checks, every main push records its build of every
   `make check` target and publishes what the pool lacks. Only main can assume the
   writer role; every other run reads. Fork pull requests get no OIDC token: they
   build without the pool, which does not fit the automatic limit.

After a toolchain or archive-tool change no published build matches. Run **CI**
manually on **main** with **seed** checked: it builds cold with a 90-minute Lean
limit, runs all correctness checks, and publishes. Only this explicit manual mode
skips the four-minute timing check.

The public Linux runner has four CPUs and 16 GB RAM. `LEAN_NUM_THREADS=2`
limits Lake's worker pool; the native release suites run one per core.
Logs record available disk and memory, build-tree size and `time -v` results.
The latter reports the largest process RSS, not total concurrent memory.
Changed-main S3 publication remains inside the time budget and can cause it
to fail even when correctness passes.

Thomas owns the manual seed and timing helper. Remove the seed when the standard
Lean action supports main-only publication without it; remove the timing helper when
GitHub supplies a separate elapsed-time check that lets correctness finish.

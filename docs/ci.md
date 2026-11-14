# Continuous integration

`CI` is the automatic entry point. Small reusable workflows keep each check
readable. The [path filters](../.github/paths-filter.yml) select the checks; a
manual `CI` run selects all of them. Its optional `seed` input permits a cold
build; normal runs keep the automatic time limits. Draft pull requests run helper, probe and
development-environment checks, but defer the full Lean build until ready.

| Check | Work | Automatic timeout |
| --- | --- | --- |
| Lean and native | `make check` on what the diff can change, staged CLI smoke | 30 minutes on prove; 90 on main pushes and seed dispatches; 15 on fork pull requests |
| Nightly | The full `make check` on main | 15 minutes |
| LPS reality probes | Offline fixtures, 49 native probes, mutation/live tests | 5 minutes |
| Development environments | Docker and Nix cross-tool smoke, in parallel | 10 minutes each |
| CI helpers | Cache credential/path tests and timing tests | 2 minutes |
| CI | Require every selected check to pass | 1 minute |
| CI time budget | Fail separately when the attempt exceeds four minutes, not counting module compilation | 2 minutes |

`make check` builds the full Lean library and native tools with `--wfail`. It runs
the layout, process facts, header, SHA artifact, x86 catalogue and offline LPS
checks, then all 18 native release suites. These checks use one build tree.
Independent jobs run in parallel.

On main and nightly, `make check` runs in full. A pull request runs it on the Lake
targets that `make scope BASE=HEAD^1` (`cov-lake-cache scope`) chooses:
- each changed module and every module that imports it;
- a module whose `include_str` or `include_bytes` file changed;
- a library whose `needs` input changed.

The executables and the 18 release suites run when an executable's import closure
changed. These changes check everything:
- any Lake configuration or toolchain file;
- any other file that is not in the Makefile's `SCOPE_EXCLUDE` list (files that
  Lake never reads), such as `.github/`, the `Makefile` or `tools/binaryen-lean/`.
With no Lake target, the job restores nothing and runs only the source checks.
The timing check waits for all selected correctness jobs. It includes their
setup, cache transfer, tests and publication, plus waits after the attempt
starts. Time Lake spends compiling modules the run had to build does not count:
the check reads Lake's `Built … (duration)` lines from the job logs and reports
both the elapsed time and the compile time. Restores and no-op Lake walks
still count. GitHub's wait before `run_started_at` and final workflow teardown are
outside this measurement. Reruns use the current attempt's start time.

## Cache and first run

1. A same-repository pull request, a main push, a manual run and the nightly run check on hiloop's
   prove service: the job's small runner chooses the targets, and the worker restores
   from the shared Lake pool (main's build at the nearest published first-parent
   ancestor), builds them with `--wfail` and runs `make check` in the same checkout.
   The runner downloads no toolchain and no build; what the worker built goes to the
   pool. The pool is shared with every repository on the same platform, Lean version
   and archive tool, so the build compiles only what changed since that commit.
2. Lake checks the current input traces. Cache presence never counts as a
   passing test, and all native regression suites still run.
3. On every main push the Lake pool workflow (`lake-publish.yml`) builds and publishes
   main's commit on the prove worker (`hiloop-prove publish-build`), beside CI and outside
   its time budget: a recorded build of every `make check` target, with a seed for hosts
   that never installed silmaril-lean. The prove service refuses `workflow_run` tokens,
   so it cannot wait for CI; it publishes only a build that passes with `--wfail`. The
   runner assumes the one pool role, `gha-lean-cas`, which reads the client and puts the
   commit's source tree in the pool. Fork pull requests get no OIDC token: they build on
   a free runner without the pool, which does not fit the automatic limit.

After a toolchain or archive-tool change no published build matches. Run **CI**
manually on **main** with **seed** checked: it builds cold with a 90-minute Lean
limit, runs all correctness checks, and publishes. Only this explicit manual mode
skips the four-minute timing check.

A fork pull request's public Linux runner has four CPUs and 16 GB RAM.
`LEAN_NUM_THREADS=2` limits Lake's worker pool; the native release suites run one
per core.
Logs record available disk and memory, build-tree size and `time -v` results.
The latter reports the largest process RSS, not total concurrent memory.
A cold build's compilation does not count against the time budget.

Thomas owns the manual seed and timing helper. Remove the seed when the standard
Lean action supports main-only publication without it; remove the timing helper when
GitHub supplies a separate elapsed-time check that lets correctness finish.

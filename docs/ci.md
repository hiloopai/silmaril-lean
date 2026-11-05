# Continuous integration

`CI` is the automatic entry point. Small reusable workflows keep each check
readable. The [path filters](../.github/paths-filter.yml) select the checks; a
manual `CI` run selects all of them. Its optional `seed` input permits a cold
build; normal runs keep the automatic time limits. Draft pull requests run helper, probe and
development-environment checks, but defer the full Lean build until ready.

| Check | Work | Automatic timeout |
| --- | --- | --- |
| Lean and native | `make check`, staged CLI smoke | 15 minutes |
| LPS reality probes | Offline fixtures, 49 native probes, mutation/live tests | 5 minutes |
| Development environments | Docker and Nix cross-tool smoke, in parallel | 10 minutes each |
| CI helpers | Cache credential/path tests and timing tests | 2 minutes |
| CI | Require every selected check to pass | 1 minute |
| CI time budget | Fail separately when the attempt exceeds four minutes | 2 minutes |

`make check` builds the full Lean library, native tools, release proof roots and
process theorem roots with `--wfail`. It runs the layout, process facts, header,
SHA artifact, x86 catalogue and offline LPS checks, then all 18 native release
suites. These checks use one build tree. Independent jobs run in parallel.
The timing check waits for all selected correctness jobs. It includes their
setup, cache transfer, tests and publication, plus waits after the attempt
starts. GitHub's wait before `run_started_at` and final workflow teardown are
outside this measurement. Reruns use the current attempt's start time.

## Cache and first run

1. Restore `.lake` from GitHub's cache archive. This downloads and extracts an
   archive onto the runner disk; it is not an attached persistent volume.
   Its key includes the runner OS and
   architecture, exact toolchain/dependency/configuration hashes, and commit.
   A compatible earlier main snapshot is a fallback.
2. On a disk miss, fetch public dependency artifacts and try the optional S3
   cache. The shared Covalence tool uses the existing main-only writer environment. Pull
   requests can use a read key or public URL if configured; neither is required
   for the disk cache. A cache miss still runs the correctness checks.
3. Lake checks the current input traces. Cache presence never counts as a
   passing test, and all native regression suites still run.
4. After successful checks, canonical main publishes to S3 and saves a new disk
   snapshot. An exact disk hit avoids both writes. Pull-request events never publish.
   GitHub's branch-scoped cache prevents a pull-request cache from replacing the
   default-branch entry.

Run **CI** manually with **seed** checked to build a missing cache. This runs
all correctness checks, with a 90-minute Lean limit, then saves the disk snapshot
on the triggering branch. Only this explicit manual mode skips the four-minute
timing check. An ordinary manual `CI` run on the same branch then measures the
full warm path, including the timing check. This works before a PR is merged.

Manual seeds in the canonical repository can write only the triggering ref's
GitHub cache; they cannot create an entry visible to main from another branch.
They do not receive S3 writer access. After this workflow reaches main, seed
**main** once if it has no compatible cache. Repeat after a toolchain change or
eviction if an automatic 15-minute job cannot finish cold. Subsequent main
pushes refresh disk and S3 snapshots. No scheduled cold builds are added.

The public Linux runner has four CPUs and 16 GB RAM. `LEAN_NUM_THREADS=2`
limits Lake's worker pool; native suites retain their existing two workers.
Logs record available disk and memory, build-tree size and `time -v` results.
The latter reports the largest process RSS, not total concurrent memory.
The first seeded GitHub run must establish total memory, disk and transfer
costs before treating this setup as a measured four-minute solution. Native
toolchain cache entries can be several GB; GitHub cache eviction is expected.
Changed-main S3 publication remains inside the time budget and can cause it
to fail even when correctness passes.

Thomas owns the disk-cache layer, manual seed and timing helper. Remove the
disk cache and seed when the standard Lean action supports the same main-only
publication and warm restore without them; remove the timing helper when
GitHub supplies a separate elapsed-time check that lets correctness finish.

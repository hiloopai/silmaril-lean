# Compiled corpus replay measurement

The optional `ci_corpus_cjson_array_item_core` and
`ci_corpus_cjson_array_item_machine` targets compile the existing IO regression
drivers without editing their source. Building an executable does **not** run
its checks. Their `main` functions must run explicitly at runtime. These are
finite observations, never semantic proofs; no `native_decide` is involved.
The normal `make check` selection and CI accounting are initially unchanged.

Use the repository's exact Lean/dependency pins and an isolated checkout.
Restore/build the drivers' imported modules first and record that setup cost;
the initial interpreted commands need their imported OLeans. Do not prebuild
the optional executables when measuring their initial build cost:

```sh
python3 tools/corpus/benchmark_compiled_replays.py --out build/replay-measurement --audit
```

The harness runs both unchanged interpreted drivers, times the native build,
runs each native driver explicitly twice, and times a no-op build. If executable
or object artifacts were already restored/built, label that build as warm. The
combined native-build step does not separately identify C generation, C compilation
and linking: measure those facets separately when those costs are needed. It compares
complete stdout/stderr bytes and the existing168/420 case-count summaries. These
summaries alone are not full observation digests.

`--audit` additionally generates separate instrumentation-only copies under
`build/corpus-replay-audit`. It retains the source assertion bodies and case
matrices and logs each case's actual observed values. For the one source
negative-execution expression, its pure result is named and logged before the
unchanged match, without evaluating it twice. The generator checks that removing
this instrumentation recovers the original source exactly. Both interpreted
and native instrumented drivers run at runtime, with no added `#eval` or proof
work. Their full transcripts must match byte for byte, with168/420 case records
and3 source missing-allocation negatives. The two forged-provenance projections
per source case are also recorded. All original assertions/negative checks stay.

The source transcript records actual terminal output, observed caller
allocation/lifetime/byte/provenance fields, private allocation cleanup,
registrations/output preservation and rejected projections. It follows the
existing observation domain: it does not establish arbitrary continuation
unobservability or full-record source-memory equality. The machine transcript
records registers/flags/RIP/FS, mappings/key count and every byte checked outside
the existing72-byte private frame. Instrumentation times are reported separately
and must not be used as ordinary-driver speed measurements.

Outputs include per-step argv, wall/user/system time, `wait4` peak RSS, faults,
context switches, complete stdout/stderr files and SHA-256 digests. By default,
children use eight available CPUs and a32GiB `RLIMIT_AS`; this is a per-process
virtual-address limit, not an aggregate physical-memory/cgroup limit. The host's
actual CPU count and memory are recorded. Peak `wait4` RSS is not aggregate
concurrent process-tree RSS. Do not infer isolation/resource equivalence beyond
these recorded limits.

Dependencies, native objects, executable pages or filesystem caches may already
be warm; no cache is flushed. Record toolchain acquisition, dependency restore,
C generation/compilation/linking, service/client overhead and actual run time
when assessing end-to-end benefit. A no-op build or warm run is not a cold build.
Driver hashes are recorded so revisions remain distinguishable. Native binary
size and repeated build costs matter as well as run time.

These measurements do not certify a CI budget pass. Keep the unchanged timing
accounting and original acceptance target distinct, retain historical failures,
and validate net benefit locally before starting expensive full CI. No tests,
input domains, assertions, security scans or timeouts should be weakened.

`replay_measure.py` provides a separate sampled descendant-RSS diagnostic with
an unchanged default 32GiB guard. It counts each Linux `Tgid` once, even when a
proc implementation lists thread IDs as children. Distinct processes may still
share pages, so their summed RSS is conservative; sampling is not hard aggregate
memory isolation. A sampler error stops the measured process group. Run its
focused regression with:

```sh
python3 -m unittest discover -s tools/corpus -p test_replay_measure.py
```

The direct optional aliases are experimental: on the exact pinned toolchain,
the original drivers' `public meta import`/`public meta section` generates a
native entry that initializes runtime imports only. The Core alias currently
faults at its first access to a global from a meta import. A successful native
build is therefore not a successful runtime check. Without
`--full-initialization`, the measurement stops on that failure. A direct
alias cannot supply a passing runtime comparison; use the separate initialized
experiment below to obtain native outputs and full observation transcripts.

An isolated full-initialization experiment is available with:

```sh
python3 tools/corpus/benchmark_compiled_replays.py --out build/replay-measurement --full-initialization --audit
```

`replay_native_bootstrap.py` inspects the exact generated C for the real full
module initializer and `run_main` callback, rejecting a changed ABI. It emits a
plan; the harness separately times planning, bootstrap C compilation and each
link. The optional external C entry uses the supported ELF linker
`--wrap=main` option and the compiler's full initializer before the unchanged
compiled IO callback. It neither edits generated driver C nor populates any
Core/global/result by hand. All initialization runs after the measured process
starts. The initialized binaries have separate output paths; the original
aliases remain intact. Plans record bootstrap/generated-C/link-response hashes.

A successful startup or matching PASS summary is still insufficient: require
all original assertions, negative cases and complete observed-field transcript
counts/digests to match interpreted controls. Assess build-plus-run benefit
with the recorded cache conditions and setup
costs. Pipeline integration needs a separate review of dependency tracking,
runtime selection and resource limits; the measurement aliases do not change it.

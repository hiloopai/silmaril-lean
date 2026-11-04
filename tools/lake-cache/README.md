# Shared Lake cache helper

Python 3.11+, curl 8+, Git and Lean 4.37 are required. No Python packages are installed.

```sh
python3 tools/lake-cache/lake_cache.py dependencies
python3 tools/lake-cache/lake_cache.py build --repository example/library --record build/cache -- MyLibrary
# Run the repository's other checks here. Publish only if they succeed.
python3 tools/lake-cache/lake_cache.py put --repository example/library --record build/cache
python3 tools/lake-cache/lake_cache.py get --repository example/library
```

`build` runs the required `lake build --wfail` and records its native output mappings.
Use it in place of the existing build when publication is needed. `put` never builds.
It accepts only a successful build receipt for the current Git revision, native platform,
Lean version, dependency pins, package and CI run. A failed build removes the receipt.
The caller must keep its remaining correctness checks before the publication step.
This receipt is bookkeeping in a trusted runner, not a proof certificate.

Set `LAKE_CI_ENDPOINT` to an HTTPS S3 origin, `LAKE_CI_BUCKET`, `LAKE_CI_PREFIX`,
`LAKE_CI_REGION` (default `auto`), and `LAKE_CI_KEY` (`access-id:secret`). This uses
direct curl AWS SigV4 authentication; no service or edge-auth hop. Keys go through
stdin, never command arguments. S3 and R2 must support paginated ListObjectsV2 for
the configured prefix. For temporary AWS credentials also set `LAKE_CI_SESSION_TOKEN`.
An inventory failure stops publication and reports the cause.
It does not silently treat an incomplete inventory as a cache hit.

Keep writer keys in a protected main-only CI environment. Give restore steps only
read credentials, or no credentials for a public endpoint. Do not pass writer keys
to PRs. The CLI restricts publication to main pushes/manual runs in the specified
repository; server-side credentials and environment policy enforce writer trust.

Publication lists the scoped remote objects, checks their sizes, uploads missing
artifacts in batches of at most 16 concurrent transfers, then uploads the complete
mapping and finally `main-latest`. It reports artifact count, reused count, uploaded
bytes, metadata bytes, inventory time and transfer time. Missing remote blobs are
repaired on the next publication. Object existence is not an integrity proof: native
Lake checks downloaded content hashes and matches the current build inputs.

`get` reads the latest successful mapping in the exact scope and delegates downloads
and content validation to Lake. A missing pointer is a cache miss. Other failures
are reported; callers may make optional cache fetching advisory and continue with
the normal checked build. Disk mounts and GitHub cache snapshots remain caller policy.

Use `--package NAME` for a dependency's mappings. Lake records one package per build;
record each package explicitly before tests/publication. Package names are part of
the remote scope. Native outputs are separated by OS, architecture and Lean build.

Consumers pin the public release's commit and fetch only `lake_cache.py` and
`storage.py`, retaining them under ignored `.lake` state. Development happens in the
development repository; public promotion carries the same helper files. Updating
the pin distributes a fix without copying its implementation into each consumer.

Thomas owns this module. Delete the publication/transport implementation when Lake
supports authenticated S3 reads, skip-existing uploads and transfer byte reporting.
Delete `dependencies` when CSLib supports the pinned Lean release and the normal
Mathlib cache command supplies these outputs.

## Test

```sh
python3 -m unittest discover -s tools/lake-cache -v
```

Tests build real small Lean modules, serve native artifacts over a local HTTPS S3
test server, and restore with native Lake. They cover unchanged/edited builds,
deleted blobs, pagination, interrupted uploads, stale receipts, invalid proofs and
namespace validation. Local server timings measure implementation overhead only;
they are not R2 throughput or full repository CI measurements.

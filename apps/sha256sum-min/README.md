# Recovered original `sha256sum-min` source

These are the exact recovered source/build inputs for the existing Lean target
`Silmaril/Apps/Sha256sum/Binary`: GCC 13.3.0 `-O2` driver with the pinned Clang
18.1.3 `-O2` compression bytes. The original executable is 35,512 bytes,
SHA-256 `22fa6345cc5bed08f07d4d5a0836885118259a73402470e4d7f7a7a81ad42817`.
This is distinct from the smaller `apps/sha256-cli` filter and its O3 variants.

Recovered unchanged from the research host:

- `src/`: original C, startup/syscall assembly, generated GNU text/errno tables,
  compression assembly and pilot hex.
- `scripts/build.sh`, generators and pilot byte checker: original scripts.
- `inputs/xc_sha256.c`: exact retained Silmaril input used for the GCC-compress
  sibling; the original input commit is `76eb80d5cb83e0396af429f1631b350cb898805e`.
- `historical-manifest.json`: untouched original build/source/tool-version
  receipt. Every recorded source, generator and input hash was rechecked.

The original recipe takes a Silmaril checkout and reads its `origin/main`:

```sh
bash apps/sha256sum-min/scripts/build.sh /path/to/historical-checkout
```

That ref must resolve to the recorded input commit. The generated
`src/gen_tables.h` is part of the frozen program: its help/version/strerror
bytes came from the original GNU/glibc environment. Regenerating it on a new
host can change observable behavior.

`build.py` is a new offline wrapper, separate from the historical recipe. It
verifies every historical identity, reads the original recipe's literal flags,
uses frozen local inputs and preserves the generated tables:

```sh
python3 apps/sha256sum-min/build.py --verify-only
python3 apps/sha256sum-min/build.py --cc gcc --out /tmp/sha256sum-reproduced
```

Building requires actual x86-64 GCC 13.3.0 and GNU binutils 2.42. The output
directory must be fresh. A build writes both executables and a new receipt
with current compiler/component hashes, commands, pilot-byte checks and exact
historical-hash comparisons. New executable hashes do not establish the
historical compiler executable's identity; those hashes were not recorded.

An equivalent frozen-input recipe ran wholly on the original Linux host,
without any source upload. It rebuilt **both original binary hashes exactly**
in 0.65 seconds, passed the native compression/relocation/K-byte check, and
returned the expected GNU-format stdin records for empty input and `abc`.
The local wrapper's identity checks and compression regeneration passed;
changed source, table, recipe, wrapper input and pilot-hex controls rejected.
The full new wrapper was not executed on this macOS host, whose `gcc` is Clang.
The initial attempt to invoke the historical recipe through a temporary
shared Git clone failed on a missing promisor object before compilation.

Exact source observations, reproduction commands/tool hashes, runtime outputs,
costs and limitations are retained in
[`recovered-provenance.json`](../../scripts/sha256sum/recovered-provenance.json).
This closes the missing-source/build-recipe boundary. It adds no source-to-
machine, driver/ABI, prefix-safety or completed-result theorem. Existing
compression/image proofs remain separate from native build/runtime evidence.

# ELF byte-grounded region and CFG views

The project explorer has separate **regions** and **graph** tabs for ELF files.
They consume `elf/regions/SLUG.json` emitted by `elf-pages`, alongside the
[ELF reader's existing pages](elf-reader.md). The viewer, exporter, byte
certificates and conditional execution theorem are in this repository.

## Two independent proof dimensions

`Machine.Region.X86.CFG.Row.Valid` is an intrinsic relation on a byte window,
its virtual base address, decoder fuel, instruction listing, entry, edge list
and declared outward labels. It requires:

1. The existing canonical `X86.Ext` decoder consumes the whole window and
   produces exactly the listing.
2. Calls and returns are absent in this direct-transfer subset.
3. Entry is an instruction start; the window ends strictly below `2^64`.
4. Edges equal all named decoded successors, extensionally.
5. Declared outward labels equal the targets of actual edges whose targets are
   not instruction starts of this listing.

The definition mentions no machine execution, memory, function partition,
semantic region validity or concurrent interference. Its byte range is ordered
and half-open; its graph support consists of instruction starts, not every byte
in that range. Edge and exit list order and duplication do not matter to
certification. `edges_iff` and `exits_iff` characterize this wiring directly.
`CFG.View` optionally projects a row to the existing abstract `Tree.FlatCFG`,
proving source closure, entry membership and the outward-edge characterization.
This projection retains every successor independently of any dominance tree.
Branches can have statically possible but semantically unreachable edges.
The certificate is exact for decoded syntax, not exact for reachable exits.

`Elf.Region.CFG.Valid file row` separately pairs that relation with
`Elf.CodeAt file row.code.base row.code.bytes`. The checked ELF reader supplies
a read-only executable `PT_LOAD`, translating the base-relative ELF VA to a
file offset, and a kernel read binds the literal bytes to the included file.
This does not assert that a loader mapped it or that any execution reaches it.
A PIE's base-relative ELF VA is distinct from its runtime address after load
bias; loading/relocation must be supplied before applying runtime results.

These are certificates outside the [abstract positive-rule region lattice](region-lattices.md).
A CFG row does not assert structural single entry: incoming transfers from
outside the selected window remain an independent boundary obligation.

## Execution and interference contract

`CFG.retirement_edge` connects an intrinsic certificate to one actual retired
step of the repository's handwritten `X86.Ext` machine. It reuses the existing
`listing_step` fetch/decode theorem; it does not introduce machine semantics.
It requires the exact window to satisfy `Region.LoadedIn`, including executable
fetch and byte contents. All nonretirement outcomes stay distinguished halts;
normal-edge coverage establishes neither progress nor absence of faults, traps,
undefined conditions or stuckness. There is no syscall opcode in this Ext
subset. Calls/returns are rejected rather than interpreted as call fallthrough.
Unknown/noncanonical instructions cause decoding rejection.

`ExecutionContract row Ambient` packages the optional operational context:

| Field / premise | Required meaning |
| --- | --- |
| `focus` | Select the modeled thread's registers and memory from an ambient state |
| `invariant`, `loaded` | Every invariant state fetches the window's exact immutable executable bytes |
| `thread`, `thread_step` | Each observed thread step refines an actual `Ext.step` retirement |
| `thread_preserves` | Thread steps preserve that invariant |
| `environment`, `environment_preserves` | Interference preserves the same executable-code and ambient invariant |
| `environment_pc` | Environment steps leave the focused program counter unchanged |

The environment may change other data only within this contract. Its abstract
steps can summarize interference; no hardware memory model, race-freedom,
fairness, atomicity of a hardware instruction, or unconditional multithread
adequacy theorem is supplied.

`interleaving_sound` proves every normal first exit of these thread/environment
interleavings has a declared outward label. Environment steps stutter at the
focused PC, so they introduce no outward edge. `semantic_valid` additionally
requires a nonempty admitted domain, every admitted state at the row entry,
and invariant admission. This supplies the semantic region predicate without
defining regions as partitions into locally valid basic blocks. It still proves
no termination or exact-exit reachability.

The existing ELF placement theorem in `Elf.Region.X86` obtains `LoadedIn` from
an actual `LPS.ELFImage.parse` and `ImageLoaded` witness. The staged ELF reader's
`CodeAt` and that loader parser are different interfaces: this development does
not prove their parser-equivalence or automatically identify a staged code
window with a loaded segment. To discharge the concrete file's execution
premises, provide that identification, the runtime load bias, admitted thread
state/frame and a preserved code/interference invariant.

## Actual corpus scope

The source is `examples/dyn/pinned/hello-gcc`, the checked-in GCC 13.3 `-O2`
hello executable, dynamically linked against glibc 2.39. Its exact bytes are
pinned by SHA-256:

```text
6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7
```

| Selected ELF VA window | Bytes | Decoded instructions | Declared outward labels |
| --- | --- | --- | --- |
| `[0x10be, 0x10c3)` | `48 39 f8 74 15` | `cmp rax,rdi`; `je` | `0x10d8`, `0x10c3` |
| `[0x1160, 0x1169)` | `f3 0f 1e fa e9 77 ff ff ff` | `endbr64`; direct `jmp` | `0x10e0` |

Both windows have kernel-checked byte and CFG certificates. The measured
selection denominator is **2 selected windows, 4 listed instructions, 14 bytes
of the file's 265-byte `.text`**; `selected_coverage` checks these counts and the
section size. There is no whole-file instruction denominator or corpus-wide
success-rate claim. The other six ELF-page corpus files have no region/CFG rows
in this slice.

The examples reject a missing conditional edge, modified bytes with the old
listing, and a return given an empty direct CFG. They accept permuted exit
order. Two extra stated rows demonstrate identical data without attached proof
provenance and an intentionally incomplete alternative. These are labeled
comparison examples, not inferred additional corpus decompositions.

## Export and viewer evidence

The runtime exporter imports row **definitions**, not their theorem root.
After the root is built it dynamically imports `HelloGcc.Regions.Thms`, reads
each theorem's type, requires `Elf.Region.CFG.Valid` with the exact file and row
constants, checks its axioms, and records its source, statement and dimensions.
Unrecognized claims, a different file or row, and unsupported axioms fail export.
Native acceptance is only a consistency check, never the certificate source.

The serialized provenance is a `RegionProvenance` sum, with `stated` and
`certifiedByteCFG` cases. Browser badges require matching checked evidence,
row ID, image hash and claim dimensions; a status label alone is insufficient.
The browser trusts the checked exporter data; it is not a Lean proof checker.
`elf-pages --verify` regenerates all data and rejects modifications, including
edge tampering, promotion of stated provenance, or removal of CFG evidence.

The region table shows explicit half-open VA and file ranges, instruction-start
support, entry/exits, byte values and theorem provenance. Its comparison uses
edges at **shared sources**; omitted sources are coverage differences. Different
supports have different boundaries, so their exit sets are not blindly compared
as a contradiction. Data equality does not transport a certificate. A missing
certificate remains unknown even when the native consistency checker accepts
or rejects a candidate.

The graph tab displays the full outgoing adjacency, including loops, parallel
serialized edge rows and cross edges. Internal vertices, entry and declared
exits have separate roles. A property table distinguishes the directed row
multigraph, extensional directed relation, and undirected simple projection.
The last drops direction, loops and multiplicity. All counts and layouts are
browser observations. No dominator tree is inferred: immediate dominance needs
rooted reachability, an explicit exit policy and a separate witness.

Existing ELF-part coverage and the unverified objdump listing keep their own
meanings. A CFG certificate does not silently upgrade raw byte coverage or
certify objdump's text. Viewer row data is limited to the JavaScript-safe integer
addresses of these fixtures; a future arbitrary-64-bit schema needs string or
big-integer addresses throughout the existing ELF exporter/viewer.

## Reproduction and boundaries

```sh
lake build --wfail \
  Silmaril.Elf.Staged.Pinned.HelloGcc.Regions.Examples.Thms \
  Silmaril.Machine.Region.X86.CFG.Semantic.Thms \
  Silmaril.Machine.Region.X86.CFG.View.Thms
make elf-check
make project-tool
node --test tools/silmaril-project/tests/explore/*.test.mjs
make pages
node tools/silmaril-project/tests/explore/elf.mjs _site /tmp/elf-shots
```

`make elf-check` builds the dynamic certificate roots and runs exporter
regeneration/tamper tests. The browser test checks both old ELF views and the
new region/graph tabs on generated data. Rust/toolchain versions follow the
project's CI; no correctness check or timing budget is relaxed.

| Additional integration | Evidence still required |
| --- | --- |
| Concrete file execution | Loader/staged-reader window identification, runtime bias, admitted states and executable-code invariant |
| Wider direct CFG coverage | Additional selected byte windows or a declared corpus and a measured decoder/recognizer denominator |
| Call/return edges | Valid call summaries, first-return/resumption and continuation/frame proofs; no inferred fallthrough |
| Operational effects | Instruction/call/syscall event adequacy and halt policy, separate from normal-edge coverage |
| Dominator/structured views | Reachability and dominance/shape witnesses for the chosen graph and exit policy |
| Nested Wasm maps | Per-body instruction-to-byte validation with structured nested spans; unrelated to these ELF certificates |

The [complete function-extent guide](elf-complete-functions.md) adds a checked
whole symbol extent, with explicit external-tail and RET policy, and a measured
seven-file candidate inventory. It distinguishes native discovery from proofs.

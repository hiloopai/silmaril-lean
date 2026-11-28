# ACL2 x86isa ingestion scope (C1)

The target is the logical machine in ACL2 **8.7**, released March 23, 2026, at
`bc6f4f49e81a0711214a8d91f0d06e0e084d2204` (Git tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`). The release contains the system and
the Community Books in the same tree. Here `:dir :system` resolves into that
tree's `books/`, while ACL2 primitives and initial world come from the system.
[Official release](https://www.cs.utexas.edu/users/moore/acl2/),
[release commit and books](https://github.com/acl2/acl2/tree/bc6f4f49e81a0711214a8d91f0d06e0e084d2204).

## Entry books and coverage

Book paths are relative to `books/projects/x86isa/`.

| Entry book | Scope |
| --- | --- |
| `machine/x86.lisp` (`make model`) | Executable logical model. `X86ISA::X86-FETCH-DECODE-EXECUTE` is the step and `X86ISA::X86-RUN` iterates it with a count, stopping on `FAULT` or `MS`. This is the ingestion root. |
| `tools/execution/top.lisp` (`make tools`) | Simulation interface, including executable loaders, initialization, instrumentation and raw runtime overrides. It reaches the machine root through `instrument/top`. |
| `top.lisp` (`make top`) | Project bundle including `doc`, execution tools and examples, proof utilities, virtualization, save/restore and experimental `machine/new-decode`. `proofs/top` is commented out. |

The root includes the instruction definitions, legacy opcode maps, VEX/EVEX
dispatch, prefixes, CPUID and interrupt handling. The ingestion boundary
includes the machine state, segmentation, application and system memory views,
paging and TLB, integer, SIMD and floating-point submodels, and the upstream
halt, fault and unsupported cases. Preserve the upstream protected,
compatibility and 64-bit modes and their partial coverage. Real-address,
virtual-8086 and SMM are outside the documented model. A dispatch entry or
catalogue listing alone does not establish that an instruction is implemented.
[Machine root](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/x86.lisp),
[instruction root](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/instructions/top.lisp),
[modes](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/modes.lisp),
[execution tools](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/tools/execution/top.lisp),
[project root](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/top.lisp),
[bundle contents](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/doc.lisp).

## Dependency inventory

The [inventory tool](../../tools/acl2-x86isa/inventory.py) uses upstream
`cert.pl --makefile-only --smakefile` for Make dependencies. It records the
tool's explicit dependency map, source and other files, and reported feature
sets with paths relative to `books/`. Counts include each root. “Other books” means outside
`projects/x86isa/`, including `projects/execloader`, XDOC, STD, FTY, bitops,
records, arithmetic and RTL books. Linux x86-64 results used SBCL 2.5.2,
GNU Make 4.4.1 and Perl 5.40.1.

| Root | Cert targets | x86isa / other books | Sources (`nil` / `t` inputs) | Other inputs |
| --- | ---: | ---: | ---: | ---: |
| `machine/x86` | 1,030 | 109 / 921 | 1,163 / 1,165 | 7 |
| `tools/execution/top` | 1,081 | 115 / 966 | 1,224 / 1,226 | 11 |
| `top` | 1,131 | 160 / 971 | 1,287 / 1,289 | 15 |

- **Make and certification.** A literal `include-book` scan is a lower bound on
  discoverable dependencies and may list an inactive branch. `cert.pl` adds
  per-book `.acl2` or directory `cert.acl2` setup, `ld` from setup files,
  `include-events` / `include-src-events` / `loads`, `depends-on` comments and
  `.certdep` inputs, and recognizes certification directives. Implicit Make
  rules and the host toolchain are additional inputs. For example,
  `machine/cert.acl2` imports the sharp-dot constants and declares `:utils`.
  The model Make graph includes ACL2 exports, the ground-zero theory, internal
  records and raw Lisp files. The tool scans a known subset of source syntax.
  Includes split across lines or generated at event time can escape it.
  [Upstream cert.pl](https://github.com/acl2/acl2/blob/8.7/books/build/cert.pl),
  [machine setup](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/cert.acl2).
- **Conditional and generated.** Reader feature tests (`#+` / `#-`),
  `cert_param` restrictions, and build-time world queries are distinct.
  `X86ISA_EXEC=t` on Linux adds Make's C shared object plus two sources,
  `machine/syscalls.acl2` and `machine/x86isa_full_exec_support.lisp`. The
  generated `ld` defines a marker that changes the `make-event` expansion in
  `syscalls.lisp`. The `depends-on` comment for the raw syscall Lisp appears
  even in the `nil` scan. Upstream documents full syscall execution with
  Clozure CL's FFI. The `t` inventory covers Linux Make inputs only.
  The execution-tools book separately includes raw random and undefined-value
  overrides with `:other-non-det` and `:undef-flg`.
  [Makefile](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/Makefile),
  [conditional syscall events](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/syscalls.lisp#L1118).
- **Certificate and live world.** The `--certified` mode reads ACL2's
  certificate pre-alist (portcullis world) and post-alist (includes encountered
  during certification, with local-only entries marked), then records the
  visible includes from a fresh image. These are root records. A book may be
  visible via one route and local along another. Local proof and expansion
  support can affect admission even if it disappears from the public world.
  The manifest retains per-row trust tags and skip-proof and axiom annotations
  (`NIL`, `T`, `?`); these describe ACL2's bookkeeping. A book-level closure
  also includes macros, documentation and proof libraries. The logical
  function and constraint closure has to be derived from the translated events.
  [ACL2 certificate format](https://github.com/acl2/acl2/blob/8.7/other-events.lisp#L12965).

In the certified SBCL `nil` profile, pre/post and live counts below are
deduplicated by source path. The visible certificate names matched each live
world. All recorded pre/post names were present in the corresponding Make
target list.

| Root | Pre/post books | Live books | Pre/post outside live | Make targets outside root records | Root expansion entries |
| --- | ---: | ---: | ---: | ---: | ---: |
| `machine/x86` | 1,027 | 293 | 734 | 3 | 11 |
| `tools/execution/top` | 1,073 | 321 | 752 | 8 | 4 |
| `top` | 1,123 | 375 | 748 | 8 | 0 |

The model's three Make-only targets illustrate the limits of a root
certificate. `tools/flag`'s certification log shows a local
`system/termp` inclusion, and `system/termp` in turn depends on
`system/legal-variablep`. XDOC's separate expansion pass uses `strsubst`
before `acl2x-replace` substitutes an invisible event for certification.
All three roots' pre/post records have `NIL` for skip-proof and axiom
annotations. The model records no trust tags. The execution root records
`INSTRUMENT`, `OTHER-NON-DET` and `UNDEF-FLG`. The project bundle additionally
records `BIGNUM-EXTRACT` and `VIRTUALIZATION`.
[Flag local include](https://github.com/acl2/acl2/blob/8.7/books/tools/flag.lisp#L59),
[XDOC expansion](https://github.com/acl2/acl2/blob/8.7/books/xdoc/str.lisp#L77).

## Features the importer must account for

| Layer | Required treatment for the machine root |
| --- | --- |
| Reader and world | Preserve package-qualified symbol identity, `defpkg` imports, ACL2 numbers and literals (including `#ux`), dotted pairs, quoting/backquote, `#.` constants and reader conditions. Replay dependency order, portcullis, `local`, `encapsulate`, constants, tables and state/world lookups when elaborating source. Assign an event and source origin to every emitted declaration. |
| Expansion | Distinguish reader evaluation, `defmacro`/term expansion (e.g. `b*`, `case`, `mv-let`), event macros (`define`, `def-inst`, bit structures, FTY, `defrstobj`) and `make-event`. For instance, `machine/x86` locally loads `dispatch-creator`; `create-dispatch-for-opcodes` inspects the world and generates `ONE-BYTE-OPCODE-EXECUTE`. State construction generates the abstract `x86` stobj interface and its logical models. The expansion pipeline needs tables, package state and prior events. A consumer of already translated terms can omit the macro evaluator if it records how those terms were obtained and states its source-correspondence boundary. |
| Logical terms | Represent ACL2's total functions over the untyped value universe, including the `nil`/non-`nil` truth convention, exact arithmetic, conses, ACL2 bit operations on integers and translated `if`, quoted values and lambdas. Preserve default values outside guards, `mv` result order, logical stobj state threading and the `:logic` branch of `mbe`/`defexec`. Model the abstract stobj; relating it to any concrete arrays, memory representation or optimized Lean evaluator requires a correspondence proof. |
| Admission and proof events | Recover the mode (`:logic` / `:program`), definitional equations, mutual recursion groups, measures and well-founded relation. Termination, guard verification and `:logic`/`:exec` agreement are separate obligations. Preserve `encapsulate` witnesses or formulate and prove downstream results under explicit constraints. Keep theorem formulas apart from hints, computed hints, rule classes, theory changes and `verify-guards`. Local facts may be needed to reconstruct a proof. Audit `defaxiom`, `skip-proofs`, attachments, meta rules and clause processors before using any exported theorem or constraint. |
| Environment and trust | State and oracle inputs are explicit. Preserve x86isa's logical syscall environment/oracle, undefined-value handling, and TTY buffers. Host syscall forwarding, random/undefined-value overrides, instrumentation and optional socket TTY use raw Lisp or foreign code. `defttag` and `:ttags` authorize dependencies or privileged operations; neither supplies a proof of equivalence to those operations. Keep host adapters outside the logical model and prove any claimed observation correspondence separately. |

[X86ISA package](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/portcullis/package.lsp),
[generated state](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/state.lisp#L642),
[dispatch generation](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/x86.lisp#L76),
[logical environment](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/environment.lisp),
[ACL2+Books manual](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/).

For example, `CREATE-UNDEF` is introduced by `encapsulate` with a local `nfix`
witness and an exported natural-number constraint. An importer can quantify
over an implementation satisfying that constraint and use `nfix` to show that
it is satisfiable. Pinning the logical machine to the witness would specialize
the spec, and assuming that different seeds yield distinct results would add
a property the book does not export.
[Undefined values](https://github.com/acl2/acl2/blob/8.7/books/projects/x86isa/machine/register-readers-and-writers.lisp#L1494).

## Checkable target and upstream evidence

The [C3 X86-RUN slice](acl2-x86-run.md) reproduces the certified logical export
for one declaration and binds the exported body and halted statement in Lean.
The [C3 dependency manifest](acl2-x86-dependencies.md) records and checks the
direct calls from the translated run and step bodies.

1. Export the ordered declaration and constraint closure reachable from the
   translated machine step and run, including the generated dispatcher and
   stobj interface, with book/event origins and pinned input hashes. Expand
   dependencies to a fixed point and fail on unresolved references, including
   unsupported primitives or a `:program` function in a logical body. Keep an
   explicit inventory of excluded proof, documentation and host-runtime events.
2. Have Lean check the serialized terms, references, stobj interface, and
   termination or constraint-witness obligations against an ACL2 value and
   evaluation model. Require the result to cover both `app-view` and `sys-view`,
   including fault/stop state, memory and the given environment inputs. State
   a correspondence theorem for step/run against an independent interpretation
   of the same exported logical terms, with an explicit state relation for an
   optimized representation. Prove source-to-export correspondence separately
   or identify ACL2 expansion as the input-provenance assumption of that result.
3. Import a theorem as a statement or proof obligation until Lean checks a
   derivation. Audit the resulting Lean axioms. An upstream trace or an x86isa
   differential run can help locate a discrepancy; neither discharges a Lean
   obligation. An arbitrary ACL2 proof script has no assumed Lean translation.

The audit emits a small world export with the actual step, run, generated
one-byte dispatcher, `CREATE-UNDEF` constraint and `X86-RUN-HALTED` theorem.
It includes translated bodies, guard and stobj signatures, and admission
metadata where present. The original translated body avoids ACL2's later
`:definition` rule overrides. ACL2's certificate expansion alist and optional
`.acl2x` files cache `make-event` results. `.acl2x` can be generated in a
separate pass, including with proofs
skipped, and replayed at certification. Ordinary event or term macro expansion
and dependency/provenance capture still matter. A `.cert` records ACL2's
certification and book metadata; inclusion normally skips proof replay.
[Make-event](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____MAKE-EVENT),
[set-write-acl2x](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____SET-WRITE-ACL2X).

The pinned `machine/.sys/x86@useless-runes.lsp` is useful for finding proof
dependencies, with SHA-256
`9e083c28699c0c171525ac17dfd4382cb875145a5f9dd99d490f4cf399d0272e`.
Useless-runes counts, proof-tree and rewrite diagnostics do not encode all
inferences. Kestrel's `acl2data` is a source of prover observations for ML.
ACL2 proof-builder scripts drive ACL2's prover, so replay still
needs justified implementations of the commands and inference rules. Milawa
has explicit proofs and a separate checker for its own logic and corpus.
Neither its scope nor a certificate establishes a checker path for these books.
An independently checkable proof format may help for supported fragments if
its checker and the link to the ACL2 statement are proved in Lean.
[Useless-runes](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____USELESS-RUNES),
[proof-builder](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____PROOF-BUILDER),
[Kestrel acl2data](https://github.com/acl2/acl2/tree/8.7/books/kestrel/acl2data),
[Milawa README](https://github.com/acl2/acl2/blob/8.7/books/projects/milawa/README).

## Reproduce

From the Silmaril root, with Git, Python 3.9+, SBCL, Perl, GNU Make and a C
compiler for the Linux native-input check:

```sh
tool="$PWD/tools/acl2-x86isa/inventory.py"
work=$(mktemp -d)
git clone --depth 1 --branch 8.7 https://github.com/acl2/acl2.git "$work/acl2"
git -C "$work/acl2" rev-parse HEAD 'HEAD^{tree}'
make -C "$work/acl2" LISP=sbcl
python3 -B "$tool" "$work/acl2" "$work/logic-scan"

(
  cd "$work/acl2/books/projects/x86isa"
  export ACL2_CUSTOMIZATION=NONE CERT_PL_NO_COLOR=1 X86ISA_EXEC=nil
  ../../build/cert.pl \
    --acl2 "$work/acl2/saved_acl2" --acl2-books "$work/acl2/books" \
    -o "$work/certify.mk" -j 14 machine/x86 tools/execution/top
  ../../build/cert.pl \
    --acl2 "$work/acl2/saved_acl2" --acl2-books "$work/acl2/books" \
    -o "$work/certify-top.mk" -j 14 top
)
python3 -B "$tool" "$work/acl2" "$work/certified" --certified

git -C "$work/acl2" worktree add --detach "$work/native" HEAD
make -C "$work/native/books/projects/x86isa" ACL2="$work/acl2/saved_acl2" \
  X86ISA_EXEC=t machine/shared/libsyscallutils.so write_exec_fn
python3 -B "$tool" "$work/native" "$work/native-scan" \
  --acl2 "$work/acl2/saved_acl2" --native-inputs
sha256sum "$work"/{logic-scan,certified,native-scan}/manifest.json
```

Reference manifest SHA-256 values:

```text
1078ab76d8710aa69d9b672c01575ff393a6f78e63c88eb05eb5d88e026498ec  logic-scan
4053bf6625e6397fce7fd994fd50535ddd8e4b8f377f86019e3d1a7667ccdd27  certified
8d55da7060618bd9a57eca9a79dfaa1c00b3fc1ff91c137f57ef3ea0cbde3864  native-scan
```

The manifest includes each entry source's SHA-256. The audit also records the
raw `.cert` digest and the world sample digest. Raw certificate and log bytes
can depend on the checkout location, host, timing and ACL2 options.

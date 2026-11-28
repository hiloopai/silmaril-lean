# ACL2 x86isa logical call dependencies

This C3 manifest catalogs direct calls in the translated logical bodies of
`X86ISA::X86-RUN` and `X86ISA::X86-FETCH-DECODE-EXECUTE`. It extends the
existing [X86-RUN export](acl2-x86-run.md) and uses the same certified `machine/x86`
root as the [book and certificate inventory](acl2-x86isa.md). The world is
ACL2 8.7 at `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`, with `X86ISA_EXEC=nil`.
[Upstream machine source][source] · [Manifest][manifest] · [Translated step body][step-body]

## Manifest contract

Each root records its requested and resolved symbols. The exporter looks up
the exact ACL2 function first, then consults the world's `macro-aliases` table
if the requested symbol is an alias. It preserves translated call heads as
they occur, including any `$INLINE` names. Both requests in this fixture
resolve directly to the exact spelling shown above.
[ACL2 alias table][aliases] · [Lisp exporter][exporter]

An edge records a call head as `["symbol", package, name]` and its argument
count. Equal edges are coalesced per source declaration. Extraction starts
with `unnormalized-body` and uses ACL2's `remove-guard-holders`, the same
projection used for the pinned X86-RUN export. `X86-RUN-HALTED` remains a
theorem in that export, outside the body graph. The walker includes every
branch and visits the body and actual arguments of translated lambdas.
Quoted objects and variable references contribute no edges. The native
export checks the symbol sets against ACL2's `all-fnnames` and retrieves
declaration arities separately from the world. The offline checker recomputes
both edge lists from the recorded bodies and checks them against the target
arities, declaration table, and frontier.
The native export attests the live arities, world classifications, and alias
resolutions. Reproduction checks those attestations against the pinned world.
[Logical projection][projection] · [ACL2 call collection][all-fnnames] · [Offline checker][checker]

The `world` field records the live-world classification. The `kind` field
records how a declaration can be used by this manifest.

| `kind` | Meaning |
| --- | --- |
| `checked` | The body has a Lean dependency check. Here only `X86-RUN` has this status. |
| `native-only` | ACL2 exposes a translated logical definition. Here the step body is checked structurally by the offline walker, and other definitions of this kind are frontier entries. |
| `primitive` | The call target occurs in ACL2's `*primitive-formals-and-guards*`. This is a world classification. |
| `unsupported` | A named world declaration without a supported logical definition. `world` distinguishes `constrained`, `no-body` and `program`. A program-mode call in an expanded logical body is rejected. |
| `unresolved-external` | A translated call head with no world declaration. The call retains its argument count and the declaration arity is JSON `null`. |

Only the two roots have populated `calls` fields. Unexpanded nonprimitive
targets appear explicitly in `frontier`. Primitives are terminal for this
catalog. The X86-RUN self-edge is retained. No traversal continues from the
frontier, so the manifest makes no claim about SCCs through those declarations.

| Root | Arity | Distinct outgoing edges |
| --- | ---: | ---: |
| `X86ISA::X86-RUN` | 2 | 7 |
| `X86ISA::X86-FETCH-DECODE-EXECUTE` | 1 | 37 |

The 40 declarations comprise two expanded roots, four primitives and 34
frontier definitions, including `X86ISA::ONE-BYTE-OPCODE-EXECUTE` and
the VEX and EVEX dispatchers. This slice has zero unsupported or unresolved
targets.
[Primitive table][primitives] · [Manifest][manifest]

The [frontier audit](acl2-x86-frontier-audit.md) uses this manifest to select
27 additional roots and checks their immediate logical dependencies.

## Checked slice and limits

The native export matches the live X86-RUN formals and logical body against
the already pinned X86-RUN artifact. The existing C3 translation check ties
that artifact to `X86Run.sourceBody`. A Lean kernel check collects the named
calls from that typed body, including its translated `IF` and recursive
call, and compares the set of names and arities to the manifest's X86-RUN
row. The typed translation encodes quoted `-1` as a reserved nullary symbol,
which the comparison removes. The check uses `decide` and audits the
resulting theorem's axioms. The regression suite deletes the self-edge and
a step edge, changes a package and a world arity, deletes a frontier entry,
and marks the step checked. Each mutation must fail at the corresponding
semantic check. [Typed X86-RUN source][run-lean] · [Mutation tests][mutations]

Coverage is **bounded to two logical bodies**, with a **local Lean check for
X86-RUN** in this manifest. The [checked step definition](acl2-x86-step.md)
uses the same pinned step body and frontier. The graph omits transitive
bodies, quoted or dynamically applied callees,
guards, measures, theorem and rewrite dependencies, and stobj constraints
and correspondence obligations. The optional native syscall support is
absent from this profile. The exporter checks the completed root certificate
and rejects skipped-proof, axiom and trust-tag annotations in the root's
pre-, post- and live include records. Those records omit some nested local
certification and expansion dependencies. Repeating the C1 audit gave 1,030
Make targets, 1,027 distinct books named in the root certificate's pre/post
records and 293 visible includes. Local witnesses and proof events are
unavailable in the public world. The ACL2 certificate and its expansion cache
give provenance for the public terms. Reconstructing admission in Lean would
also require constraint and proof evidence. The exporter only inspects
translated terms and world properties.
[C1 certificate evidence and omissions](acl2-x86isa.md#dependency-inventory)

## Reproduce

Build ACL2 and certify `machine/x86` with the
[pinned commands](acl2-x86-run.md#reproduce). Set `acl2` to that checkout
and run the following from the Silmaril root. Both commands start fresh ACL2
processes using the same certified checkout.

```sh
work=$(mktemp -d)
python3 -B tools/acl2-x86isa/export_dependencies.py "$acl2" "$work/one"
python3 -B tools/acl2-x86isa/export_dependencies.py "$acl2" "$work/two"
for file in manifest.json step-body.json; do
  cmp "$work/one/$file" "$work/two/$file"
  cmp "$work/one/$file" "corpus/acl2/x86-dependencies/$file"
done
lake build --wfail +Silmaril.Logic.ACL2.Dependencies.Defs +Silmaril.Logic.ACL2.X86Run.Thms
python3 -B tools/acl2-x86isa/check_dependencies.py "$work/one" --lean
make check CHECK_TARGETS='+Silmaril.Logic.ACL2.Dependencies.Defs +Silmaril.Logic.ACL2.X86Run.Thms'
```

Two fresh SBCL 2.5.2 processes using the same certified checkout produced
byte-identical manifests and step bodies. The Lean dependency agreement
theorem uses only `propext`. The local root certificate hash identifies the
certificate used in both runs. Certificate bytes can vary across checkouts.

| Artifact | SHA-256 |
| --- | --- |
| Dependency manifest | `c36ab7c664fd850adc6d8c81f0d659eeb51fbe18bf06037af79ebeac5f4c9806` |
| Translated step body | `4aa5dcc4b81c2843d7e095c948ad89727248c08c1f37ef397ebd8ae46b328fea` |
| Local `machine/x86.cert` | `aaf5cb798f4dc09d56deff787a4e0b72f796f052122b8286e30fd4e029790011` |

[source]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/x86.lisp#L207
[manifest]: ../../corpus/acl2/x86-dependencies/manifest.json
[step-body]: ../../corpus/acl2/x86-dependencies/step-body.json
[aliases]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L24783-L24797
[exporter]: ../../tools/acl2-x86isa/dependencies.lisp
[projection]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/translate.lisp#L6347
[all-fnnames]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/translate.lisp#L4277
[checker]: ../../tools/acl2-x86isa/check_dependencies.py
[primitives]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/basis-b.lisp#L630
[run-lean]: ../../Silmaril/Logic/ACL2/X86Run/Source.lean
[mutations]: ../../tests/acl2/check_dependencies.py

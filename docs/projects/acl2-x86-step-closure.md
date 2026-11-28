# Literal logical call closure of the 24-root x86 step frontier

The fixture starts from the 24 residual name/arity pairs after the three
`PREFIXES` projection bindings. It selects the original 27 audited roots
with those three pairs removed, checks all 24 root rows against the
immediate audit, and compares the ordered list with Lean's
`Frontier.remainingEntries`. The roots comprise six ordinary-object
definitions, seven stobj interface definitions and eleven other
stobj-bearing definitions.
[Closure fixture][graph] · [Immediate audit](acl2-x86-frontier-audit.md) ·
[Lean frontier](acl2-x86-step-frontier.md)

## Stop rule and source evidence

Starting with the roots, the exporter visits each exact package-qualified
call head once. For every logical definition it projects
`unnormalized-body` through ACL2's `remove-guard-holders`. A separate
walker checks scope and arities of applications, traverses lambda bodies
and actual arguments, and treats quotation as data. ACL2's `all-fnnames`
independently checks the call-head set per body. Each edge records the
observed argument count, independently of the callee's live world arity.
The walk stops at primitives, constrained functions, functions without
logical bodies, and declarations absent from the world. Every named call
to such a terminal stays in the graph. The checker lists nonprimitive
terminal edges and arity mismatches explicitly.

The native exporter hashes the ordered formals and projected body as
compact UTF-8 C3 JSON in memory. Its output contains names, arities,
edges, symbol and stobj metadata, recursion cliques, quotation counts,
and hashes. It leaves the translated terms inside the introspection
process. The 24 root body hashes, edge lists and associated metadata
agree with the immediate audit. The scope is literal logical calls in
the pinned world. Guard, theorem, attachment and raw execution dependencies,
including any call identity carried only as quoted data, fall outside that
scope. Lean checks the root identity list. The transitive evidence comes
from the native world projection and replay.
[World reader][reader] · [Graph checker][checker]

## Verified graph

The walk reached **1,453 declarations and 12,355 distinct directed
call edges**. Every edge has a live declaration of the observed arity.
The table separates declarations with a translated definition from
terminals. A definition with zero named outgoing calls is also a
graph terminal.

| World and signature category | Declarations | Graph terminals |
| --- | ---: | ---: |
| Logical definition with ordinary object signature | 815 | 14 |
| Logical definition in a stobj interface | 146 | 0 |
| Other stobj-bearing logical definition | 462 | 0 |
| Native primitive | 28 | 28 |
| Constrained logical declaration | 2 | 2 |
| Program, absent, or other missing body | 0 | 0 |

The interface category uses the live `stobj-function` property or
membership in the live abstract X86 stobj tuples. The graph contains 73
abstract export names and their 73 logical implementation names. The
recorded role data also distinguishes foundational implementations, of
which this logical call graph reaches zero. An ordinary-object signature
means the function uses ordinary ACL2 object slots and lacks the recorded
interface role. That classification makes no claim about the semantic
meaning of its arguments, including encoded records.
[Logical stobj accessor correspondence](acl2-x86-status.md)

The graph has 1,379 acyclic singleton SCCs and 74 self-recursive singleton
SCCs. Of the self-recursive declarations, 59 have ordinary object
signatures and 15 are stobj-bearing. There are zero multi-declaration
SCCs. The computed cyclic memberships agree with the live ACL2 recursion
cliques. The fixture lists all cyclic members by exact identity.

| Caller | Constrained terminal | Observed and live arity |
| --- | --- | ---: |
| `X86ISA::FEATURE-FLAG` | `X86ISA::CPUID-FLAG-FN` | 5 |
| `X86ISA::FIRST-THREE-BYTE-OPCODE-EXECUTE` | `X86ISA::CPUID-FLAG-FN` | 5 |
| `X86ISA::UNDEF-READ-LOGIC` | `X86ISA::CREATE-UNDEF` | 1 |

These are all three unresolved edges. The public logical world supplies
constraints at these two terminals. A Lean interpretation would need
explicit denotations and any constraints used by its theorems.
[CPUID encapsulation][cpuid] · [CREATE-UNDEF encapsulation][undef]

## Admission and translation boundaries

- **Ordinary object definitions.** The graph establishes native logical
  identities and dependencies. A checked interpretation still needs
  correspondence for the required primitives and a termination argument
  for recursive definitions. For example, the 32-declaration closure of
  `X86-DECODE-SIB-P/2` contains 21 ordinary-object definitions and 11
  primitives, with no stobj role, constrained terminal, or quotation
  outside the current step lowerer's integer-and-symbol fragment. The
  18-declaration closure of the opcode ModR/M predicate includes two
  definitions with other-object quotations.
- **Stobj interfaces.** The live tuples connect public and logical names.
  Proofs about encoded records, accessor and update invariants, and any
  correspondence to concrete state require additional evidence.
- **Stobj-bearing work.** The current lowerer's quotation fragment
  excludes strings in 18 stobj-bearing definitions and other quoted
  objects in 57. The 15 stobj-bearing recursive SCCs still need admission
  evidence. A dependency edge or body hash records source provenance.
  It supplies neither an interpretation nor a refinement theorem.
  [Step translation boundary](acl2-x86-step.md)

## Reproduce

Use the [pinned ACL2 8.7 and certified `machine/x86` checkout](acl2-x86-run.md#reproduce)
at `bc6f4f49e81a0711214a8d91f0d06e0e084d2204` with `X86ISA_EXEC=nil`.
The native hashing routine uses OpenSSL 3's `libcrypto.so.3` on 64-bit
Linux with SBCL. The offline checker and mutation tests use Python's
standard library. From the repository root, set `acl2` to the cached or
freshly certified checkout.

```sh
work=$(mktemp -d)
export PYTHONSAFEPATH=1
for replay in one two; do
  python3 -I tools/acl2-x86isa/check_closure_dependencies.py \
    --checkout "$acl2" --emit "$work/$replay.json"
  cmp "$work/$replay.json" corpus/acl2/x86-dependencies/step-closure.json
done
python3 -I tools/acl2-x86isa/check_closure_dependencies.py
python3 -I tests/acl2/check_closure_dependencies.py
lake build --wfail +Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Defs
python3 -I tools/acl2-x86isa/check_closure_dependencies.py --lean
```

Two fresh native processes produced byte-identical graphs. The fixture
SHA-256 is
`34c24c3ac654cabe834fa2bdcf629936ae355475025c3559a16ab65bf0a38f4a`.
The offline checker validates root evidence, arities, reachability and
graph statistics against that pin. The optional `--lean` check compares
this snapshot with the live specialization, so it detects a later
change to the 24-entry frontier. The snapshot can still be replayed
independently of that comparison.

[graph]: ../../corpus/acl2/x86-dependencies/step-closure.json
[reader]: ../../tools/acl2-x86isa/closure-dependencies.lisp
[checker]: ../../tools/acl2-x86isa/check_closure_dependencies.py
[cpuid]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/cpuid.lisp#L131
[undef]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/register-readers-and-writers.lisp#L1494

# Immediate dependencies of the open ACL2 x86 step frontier

The audit starts from the 28 caller-supplied entries of the
[checked frontier specialization](acl2-x86-step-frontier.md) and excludes
`BITOPS::PART-SELECT-LOW-HIGH$INLINE` (arity 3), whose generic equation is
already checked. The 27 audited roots are selected by exact package, name
and arity. The canonical [run/step audit](acl2-x86-dependencies.md) pins the
original call graph and translated step syntax, and a Lean check equates the
selected signatures with the compiled frontier after selector exclusion.
[Generic bit selection proof](acl2-bit-selection.md) ·
[Immediate graph fixture](../../corpus/acl2/x86-dependencies/frontier-audit.json)

## Verified inventory

| Root classification | Count | Criterion |
| --- | ---: | --- |
| Pure object logic | 9 | Ordinary object inputs and outputs |
| Abstract stobj logical wrappers | 7 | Native `stobj-function` is `X86ISA::X86`, with one direct call to the corresponding `$A` function |
| Opaque machine and dispatcher bodies | 11 | State-bearing or state-dependent logical bodies outside the direct wrapper group |

The graph has 256 distinct outgoing edges counted per audited body. It
includes 21 edges whose target is also an audited root. The union of roots
and targets contains 180 live logical definitions and nine native
primitives. Every observed call arity agrees with ACL2's live arity.
The audited wrapper group includes the two writes `!MS` and
`!INHIBIT-INTERRUPTS-ONE-INSTRUCTION`, and the reads `APP-VIEW`,
`ENABLE-PERIPHERALS`, `HANDLE-EXCEPTIONS`,
`INHIBIT-INTERRUPTS-ONE-INSTRUCTION`, and `RIP`. The `$A` targets terminate
this audit layer. Admitting them will require the corresponding logical
record operation and its encoded-state assumptions.

The audit retains the translated-body hashes, stobj signatures, recursion
metadata and exact outgoing edge lists. It stores no dispatcher or memory
body. The metadata exporter temporarily reads the guard-holder-free
`unnormalized-body` terms from the certified world. The canonical
scope-aware walker checks argument counts, lambda scopes and literal call
heads, and ACL2's `all-fnnames` independently checks their identity sets.
The source hashes include the ordered formals and projected body.
[World reader](../../tools/acl2-x86isa/frontier-dependencies.lisp) ·
[Audit checker](../../tools/acl2-x86isa/check_frontier_dependencies.py)

`X86ISA::GET-PREFIXES` is the only audited root with a recorded recursion
clique and a self-edge. Its memory dependency remains external.
Five machine bodies contain quotations outside the current step
lowerer's integer-and-symbol quotation fragment. The fixture records
string and other-object occurrence counts, including 1,535 strings
and 256 other objects in `X86ISA::ONE-BYTE-OPCODE-EXECUTE`. A graph edge
or a supported quotation fragment supplies source evidence for a future
admission. ACL2 admission proofs, transitive closure, guard semantics,
stobj correspondence and instruction behavior remain outside the audit.

## Small pure admission targets

These are four roots within the pure group. Their prerequisites were read
from the pinned translated definitions. They reuse the already checked
logical `LOGHEAD` and width/offset selector.

| Root | Next exact premise |
| --- | --- |
| `X86ISA::PREFIXES->ADR$INLINE / 1` | `PREFIXES-FIX$INLINE x = LOGHEAD 52 x`; select width 8 at offset 36 |
| `X86ISA::PREFIXES->NUM$INLINE / 1` | The same 52-bit fix; select width 4 at offset 0 |
| `X86ISA::PREFIXES->NXT$INLINE / 1` | The same 52-bit fix; select width 8 at offset 44 |
| `X86ISA::X86-DECODE-SIB-P / 2` | `MODR/M-FIX$INLINE x = LOGHEAD 8 x`; `MODR/M->MOD$INLINE` uses width 2 at offset 6, and `MODR/M->R/M$INLINE` uses width 3 at offset 0. Reuse standard `NOT` and `EQL` for the branch tests. |

The SIB predicate requires a NIL 16-bit-address flag, an R/M field of 4,
and a MOD field different from 3. [Bit layouts][layouts] ·
[SIB recognition source][sib]

The four pure prefix-byte setters in the graph introduce
`BITOPS::PART-INSTALL-WIDTH-LOW$INLINE` and additional fixers.
The pure opcode ModR/M predicate calls two unexpanded mode-specific table
functions. Those are larger closures than the four targets above.

## Reproduce

Use the [pinned certified checkout](acl2-x86-run.md#reproduce).

```sh
export PYTHONSAFEPATH=1
python3 -I tools/acl2-x86isa/check_frontier_dependencies.py \
  --checkout "$work/acl2" --emit "$work/frontier-audit.json"
cmp "$work/frontier-audit.json" corpus/acl2/x86-dependencies/frontier-audit.json
lake build --wfail +Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Defs
python3 -I tools/acl2-x86isa/check_frontier_dependencies.py --lean
python3 -I tests/acl2/check_frontier_dependencies.py
```

Two fresh ACL2 sessions reproduced the audit byte-for-byte.
The fixture SHA-256 is
`c5c67c055f050450b9c74318db44cb63cca248cf0a104eb04da2fdf7f87f4553`.
The canonical manifest and step body also replay byte-for-byte.
The offline checker pins the audit and validates its graph bookkeeping
against the canonical step fixture. Live replay checks the metadata
attestations against the pinned world.

[layouts]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/utils/structures.lisp
[sib]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/prefix-modrm-sib-decoding.lisp#L2480

# Wasm continuation syntax with exact stack cuts

## Motivation

Purplesyringa's [“Wasm is not quite a stack machine”](https://purplesyringa.moe/blog/wasm-is-not-quite-a-stack-machine/)
(April 27, 2026) contrasts Wasm's lack of general stack rearrangement instructions
such as `dup` and `swap` with JVM bytecode. Its “Semantics” section proposes reading
the binary as a postfix encoding of compound expressions, with locals for sharing,
and specifically qualifies the ternary-like `if` analogy as **pre-multi-value**.
That is a useful presentation heuristic, not the Core execution or validation
specification. Current Core admits an `if` that consumes stack-supplied values
in addition to its condition and produces multiple results.

In the [Core reduction rules](../../Silmaril/Wasm/Execution/Core/Step.lean), `if`
first selects a block by popping the condition. `Step.block` moves exactly the
declared parameters into the label body and uses the result arity for the label.
`Steps.ctxtInstrs` retains the surrounding value prefix and continuation. For
`br_if`, fallthrough consumes only the condition; the taken branch invokes `br`,
and `brLabelZero` passes the target's results rather than executing the remainder
inside the label. The [Core typing rules](../../Silmaril/Wasm/Validation/Instructions.lean)
encode those same boundaries. `Examples.lean` checks the two-step `if` entry in
Core with an arbitrary preserved prefix and an arbitrary suffix of instructions.

## Representations and theorem boundary

[`Continuation/Defs`](../../Silmaril/Wasm/Binaryen/Continuation/Defs.lean) defines
unchecked `Raw` and intrinsically indexed `Code ctx inputs outputs raw`. The
right-associated `let_` binds an operation's output suffix for its continuation;
it does not name arbitrary registers or duplicate values. The consumed and
produced suffixes and the retained prefix are explicit in `Code`. `block` and
`if_` own separate continuations under an extended label context, entered on the
declared parameter stack only. This is a stack-indexed continuation presentation,
not unrestricted ANF or a replacement for the Core machine.

```text
  Code ctx ins outs raw  ── toCore ──▶ Intrinsic.Body ctx (.plain ins outs)
          │                                         │
        erase                                  Body.erase
          ▼                                         ▼
         Raw ───────────── lower ─────────────▶ List Instr
          │                                         ▲
       toBinaryen                                   │ BExpr.lowerList
          └────────────────▶ List BExpr ────────────┘
```

- `Code.binaryen_square` and `Code.sound` give **literal Core instruction
  equality** and actual `InstrsOk`, not an alternate typing validator.
- `Raw.coreEquiv` is an executable inverse on the syntactic fragment accepted
  by `Raw.read`. `Code.core_image_iff` characterizes the typed image by `Cuts`,
  an independent predicate on Core instructions: every operation has an exact
  Core typing at its cut and every structured body has such cuts. Given these
  cuts, `Code.lift_core` reads an existing intrinsic body's erasure back at the
  same type. `Code.same_erasure_iff` forgets derivation artifacts, not instructions.
  `Raw.read` by itself does **not** accept or reject on typing grounds.
- `Raw.ofBinaryen_eq_some_iff` reads any supported layer-D `BExpr` forest after
  its actual lowering, then rebuilding chooses the existing `liftInstrs`
  normal form. The folded and structured-lift fixtures demonstrably differ
  while lowering to the same body. In particular the normalized `if` has no
  tree child for the condition: the condition is already on the stack.

The fragment includes integer constants and binary operations, initialized
local reads, direct calls with their full parameter/result vectors, `drop`,
`nop`, `br_if`, `block` and `if`. It does not handle local initialization
updates, arbitrary Core subsumption, `unreachable` or stack polymorphism after
unconditional exits, loops, exception handlers, or indirect calls. An excluded
instruction can be perfectly valid Core. Equality of lowerings preserves the
order of effects/traps for the **same Core execution**, not the reductions of
a newly defined evaluator or an upstream optimization pass.

The earlier [intrinsic folded expression experiment](https://github.com/hiloopai/silmaril-lean/pull/1220)
proves the forward square for trees with an empty relative input stack and at
most one result. Here the result is stronger in a different direction: exact
read-back and a typed image theorem, with open input stacks, arbitrary declared
result vectors, and no need to reconstruct a closed producer tree for each
operand. The implementations share Core and layer D, not an unmerged API.

Silmaril's layer D is not C++ Binaryen's `Expression` tree. With pinned
Binaryen `version_133` (`fba5005a132d85d578be5bd010e0487ed8e2ce3e`), reading
and rewriting the exact Core fixture introduces locals for the `if` parameter;
that output validates and agrees on the tested results and writes, but is no
longer in this syntax fragment. This experiment does not prove the rewrite
correct in general or identify silmaril's syntax with the upstream tree.

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Binaryen.Continuation.Examples'
BINARYEN_BIN=/path/to/binaryen-version_133/bin sh scripts/wasm-continuations/check.sh
```

`Examples.lean` is a regular library module, so hosted builds check the valid
multi-result function, invalid parameter and missing-call-argument cases, and
valid but excluded `unreachable`. The evaluator fixture tests both arms with
a preserved `i64` prefix: return `(99,4,7)` with log `0`, versus `(99,4,5)` with
log `45` (not `54`). A variant traps after writing `4` and before a second call.
The script adds axiom receipts, a Core binary round trip, the independent
upstream `wasm-shell` fixture, and the Binaryen rewrite check. Those last two
tests require the pinned tools; they are not theorem premises.

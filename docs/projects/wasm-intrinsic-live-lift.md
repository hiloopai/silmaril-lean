# Canonical live Core instruction sequences

This is the checked inverse of erasure for the **live** portion of the
stack-indexed integer machine. It reuses `Op`, `Code`, and `Slot`, not another
public instruction syntax. It checks exact `i32`/`i64` operand widths and
initialized local indices, then determines the result stack. The opcodes are
integer binary operators, `local.get`, `nop`, and `drop`. `unreachable` is
excluded because the typed representation allows multiple intermediate
effects for the dead suffix. Dynamic numeric traps remain possible.

`Code.reify?` computes from raw syntax and the two input indices (locals and
initial operands). Success carries exact raw erasure, and `Code.Lifted.sound`
proves existing `InstrsOk` at the inferred effect. `Code.reify_erase` recovers
the *individual* typed sequence, not just an erasure-equivalent witness.
`Code.liveEquiv` packages both inverse laws against the raw sequences accepted
by the exact-stack profile. The inverse is executable; no classical choice
is required to obtain the witness.

The raw side is the **checked profile**, not every derivation of `InstrsOk`.
A completeness claim stated directly over all `InstrsOk` derivations for
the syntactic whitelist would need the principal-effect lemma through Core's
subsumption, framing and local-initialization annotations. The wider intrinsic
AST has proof-relevant framing and subtyping; its exact-erasure equivalence is
intentionally a quotient. Neither construction replaces the other.

```sh
lake build --wfail +Silmaril.Wasm.Execution.Core.Intrinsic.LiveLift.Thms
lake env lean -j1 -M4096 -DautoImplicit=false -E warning tests/wasm/intrinsic-machine/LiveLift.lean
```

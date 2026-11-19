# Observing typed Core code

`Silmaril.Wasm.Execution.Core.Intrinsic.Observation` lifts Core's existing
`behavioursOf` to typed instruction sequences via their erased configuration.
The observation is the actual set of finite results and infinite traces, not
equality of results at some interpreter fuel. The profile is deterministic
and has no host calls. The comparison is across all well-indexed frames and
operand stacks, using the **same** world for both operands at each comparison.

`Code.observe_seq` transports observation across a successful typed head step
using raw one-step reflection and `behavioursOf_eq_of_step_unique`. That gives
`Code.append_congr`: a shared nontrapping typed left context respects the
relation. The context condition is about the prefix's computation, not about
either tail. This does not generalize to right contexts, trapping prefixes,
arbitrary administrative or host contexts, or concurrent execution.

`Code.nop_quotient` identifies `nop; body` with `body` in the observational
quotient while proving their raw code lists unequal. The regression places
this difference after a typed local read. This quotient is distinct from the
exact-erasure quotient for `Validation.Intrinsic.Function` and `.Module`.

The next abstraction boundary is store-level invocation: Core `FunEquiv`
and `ModuleEquiv` observe invocation at addresses and linked exports, not
raw syntax in isolation. Lifting needs typed function installation/entry,
call/reference and frame/return simulation, then a relation on two reachable
stores and exports. Component `CompEquiv` and `IfaceEquiv` already quantify
over a `CoreSem` interpretation; applying them needs a semantics-preserving
adapter from those Core module observations to that interpretation, not an
identification of component typing with Core typing. None of those lifts is
claimed by this code observation layer.

```sh
lake build --wfail +Silmaril.Wasm.Execution.Core.Intrinsic.Observation.Thms
lake env lean -j1 -M4096 -DautoImplicit=false -E warning tests/wasm/intrinsic-machine/Observation.lean
```

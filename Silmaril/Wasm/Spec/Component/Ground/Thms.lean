module

public import Silmaril.Wasm.Spec.Component.Ground.Defs
public import Silmaril.Proofs.Wasm.Spec.Component.Ground

@[expose] public section

/-!
# Grounding component specifications: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Component.Ground`. For a simple component `c` with
`c.Good`, at every profile `P` (no determinism assumption):

* `Simple.ir_of_spec`: every terminating outcome `b` of the canonical-ABI specification
  `exportSpec P c x vs` (Core 3.0 `Steps P` of the core export between `checkLower` and
  `liftArgs`) is the trace `[call j vs, ret j b]` of the IR program `Simple.irProg c` in
  `irSem (modSem P)` (from `Reference.specToIR`, proved);
* `Simple.contract_spec`, `Simple.retPost_spec`: **contracts and return postconditions verified
  on the IR hold of every terminating specification outcome** (unconditional);
* `Simple.refSound_of_arity`: **`Simple.RefSound` holds unconditionally** for components within
  the flat arities (`c.FloatFree`, `c.Inst`, `c.Arity`), from the proved
  `Reference.refToSpec_of_arity`;
* `Simple.contract_ref`: **a contract verified on the IR holds, as a sentence of the reference
  institution `inst contract (refSem prof (refHost P) ())`, of the reference component
  `c.toRef` over `core3P P`** (precondition: arguments are images of well-typed IR values;
  postcondition: for terminating outcomes), for `c` good, float-free, instantiated as the IR
  assumes and within the flat arities (unconditional); `Simple.retPost_ref`, the same for return
  postconditions; `Simple.contract_of_refSound`, `Simple.retPost_of_refSound`: the forms taking
  `RefSound` as a hypothesis.

Not covered: divergence, deadlock and cancellation outcomes (the IR's finite plays do not
observe them; the transferred properties are guarded by `Terminates`), components outside the
`Simple` fragment, and sequences of calls on one instance.
-/

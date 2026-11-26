# Many-sorted equations in Peggy

`Peggy.Bridge.Equational.comorphism S` connects the existing
`Silmaril.Logic.Algebraic.ManySorted.inst S` to `Equational.totalPrimitiveInst S`,
the fixed-sort Peggy institution with total primitives. The source keeps
its ordinary algebras and algebra homomorphisms. The signature functor sends
sort `s` to `PEG.Ty.data s` and each operation to one primitive at the same
ordered operand and result profile. Distinguished PEG Boolean and iteration
count sorts keep their built-in meanings.
[Equational institution](../../Silmaril/Logic/Algebraic/ManySorted/Defs.lean) · [Bridge API](../../Silmaril/SSA/Peggy/Bridge/Equational/Thms.lean)

## Syntax and observations

The compiler preserves the declared parameter context, including unused
slots, and produces one root of the equation's result sort. It visits term
occurrences in preorder, assigning a row to each variable or operation
application. Parameter labels refer to typed parameter slots. Argument
edges point forward into the corresponding child blocks. This gives an
acyclic graph in the empty loop forest. Repeated occurrences are compiled
separately. Nullary operations and finite contexts, including the empty
context, use the same construction.

Evaluating the compiled graph gives the singleton observation `some v`,
where `v` is ordinary term evaluation in the pulled-back algebra. The proof
uses the number of each child to verify the existing guarded evaluator's
node equations, then uses uniqueness of their solution. The bridge compiles
ordinary terms to PEGs, while the Egg bridge unfolds existing PEGs to replay
rewrite receipts. Each uses the guarded Figure 11 semantics.
[Guarded denotation](peg-semantics.md)

## Variance and totality

The bridge is a comorphism. Signatures and sentences translate forward.
Models translate backward, from the total-primitive Peggy model category
into ordinary sorted algebras, with equality arrows sent to the corresponding
algebra morphisms. The operation contract requires `run` to produce a defined
result on every tuple of defined operands. Pullback uses those results as
total operations. Since opcode reducts precompose the primitive
interpretation, they preserve this contract.

Relabelling and compilation commute on the actual numbered graphs. Taking a
Peggy reduct and then the algebra pullback gives the same functor as taking
the algebra pullback first and then the source reduct. In a total-primitive
model, the compiled equation holds exactly when the original equation holds
in the pulled-back algebra. Every ordinary source algebra has a Peggy
expansion with that algebra as its pullback. This also gives reflection of
consequence for translated equational theories through the library's
model-expansive comorphism theorem.

The source is the fixed-sort, unconditional equational fragment, over
Lean `Type` sorts and carriers. Empty carriers are permitted when the
signature admits an algebra over them. Compiled sentences use parameter and
primitive nodes. The target may contain other guarded PEG graphs, whose control
operators may still yield bottom. Arbitrary partial primitives fall outside
the model contract.

## Verification

```sh
lake build --wfail +Silmaril.SSA.Peggy.Bridge.Equational.Thms \
  PeggyEquationalTests PeggyInstitutionTests PeggyDialectTests PEGCoreTests
lake env leanchecker Silmaril.SSA.Peggy.Bridge.Equational.Thms
lake env leanchecker tests.ssa.PeggyEquational
```

The regression uses a mixed-sort operation with a flag and two ordered
number operands, a nullary operation, a repeated variable and a symbol
identification.
[Lean fixture](../../tests/ssa/PeggyEquational.lean)

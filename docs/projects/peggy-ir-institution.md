# Ordered Peggy to RVSDG and regionless MLIR institutions

The bundled chain is `peggyToRVSDG`, `rvsdgToMLIR` and their composition
`peggyToMLIR`. Sentences go forward. Models are pulled back from the target,
and satisfaction is an equivalence at each signature. The signatures range
over Peggy dialects on a fixed type of data sorts. An arrow can identify
primitive symbols while retaining each ordered operand list and single result
sort. The underlying IR signature functors are `rvsdgSignature` and
`mlirSignature`. The bundled arrows are identity on their common indexing
family. Bool and count retain the PEG carriers.
[Definitions](../../Silmaril/SSA/Peggy/Bridge/IR/Defs.lean) ·
[Bundled arrows](../../Silmaril/SSA/Peggy/Bridge/IR/Thms.lean)

## Restrictions and exact observation

- The Peggy source has the actual zero-loop typed equations from the ordered
  bridge. Every operand points to a smaller vertex number. Each table extends
  to an admitted Peggy open graph in the empty forest, using the strict rank
  to rule out cycles. `includePeggy` compares that sentence restriction with
  the upstream total-primitive institution. `restrictPeggyModels` presents
  the total-primitive model restriction of the original Peggy institution.
  Source satisfaction is the upstream guarded equality of ordered roots.
- The RVSDG room uses canonical value-boundary equations, interpreted with
  the existing numbered graph evaluator. Every generated opcode has only
  value operands and a single value result. The induced models present copy
  as identity, select as the PEG Boolean choice, and each primitive as its
  original total function.
- The MLIR room uses the existing regionless equation type at the generated
  signature. Its induced models use the same data carriers and functions.
  The existing regionless profile pullback is exactly the induced RVSDG
  model. Arbitrary interpretations of the structural symbols and changes of
  the fixed sorts lie outside these model families.
  [Peggy institution](peggy-institution.md) ·
  [Ordered compilation](peg-ir-bridge.md) ·
  [Regionless institutional bridge](rvsdg-mlir-regionless.md)

`Canonical` bundles the model restrictions from the actual canonical RVSDG
and MLIR room functors, reindexed along the respective signature functors.
It includes the RVSDG value equations into all numbered equations on the
induced models. Those comparisons use Mathlib's discrete model categories
to match the room hom universe of the original IR institutions.
`mathlibDiscreteComorphism` puts either main arrow or their composition in
the same convention, retaining the signature and sentence maps and the model
pullback on objects. [Canonical comparisons](../../Silmaril/SSA/Peggy/Bridge/IR/Canonical.lean)

## Naturality

The PEG compiler commutes with primitive relabelling as equality of numbered
graphs. The proof compares the emitted terms and their exact signature lists,
preserving source reference positions and the order of roots. The existing
`mapGraph_toGraph` then transports the law to the numbered table. The
RVSDG–MLIR sentence law follows from the existing profile-map precomposition
and postcomposition theorems. Model reducts commute with both canonical IR
expansions and with the total-primitive PEG pullback.
[Compiler and profile naturality](../../Silmaril/Proofs/SSA/Peggy/Bridge/IR/Naturality.lean)

The composed arrow is model-expansive on this source. A total-primitive
Peggy interpretation gives a total function at each profile by extracting
its defined result. The induced MLIR model pulls back to the original
Peggy interpretation. This expands source models within the stated IR
restriction. Looping PEGs, effectful or partial primitives and unrestricted
IR models have separate proof obligations.

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.SSA.Peggy.Bridge.IR.Canonical PeggyInstitutionTests PeggyEquationalTests PEGIRBridgeTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyInstitution.lean
for module in \
  Silmaril.SSA.Peggy.Bridge.IR.Defs Silmaril.SSA.Peggy.Bridge.IR.Thms \
  Silmaril.SSA.Peggy.Bridge.IR.Canonical Silmaril.Proofs.SSA.Peggy.Bridge.IR.Naturality \
  Silmaril.Proofs.SSA.Peggy.Bridge.IR.Satisfaction tests.ssa.PeggyInstitution; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The regression uses a parameter, a binary primitive, a φ and repeated
roots. Two source literals give different results. A nonidentity signature
arrow identifies the literals, and the resulting equation holds in the
canonical regionless evaluator. The test applies the bundled satisfaction
theorem and checks exact sentence naturality on both compilation stages.
[Regression](../../tests/ssa/PeggyInstitution.lean)

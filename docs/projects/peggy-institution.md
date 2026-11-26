# The fixed-sort Peggy institution

`Silmaril.SSA.Peggy.Institution.inst` is an instance of the library's
`Silmaril.Inst.Institution`, built with `Plain.toInst`. Its signatures are
PEG instruction alphabets over a fixed type of data sorts. A model is a
`PEG.Interpretation` with a carrier for each data sort and a partial
interpretation for each primitive. The model categories are discrete.
[Dialect signatures](peggy-dialect.md) · [Institution builders](../../Silmaril/Logic/Inst/Builders/Core/Defs.lean)

A sentence is an open equation between two structurally admitted PEGs at a
shared parameter list, result list and loop forest. `Equation.Holds` requires
the full ordered root tuples to agree at every defined parameter assignment
and every vector of natural-number loop indices. Both sides use the guarded
Figure 11 denotation. Each root has its own optional value, so reordering
roots can change truth and each root's bottom participates in equality.
[Guarded denotation](peg-semantics.md) · [Satisfaction definitions](../../Silmaril/SSA/Peggy/Institution/Defs.lean)

For a fixed-sort opcode map `f : S ⟶ T`, sentences relabel their primitives
forward and `reduct f` precomposes a target model's primitive interpretations
with `f`. All carrier types, parameter slots and loop coordinates are shared.
`OpenGraph.denote_map` gives equality at every node and index, and
`OpenGraph.observe_map` gives equality of the ordered root observations.
Applying the latter to both sides of an equation proves
`(e.map f).Holds M ↔ e.Holds (reduct f M)`. `modelFunctor` is extracted from
`inst`, with arrows acting by the discrete functors of the reducts. The
model reduct along `f ≫ g` first takes the reduct along `g`.
[Transport and institution laws](../../Silmaril/SSA/Peggy/Institution/Thms.lean)

## Families of dialects

`onFamily F` restricts Peggy along a signature functor `F : C ⥤ FixedSortSignature Data`.
This gives a comparison comorphism `familyComorphism F` into the full
fixed-sort institution. A natural transformation `α : F ⟶ G` induces
`familyChange α` between the restricted institutions over `C`. At each
object it translates equations and takes model reducts along `α.app`,
with the same exact satisfaction condition.
[Family definitions](../../Silmaril/SSA/Peggy/Institution/Family/Defs.lean)

## Verification

```sh
lake build --wfail +Silmaril.SSA.Peggy.Institution.Thms \
  +Silmaril.SSA.Peggy.Institution.Family.Defs PeggyInstitutionTests PeggyDialectTests PEGCoreTests
lake env leanchecker Silmaril.SSA.Peggy.Institution.Thms
lake env leanchecker Silmaril.SSA.Peggy.Institution.Family.Defs
lake env leanchecker tests.ssa.PeggyInstitution
```

The regression maps the step in an open theta recurrence to a primitive
that returns bottom. An equation swapping the parameter and feedback roots
agrees at index zero and fails at index one, where the feedback root is
bottom and the parameter root is still defined. The fixture exercises the
actual institution's satisfaction condition and reduct functors, plus the
local translation and reduct of a family comorphism.
[Lean fixture](../../tests/ssa/PeggyInstitution.lean)

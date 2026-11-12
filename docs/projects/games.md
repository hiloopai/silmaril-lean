# Games region

The `Games` region holds game semantics for components that call effects and
answer them. An **effect signature** lists operations and the answers each one
can return. A **play** is a sequence of questions and answers between a
component and its environment. A **strategy** is a prefix-closed, receptive set
of plays, and refinement is inclusion of plays.

## Contents

These are the topics this release contains:

| Topic | Contents |
| --- | --- |
| `Silmaril.Games.Sig` | Effect signatures, the empty signature, sums, renamings and equivalences |
| `Silmaril.Games.Play` | Moves, legal plays and their prefix and concatenation laws |
| `Silmaril.Games.Strategy` | Strategies and their complete lattice of refinement |
| `Silmaril.Games.Zip` | Parallel interaction with hiding, and its associativity |
| `Silmaril.Games.Composition` | Composition and copycat: precongruence, unit laws, associativity, joins |
| `Silmaril.Games.Handler` | Handlers as strategies, and composition of handlers |
| `Silmaril.Games.LTS` | Labelled transition systems as strategies, and their pairing |
| `Silmaril.Games.Div` | Plays with divergence and infinite plays, and three readings of a strategy |
| `Silmaril.Games.DivComp` | Composition of strategies with divergence |
| `Silmaril.Games.DivLTS` | The divergence reading of a transition system |
| `Silmaril.Games.DivLTSComp` | Composition of transition systems with divergence |
| `Silmaril.Games.Inst` | Instantiation and linking of components with failure |

Each topic has a `Defs` and usually a `Thms` header. Proofs that need more
than a few lines are in `Silmaril/Proofs/Games/<Topic>/`; headers import them
with plain imports.

## Dependencies

The region depends on `Prelude` and on public Mathlib. `DivLTS` uses the
infinite traces of `Silmaril.Foundations.InfiniteTrace`. The institution views
of games (`InstFacade`, `InstGraph`) also use the institution facade in
`Logic`, so the region declares `deps = ["Prelude", "Logic"]`. The `Wasm`
region uses `Games` for its component games and must list it in its `deps`.

## Assumptions

The region has no `sorry`, no `axiom` declarations, no proofs by compiled code and no
`Task` declarations. Its theorems use only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

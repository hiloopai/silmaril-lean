# Institution facade

`Silmaril.Logic.Inst` gives the public institutions of
`Silmaril.Logic.Institution` short, consistent names and notation. It is a
**facade**: almost every declaration is an `abbrev` of a public notion or an
`export` alias, so a value built with the facade is a public value and every
existing statement about public institutions applies to it unchanged.

## Names

| Facade (`open Silmaril.Inst`) | Public notion |
| --- | --- |
| `Institution` (`Institution₀`, `Institution₁`, `Institution₀₁`, `Institution₁₁`) | `Inst.{u,v,w,m₁,m₂}` at the given universes |
| `A.Sen S`, `A.Mod S`, `M ⊨[A] φ` | `(A.I.obj S).Sen`, `(A.I.obj S).Mod`, `(A.I.obj S).Sat M φ` |
| `A.map σ`, `A.reduct σ`, `A.Entails Γ φ` | `(A.I.map σ).sen`, `(A.I.map σ).mod.obj`, `(A.I.obj S).Entails Γ φ` |
| `Comorphism A B`, `f.sig`, `f.sen S`, `f.mod S` | `Inst.CoHom A B`, `f.Φ.obj`, `(f.ρ.app S).sen`, `(f.ρ.app S).mod.obj` |
| `Morphism A B`, `f.sig`, `f.sen S`, `f.mod S` | `Inst.Hom A B`, `f.Φ.obj`, `(f.η.app S).sen`, `(f.η.app S).mod.obj` |
| `f ≫ᶜ g`, `𝟙ᶜ A`, `f ≫ᵐ g`, `𝟙ᵐ A` | `Inst.CoHom.comp`, `Inst.CoHom.id`, `Inst.Hom.comp`, `Inst.Hom.id` |
| `A.Theory`, `A.TheoryMorphism T T'` | `Theory A.I`, `T ⟶ T'` |
| `Comorphism.ModelExpansive`, `Morphism.Sound` | `Inst.CoHom.ModelExpansive`, `Inst.Hom.Sound` |

Three notions are new rather than aliases:

- `Satisfies`, the class behind the scoped notation `M ⊨ φ`. Every room is an
  instance, and `M ⊨ φ` is `M ⊨[A] φ` by `Iff.rfl`.
- `Valid φ`, satisfaction in every model.
- `SemiComorphism`, a comorphism whose satisfaction condition is required only
  on a class of sentences and only in the directions that hold. Every
  comorphism is one (`Comorphism.toSemi`).

The facade names are also exported into the public `Inst`, `Inst.CoHom` and
`Inst.Hom` namespaces, so dot notation works on values typed with the public
names. These aliases add no constants.

## Modules

The facade has two layers. The core layer imports only
`Silmaril.Logic.Institution.Morphism`. The broad layer adds the public
borrowing and Hets logic-graph APIs.

| Module | Layer | Contents |
| --- | --- | --- |
| `Silmaril.Logic.Inst.Core.Defs` | core | Names, notation, `Satisfies`, `SemiComorphism` |
| `Silmaril.Logic.Inst.Core.Thms` | core | Satisfaction conditions as `simp` lemmas, naturality, identity and composition laws, transfer along semi-comorphisms |
| `Silmaril.Logic.Inst.Builders.Core.Defs` | core | Institutions and comorphisms from plain functions and their laws, discrete model categories, behavioural institutions |
| `Silmaril.Logic.Inst.Defs` | broad | The core names plus `ModelExpansive` and `Sound` |
| `Silmaril.Logic.Inst.Thms` | broad | Model expansiveness of identities and composites; borrowing of consequence and validity |
| `Silmaril.Logic.Inst.Builders.Defs` | broad | The core builders plus model expansiveness of `ofIso` |
| `Silmaril.Logic.Inst.Graph.Defs` | broad | Typed logic graphs (`GraphSpec`), path comorphisms and borrowing along paths |

Import the core layer when a development needs no borrowing.

## Assumptions

The facade has no `sorry`, no `axiom` declarations, no proofs by compiled code and no
`Task` declarations. Its theorems use only Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

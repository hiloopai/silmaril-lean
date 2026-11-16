# Consequence systems: core API

This page covers the core of `Silmaril.Consequence`: what is defined, what is proved, and
which modules own what. The master roadmap for consequence systems, which covers all four
tracks (core, structural derivations, Wasm/SZS protocols, explorer), is
[consequence-systems.md](consequence-systems.md). Plans live there; this page describes the
API.

## The objects

A consequence system is a relation between contexts and conclusions:

```lean
abbrev System (Ax : Type u) (C : Type v) := Ax → C → Prop     -- S a c : "a ⊢ c"
abbrev WSystem (Ax : Type u) (C : Type v) := Ax → C → Type w  -- witnesses of a ⊢ c
def WSystem.erase (W : WSystem Ax C) : System Ax C := fun a c => Nonempty (W a c)
```

`Ax` and `C` are independent types. A context does not have to be a collection of
conclusions, and **no structural rule is assumed**: reflexivity, weakening, cut, contraction
and exchange all have to be stated as hypotheses. The core supplies one such hypothesis,
`MonoWrt r S` (monotone along a relation `r` you pass explicitly), and its `Preorder` case
`AxMono`. Structural closures belong to the structural-derivations track.

Because `System` is an `abbrev`, the order and lattice structure come from Mathlib's pointwise
`CompleteBooleanAlgebra` on `Ax → C → Prop`, with no instances of our own:

| notation | meaning (`Thms`) |
|---|---|
| `S ≤ T` | `∀ a c, S a c → T a c` (`le_iff`) |
| `⊥`, `⊤` | nothing is proved, everything is proved |
| `S ⊔ T`, `S ⊓ T`, `S \ T`, `Sᶜ` | pointwise or, and, and-not, not |
| `sSup F`, `sInf F` | proved by some member of `F`, proved by every member of `F` |

`S.Sound T := S ≤ T` and `S.Complete T := T ≤ S` compare `S` with a reference system `T`.
Both together are equality (`sound_and_complete_iff_eq`).

## Four "everything follows" notions

These are separate definitions because they come apart:

| name | statement | scope |
|---|---|---|
| `Universal S` | `∀ a c, S a c`, i.e. `S = ⊤` | the whole system |
| `ProvesAll S a` | `∀ c, S a c` | one context (inconsistent or trivial) |
| `ContextConsistent S a` | `¬ ProvesAll S a` | one context |
| `ProvesFalse S ff a` / `ConsistentWrt S ff a` | `S a ff` / `¬ S a ff` | one context, relative to a chosen `ff` |

* `ProvesAll` always implies `ProvesFalse`. The converse holds exactly under
  `Explosive S ff` (`Explosive.provesFalse_iff`), and `not_explosive_ex` gives a system where it
  fails.
* Empty domains:
  * With `IsEmpty C`, every context proves everything, no context is consistent, and `⊥ = ⊤`.
  * With `IsEmpty Ax`, every system is universal.
  * Bottom-relative consistency needs some `ff : C`, so it cannot even be stated over an empty
    `C`.

## Reindexing and translations

`S.pullback f g` reindexes along `f : Ax' → Ax` and `g : C' → C`. It is functorial
(`pullback_id`, `pullback_comp`), monotone, and preserves `⊥ ⊤ ⊔ ⊓ \`.

A `Translation S T` consists of maps `ax`, `c` with `S ≤ T.pullback ax c`. It is
conservative when `T.pullback ax c ≤ S` as well.

* `Sys`, the bundled systems, form a Mathlib `Category` with translations as morphisms.
* `WSys` and `WTranslation` (which also map witnesses) form a category too, and
  `WSys.erase : WSys ⥤ Sys` is a functor.
* `Sys.forget : Sys ⥤ Type u × Type v` is faithful.
* A translation with given maps exists iff the inclusion into the pullback holds, and it is
  then unique (`nonempty_translation_iff`). Every translation factors through the conservative
  `toPullback` (`factor_toPullback`).

## Context shapes

| shape | `Ax` | maps from finer shapes, and what they forget |
|---|---|---|
| `SingleSystem C` | `C` | — |
| `ListSystem C` | `List C` | `ctxSingle : C → List C` (forgets nothing) |
| `NamedSystem N C`, `NatNamedSystem C` | `N → Option C` | `ctxNamed : List C → ℕ → Option C` (forgets nothing; positions become names) |
| `FinsetSystem C` | `Finset C` | `ctxFinset : List C → Finset C` (forgets order and multiplicity) |
| `SetSystem C` | `Set C` | `ctxSet : Finset C → Set C` (forgets finiteness); `ctxRange : (N → Option C) → Set C` (forgets names, order, multiplicity) |

The injectivity and non-injectivity facts are proved (`Ax/Thms`). So are the weakening
orders each map respects: `List.Subset` maps to `⊆`, `NamedLE` maps to `⊆`, and a prefix
maps to `NamedLE`. Weakening orders are always passed to `MonoWrt` explicitly, because the
`≤` on `List` is lexicographic.

## Semantics, rooms, institutions, SZS

A `Satisfaction Ax C` has its own type of models and two **independent** relations, `satAx`
and `satC`. Its consequence system is `entails a c := ∀ m, satAx m a → satC m c`.

* **SZS.** `entails a c` is the THM status of `problem a c` (`entails_iff_thm` in the current
  ontology, `entails_iff_thm2007` in the 2007 text). A failure is CSA (`not_entails_iff_csa`).
  CAX implies `ProvesAll`. When `ff` has no models, CAX is the same as proving `ff`
  (`cax_iff_provesFalse`), and `provesAll_ne_cax_ex` shows that this hypothesis is needed.
* **Monotonicity is a hypothesis.** `entails_monoWrt` needs `satAx` to be antitone along the
  relation, and nothing makes an arbitrary satisfaction monotone.
* **Morphisms.** A `Satisfaction.Hom` maps contexts and conclusions forwards and models
  backwards, with a satisfaction condition for each relation. It gives a sound translation,
  functorially (`Hom.toTranslation_id`, `Hom.toTranslation_comp`). If the model map is
  surjective, the translation is conservative.
* **Rooms (fixed-signature institutions).** `roomSatisfaction R` has contexts `Set R.Sen`, and
  its entailment is `Room.Entails` (`roomSatisfaction_entails`). A corridor gives a morphism
  through its satisfaction condition, and `roomSys : Room ⥤ Sys` is a functor. This is the
  only place where institution laws are used, and they are the corridor's satisfaction
  condition. Model morphisms are forgotten.
* **Institutions.** The target is the existing category `Room.category`
  (`Silmaril.Logic.Institution.Room`), where corridors translate sentences forwards and reduce
  models backwards.
  * An institution `I : Sign ⥤ Room` gives `institutionSys I := I ⋙ roomSys`, one system per
    signature and one translation per signature morphism.
  * A `ClassicInstitution` (`Sen : Sign ⥤ Type`, `Mod : Signᵒᵖ ⥤ Cat`) goes through
    `toRoomFunctor` to `classicInstitutionSys`. Its system at `Σ` is `(I.room Σ).Entails`, and
    `σ` translates conclusions by `I.Sen.map σ`, both by `rfl`.
  * The result is covariant in signatures. The model functor enters only through the
    satisfaction condition.

## Acceptors

A language `L : Set _` (the convention of `Silmaril.Accept`) lifts to a system in four ways.
Each lift is the least system with its property (`…_le_iff`):

| lift | judgements | language recovered as |
|---|---|---|
| `liftAxFF L ff` | `a ⊢ ff` for accepted `a` | `{a | a ⊢ ff}` |
| `liftTTC tt L` | `tt ⊢ c` for accepted `c` | `{c | tt ⊢ c}` |
| `liftAxAll L` | `a ⊢ c` for accepted `a`, every `c` | `{a | ProvesAll a}`, only if `C` is nonempty |
| `liftCAll L` | `a ⊢ c` for every `a`, accepted `c` | `{c | a ⊢ c}` for any `a` |

## Modules and ownership

| module | contents | owner |
|---|---|---|
| `Silmaril/Logic/Consequence/Defs.lean`, `Thms.lean` | systems, order, consistency notions | core |
| `Silmaril/Logic/Consequence/Translation/{Defs,Thms}.lean` | translations, `Sys`, `WSys`, erasure functor | core |
| `Silmaril/Logic/Consequence/Ax/{Defs,Thms}.lean` | context shapes and their maps | core |
| `Silmaril/Logic/Consequence/Semantic/{Defs,Thms}.lean` | satisfaction, SZS, rooms, institutions | core |
| `Silmaril/Logic/Consequence/Accept/{Defs,Thms}.lean` | acceptor lifts | core |
| `Silmaril/Logic/Consequence/Examples.lean` | worked examples | core |
| `Silmaril/Logic/Consequence/Structural/…` | structural rules and derivation closures | structural derivations |
| Wasm acceptor and SZS protocol modules | Wasm evidence for the lifts | Wasm/SZS protocols |
| explorer pages, [consequence-systems.md](consequence-systems.md) | presentation and master roadmap | explorer/examples |

## Next steps for the core

* A signature-indexed version of `Satisfaction` (a functor `Sign ⥤` satisfactions) whose
  restriction to rooms is `institutionSys`.
* Whether conservative translations reflect `ProvesAll` and `ConsistentWrt`, and which
  structural properties pullbacks preserve, once the structural track has fixed its closures.

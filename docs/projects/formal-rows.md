# Formal rows: interpretation, soundness and consistency of concrete logics

This page tracks the request to make the consistency and soundness of the logics explorable and
statable, over the abstract syntax and over S-expressions. The rows are first-order logic, Peano
arithmetic and second-order arithmetic (top priority), then HOL, then MLTT. It records what is
proved, under which assumptions, what is only defined, and what is not done yet. Every result is
relative to Lean's own consistency (with `propext`, `Classical.choice`, `Quot.sound`) and to the
models named; none claims consistency of an arbitrary extension by further axioms.

## The framework (`Silmaril.Logic.Consequence.Soundness`, `Silmaril.Logic.Concrete.Codec`)

| notion | Lean | reading |
|---|---|---|
| interpretation | `Satisfaction Ax C` (existing) | models, satisfaction of contexts and conclusions |
| satisfiability | `Satisfaction.Satisfiable`, `Room.Satisfiable` | some model satisfies the context / theory |
| soundness | `System.SoundFor S I` | `S ≤ I.entails` |
| consistency | `System.ConsistentWrt S ff Γ` (existing), `ER.ConsistentWrt` | `Γ` does not derive the chosen falsity `ff` |
| nontriviality | `System.ContextConsistent` (existing), `ER.Nontrivial` | some conclusion is not derived |
| bridge | `consistentWrt_of_sound`, `ER.consistentWrt_of_sound` | sound + a model of `Γ` falsifying `ff` ⇒ consistent |
| transport | `consistentWrt_of_translation` | consistency transports backwards along a translation |
| concrete syntax | `SExpCodec A`, `System.viaCodec`, `viaCodec_consistentWrt_iff` | a system read over a presentation is consistent exactly when the abstract one is |

**Presentations.** A logic's identity is its abstract syntax; an `SExpCodec` is one named,
versioned presentation of it (`name`, `version`, `encode`, a `decode` that accepts exactly the
canonical forms). A logic can have several: `SExpCodec.rename c σ` renames atoms by a bijection, and
the renaming *induces* the identity on abstract syntax (`rename_induces`): the simplest
S-expression morphism. `SExpCodec.Induces c₁ c₂ m f` states that an S-expression map `m` computes a
map `f` of abstract syntax; this is the shape of the institution morphisms that are simple
S-expression morphisms, with no claim that every morphism has it.

## Registry and explorer

Four record kinds (`Silmaril.Project.Registry.Formal.Defs`). In each, Lean checks the claim from
the theorem's **type**, never from its name:

| kind | Lean checks | the record keeps |
|---|---|---|
| `presentation N := c` | `c : SExpCodec A` | the codec's own name and version (reduced from `c`), `A`, default flag |
| `logic_property N := t (role := r) (system := S)` | `t`'s statement has the role's shape for the registered system: soundness `System.SoundFor S I`, consistency `System.ConsistentWrt S ff Γ`, nontriviality `System.ContextConsistent S Γ`, satisfiability `Room.Satisfiable` / `Satisfaction.Satisfiable`, inclusion `S ≤ T` | statement, interpretation / falsity / context, axioms |
| `logic_problem N := φ (presentation := P)` | each claim theorem is about `φ`: `S Γ φ` (derived, entailed) or `I.satC m φ` (true) | the S-expression of `φ` in every registered presentation of its abstract syntax, computed by running the printers |
| `logic_row N` | every referenced record exists | systems, interpretations, presentations, properties, problems, variant |

`Silmaril.LogicGraph.Consequence.Formal.Defs` registers five rows: FOL, PA, second-order
arithmetic, HOL and extensional MLTT. The explorer page `#/formal/` puts them in a table, with
FOL, PA and second-order arithmetic first. `#/formal-row/<name>` shows one row; problems,
properties and presentations each have a page of their own. A problem's page switches between
presentations and keeps the choice in the URL. The browser suite is
`tools/silmaril-project/tests/explore/formal.mjs`.

## Acceptance matrix

✓ proved · ◆ defined · ◇ conditional (on a stated hypothesis) · — not done

| row | abstract syntax | presentations | derivation (proof objects) | interpretation | soundness | consistency | concrete problems |
|---|---|---|---|---|---|---|---|
| **FOL** (unsorted; signature `orderSig`) | ◆ `UFOL.Formula` (existing) | ◆ `silmaril.fol.formula` v1 over named signatures (arity-checked; `decodeFormula_eq_some_iff` ✓) | — none yet | ◆ one specified structure (`inStructure natStructure`, ℕ) and all structures (`consequence`) | — (no derivations) | ✓ model existence `orderTheory_satisfiable`; ✓ nontrivial consequence `orderTheory_nontrivial` | ✓ `orderTheory_entails_succIrrefl` (every structure), `succIrrefl_true` (ℕ) |
| **PA** (and Q) | ◆ `Arithmetic.Formula` (existing) | ◆ `silmaril.arithmetic.formula` v1 (default), `….words` v1; ✓ bytes round trip for every formula | ◆ `PAProof`, `QProof` (existing natural deduction) | ◆ standard model ℕ (`standard`) | ✓ `pa_soundFor`, `q_soundFor` | ✓ `pa_consistent`, `q_consistent`, `paConcrete_consistent` | ✓ `zeroAddZero`, `zeroOrSuccessor` (decoded, derived, true in ℕ) |
| **Second-order arithmetic**: `RCA0`, `WKL0Sep` (Σ⁰₁ separation), `ACA0`, `Z2`, `Z2Full` | ◆ `SecondOrderArithmetic.Formula` (existing, named) | ◆ `silmaril.soa.formula` v1 | ◆ `Proof` (existing Hilbert), `HProof` with hypotheses | ◆ **full** standard (`full`: ℕ and every subset) and **Henkin** (`henkin S`: structures validating `S`'s axioms) | ✓ `derives_soundFor_full`, `derives_soundFor_henkin` | ✓ `consistent S` for every subsystem, `concrete_consistent` | ✓ `succNeZero` (RCA0), `comprehensionEq` (Z2) |
| **HOL** (HOL Light kernel) | ◆ existing | ◆ `silmaril.hol-light.term` v1 | ◆ `HOLLight.Derives` (existing) | ◆ existing standard models (`Model`, full function spaces in `Type u`) | ✓ existing `Derives.sound` | ✓ existing `classical_consistent` (ETA, SELECT, INFINITY) | — next stage |
| **Extensional MLTT** | ◆ existing | ◆ `silmaril.mltt.judgment` v1 | ◆ existing | ◆ existing ZFSet towers | ✓ existing (bounded heights) | ✓ existing, heights 1–3 | — next stage |

`WKL0Sep` is RCA0 with Σ⁰₁ separation; its equivalence to weak König's lemma is not proved. `Z2`
and `Z2Full` prove the same formulas (`z2_full_provable_iff`, existing). Full second-order
semantics uses all subsets of ℕ; Henkin semantics allows nonstandard numbers and fewer sets.
Completeness is claimed for none of these.

**New results in this stage.** Native second-order consistency was missing: every axiom of every
subsystem is valid in the full standard model (`SecondOrderArithmetic.validAxioms_fullStandard`),
which gives `SecondOrderArithmetic.consistent` and the row's consistency. Before, consistency was
known only for the Metamath `z2.mm` presentation.

## Audit (before this stage)

**HOL Light** (`Silmaril.Logic.HOLLight`). Standard semantics are genuine:
- `bool` is `ULift Bool` and `ind` is `ULift ℕ`;
- arrows are the full Lean function space and `=` is Lean equality;
- `@` is Hilbert choice, via `Classical.choose`.

Soundness is `Derives.sound : Derives sig theory H p → Models M theory → Entails M H p`, for every
model in `Type u`. Consistency is `classical_consistent : ¬ Derives initialSignature classicalTheory ∅ Tm.falsity`,
where the theory is ETA_AX, SELECT_AX and INFINITY_AX, with the standard model at universe 0. The
kernel has no definition rules. The values of typed terms exist (`HasType.eval_exists`) and are
unique (`Eval.unique`), but there is no total denotation function with typing evidence: that is
the next stage.

**Extensional MLTT.** It is sound and consistent for bounded universe heights in ZFSet towers:
`FiniteTower.one/two/three`, at Lean universes 1–3, so no inaccessibles are assumed. For example,
`ECtx.JEqB.consistent_one`. The unbounded system is sound only relative to an assumed
`SetHierarchy`, which is never constructed, so its consistency is not proved.

**Intensional MLTT (original rules, J, unbounded cumulative universes).** Consistency is
`RawRealizability.empty_consistency`, by term realizability. That is a genuine model, but a
syntactic one, not a Lean-type model.

**λΠ.** Its library "semantics" is closed theories, which coincide with derivability by
construction, so it says nothing semantic.

**Lean-NDJSON.** This is lean4export's NDJSON export format, version 3.1.0 (`format_ndjson.md`
upstream):
- a `meta` header;
- separate name, level and expression tables (`in`, `il`, `ie`), with dense ids that refer only
  backward;
- declarations keyed by name.

moria-lean has a typed decoder and a reference validator for it (`Formats/LeanNDJSON/Events`). The
indexed derivation format will follow this format rather than invent a JSONL schema.

## Not done yet (exact obligations)

1. HOL and MLTT rows state their consistency in this framework: the library's
   `HOLLight.classical_consistent` and `ECtx.JEqB.consistent_one` are not yet
   `System.ConsistentWrt` statements.
2. **A FOL derivation system** with proof objects and soundness, generalizing
   `Arithmetic.Derivation` to an arbitrary signature.
3. **HOL**:
   - a total standard denotation of typed terms into Lean values, with typing evidence;
   - composition with parsing and type checking of S-expressions;
   - concrete HOL problems with checked kernel derivations and their standard meaning.
4. **MLTT**: the low fixed-universe interpretation over the AST and S-expressions, and consistency
   rows for the supported variants as audited above.
5. **Derivation systems**: explicit derivation objects with rule instances, a checker and
   soundness, integrated with `System`/`WSystem` and institutions, and explorable.
6. **Proof formats**:
   - an S-expression derivation syntax;
   - Lean-NDJSON indexed derivations, with reference validation and a checked translation;
   - a documented Alethe fragment with an adapter that rejects unsupported rules.
7. Standard JSON and DASL syntaxes are future plans, outside this scope.

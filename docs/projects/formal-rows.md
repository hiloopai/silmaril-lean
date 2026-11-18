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

## Derivation systems (`Silmaril.Logic.Consequence.Derivation`)

A **derivation system** `D : DerivationSystem J` has rule labels `D.Rule` and rule instances
`D.Instance r ps c` (rule `r` concludes `c` from the premises `ps`). A label names a rule
*instance*, with the data it needs, so checking one step is decidable.

| notion | Lean | reading |
|---|---|---|
| proof objects | `ProofTree R J` (`assume j`, `infer r c ts`); `Line R J` (`assume j`, `infer r c prems`) | trees, and indexed lines citing earlier lines by position (the Alethe / NDJSON shape) |
| validity | `D.Valid Γ t`, `D.LinesValid Γ prev ls` | every leaf in `Γ`; every node an instance of its rule |
| consequence | `D.derives : System (List J) J`, `D.proofs` (a `WSystem`), `D.linearDerives` | some valid proof from `Γ` concludes `c` |
| checker | `D.check`, `D.checkLines`; `check_iff`, `checkLines_iff` | Boolean checkers that decide validity exactly |
| structure | `derives_closed` | identity, weakening along `⊆`, multi-cut (by grafting proofs onto leaves) |
| formats agree | `linearDerives_eq` (`ProofTree.lines` flattens a tree) | lines and trees derive the same judgments |
| soundness | `LocallySound sat` ⇒ `derives_soundFor : D.derives.SoundFor (listSat M sat)` | every rule preserves truth in each model |
| consistency | `consistentWrt_of_locallySound` | a model of `Γ` falsifying `ff` |
| elaboration | `ProofTree.elaborate`, `Line.elaborate`; `derives_of_elaborate`, `derives_of_elaborateLines` | raw labels (a rule name and a few arguments) become rule labels by an *untrusted* function; the result is checked |

**Proof formats** (`Silmaril.Logic.Consequence.Derivation.SExp`), generic in the presentation of
judgments; the readers invert the encoders, so both are presentations (`SExpCodec`):

```
silmaril.derivation.tree  v1:  tree ::= (assume J) | (infer RULE J tree*)
silmaril.derivation.lines v1:  (proof line*)   line ::= (assume J) | (infer RULE J (i*))
```

**PA and Q** (`Silmaril.Logic.Consequence.Arithmetic.Derivation`): judgments `Seq` (`Γ ⊢ φ` with
`n` variables, presentation `silmaril.arithmetic.sequent` v1: `(seq n (φ*) ψ)`); rule instances
`Rule n` (every rule of `Derivation`, each determining its premises and conclusion; side
conditions for `hyp`, `weaken` and the theory's axioms).

* `locallySound_derivable`, `locallySound_valid`: every rule instance is a `Derivation` step, and
  valid in ℕ.
* `treeDerives_pa : treeDerives .pa = paDerives`, `treeDerives_q : treeDerives .q = qDerives`:
  tree-checked proofs derive exactly what the existing natural deduction derives.
* `treeDerives_soundFor`, `pa_tree_consistent`, `q_tree_consistent`.
* `checkTree`, `checkLines` (and `…Bytes`): decode, elaborate (`elabRule`), check; rejections
  name the stage (`syntax`, `elaboration`, `check`, `empty`). `checkTree_sound`,
  `checkLines_sound`: an accepted proof is a derivation.
* Kernel-checked examples (`…Derivation.Examples`): `⊢ 0 + 0 = 0`; `∀`-elimination (trees and
  lines); `⊢ ∀x ∀y. x = y → y = x`; `⊢ ∀x. 0 + x = x` **by induction** (PA accepts; Q rejects);
  six rejections (wrong axiom conclusion, unknown rule, missing hypothesis, forward citation, empty
  lines, not a proof) and byte-level syntax errors.

## Registry and explorer

Six record kinds (`Silmaril.Project.Registry.Formal.Defs`). In each, Lean checks the claim from
the theorem's **type**, never from its name:

| kind | Lean checks | the record keeps |
|---|---|---|
| `presentation N := c` | `c : SExpCodec A` | the codec's own name and version (reduced from `c`), `A`, default flag |
| `logic_property N := t (role := r) (system := S)` | `t`'s statement has the role's shape for the registered system: soundness `System.SoundFor S I`, consistency `System.ConsistentWrt S ff Γ`, nontriviality `System.ContextConsistent S Γ`, satisfiability `Room.Satisfiable` / `Satisfaction.Satisfiable`, inclusion `S ≤ T` | statement, interpretation / falsity / context, axioms |
| `logic_problem N := φ (presentation := P)` | each claim theorem is about `φ`: `S Γ φ` (derived, entailed) or `I.satC m φ` (true) | the S-expression of `φ` in every registered presentation of its abstract syntax, computed by running the printers |
| `logic_row N` | every referenced record exists | systems, interpretations, presentations, properties, problems, derivation systems, derivations, variant |
| `derivation_system N := D (arg := a)` | `D a : DerivationSystem J`; `judgments` presents `J`; each of `formats` presents proof trees or lines over `J`; `locally_sound` states `D.LocallySound sat`; `agrees` states `X = S` for the registered system `S` | `J`, the claims with statements and axioms |
| `derivation N := p (presentation := P) (system := D)` | `p` is a proof tree of `P`'s type; each of `verdicts` states `check e = r` where `e` encodes `p` (as a tree, or flattened into lines) in a registered format; `derives` states `S Γ φ` | renderings in every tree and lines format, the indexed steps (rule, judgment, cited lines) and the conclusion (by evaluation), each verdict's checker, result and stage |

`Silmaril.LogicGraph.Consequence.Formal.Defs` registers five rows: FOL, PA, second-order
arithmetic, HOL and extensional MLTT. The explorer page `#/formal/` puts them in a table, with
FOL, PA and second-order arithmetic first. `#/formal-row/<name>` shows one row; problems,
properties and presentations each have a page of their own. A problem's page switches between
presentations and keeps the choice in the URL. `#/derivation-system/<name>` shows a derivation
system's checked claims; `#/derivation/<name>` shows a proof's verdicts (accepted, or rejected with
the stage), its proof tree, its indexed steps (hovering a step highlights its premises) and its
S-expression in each format (kept in the URL). The browser suite is
`tools/silmaril-project/tests/explore/formal.mjs`.

## Acceptance matrix

✓ proved · ◆ defined · ◇ conditional (on a stated hypothesis) · — not done

| row | abstract syntax | presentations | derivation (proof objects) | interpretation | soundness | consistency | concrete problems |
|---|---|---|---|---|---|---|---|
| **FOL** (unsorted; signature `orderSig`) | ◆ `UFOL.Formula` (existing) | ◆ `silmaril.fol.formula` v1 over named signatures (arity-checked; `decodeFormula_eq_some_iff` ✓) | — none yet | ◆ one specified structure (`inStructure natStructure`, ℕ) and all structures (`consequence`) | — (no derivations) | ✓ model existence `orderTheory_satisfiable`; ✓ nontrivial consequence `orderTheory_nontrivial` | ✓ `orderTheory_entails_succIrrefl` (every structure), `succIrrefl_true` (ℕ) |
| **PA** (and Q) | ◆ `Arithmetic.Formula` (existing) | ◆ `silmaril.arithmetic.formula` v1 (default), `….words` v1; ✓ bytes round trip for every formula | ◆ `PAProof`, `QProof` (existing natural deduction); ✓ as a derivation system with checked proof trees and lines (`treeDerives_pa`, `treeDerives_q`), S-expression proofs `silmaril.derivation.tree` / `….lines` | ◆ standard model ℕ (`standard`) | ✓ `pa_soundFor`, `q_soundFor` | ✓ `pa_consistent`, `q_consistent`, `paConcrete_consistent` | ✓ `zeroAddZero`, `zeroOrSuccessor` (decoded, derived, true in ℕ) |
| **Second-order arithmetic**: `RCA0`, `WKL0Sep` (Σ⁰₁ separation), `ACA0`, `Z2`, `Z2Full` | ◆ `SecondOrderArithmetic.Formula` (existing, named) | ◆ `silmaril.soa.formula` v1 | ◆ `Proof` (existing Hilbert), `HProof` with hypotheses | ◆ **full** standard (`full`: ℕ and every subset) and **Henkin** (`henkin S`: structures validating `S`'s axioms) | ✓ `derives_soundFor_full`, `derives_soundFor_henkin` | ✓ `consistent S` for every subsystem, `concrete_consistent` | ✓ `succNeZero` (RCA0), `comprehensionEq` (Z2) |
| **HOL** (HOL Light kernel, initial signature) | ◆ existing; ✓ type checker `Tm.typeOf?` sound and complete | ◆ `silmaril.hol-light.prop` v1 (decode, type-check, require `bool`; errors exact: `decodeProp_eq_none_iff`), `silmaril.hol-light.term` v1 | ◆ `HOLLight.Derives` (existing), on propositions `kernel`, `kernelFrom … classicalTheory` | ◆ standard models (`points`: model in `Type u`, type valuation, assignment); `denote` of typed terms; `standardPoint` | ✓ `kernel_soundFor` | ✓ `kernel_consistent` (pure), `classical_consistent'` (ETA, SELECT, INFINITY) | ✓ `truthProp`, `reflProp` (derived, true), `emProp` (derived from the classical axioms) |
| **MLTT** | ◆ existing | ◆ `silmaril.mltt.judgment` v1 (extensional) | ◆ existing (`ECtx.JEqB`, `ECtx.JEqH`, original intensional rules) | ◆ ZFSet towers (extensional), realizability (intensional) | ✓ existing (as inclusions) | ✓ nontriviality: extensional with 1, 2, 3 universe levels (`bounded_consistent_one/two/three`), intensional with J at every stage (`intensional_consistent`) | — |

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

1. **A FOL derivation system** with proof objects and soundness (generalize `Arithmetic.Derivation`
   to an arbitrary signature); FOL's row has semantics and model existence only.
2. **HOL**: the standard interpretation is stated for the initial signature; HOL problems over
   user signatures and constants (with a model interpreting them) are not registered yet. The
   kernel has no definition rules.
3. **MLTT**:
   - The standard interpretation in Lean types at fixed low universes is not done; the existing
     models are ZFSet towers (extensional) and realizability (intensional).
   - MLTT problems are not registered.
   - Unbounded extensional MLTT is sound only relative to an assumed `SetHierarchy`, so its
     consistency is not claimed.
4. **Derivation systems**: the framework, checkers, PA/Q instance, and registry, database and
   explorer pages are done (above). Not yet done: second-order arithmetic, HOL and MLTT as
   derivation systems; derivation-system morphisms.
5. **Proof formats**:
   - the S-expression tree and lines formats are done, with PA/Q elaboration;
   - Lean-NDJSON (lean4export 3.1.0 files of real derivation declarations, decoded with
     reference validation and independently checked) is not done;
   - a documented Alethe fragment with an adapter that rejects unsupported rules is not done.
6. Standard JSON and DASL syntaxes are future plans, outside this scope.

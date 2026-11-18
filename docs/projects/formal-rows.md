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

## First-order natural deduction (`Silmaril.Logic.Consequence.FirstOrder.Derivation`)

Over any unsorted signature whose symbols of each arity have decidable equality (named signatures
do), with judgments `Γ ⊢ φ` at `k` variables and rule instances carrying their data
(`FirstOrder.ND.Rule`): hypothesis, weakening along `⊆`, `⊤`-introduction, `¬`-introduction (from
`ψ` and `¬ψ`), `¬`-elimination (explosion), double negation, the `∧` rules, `∀`-introduction and
elimination, equality reflexivity and elimination. The syntax operations it needs (renaming,
substitution, `shift`, `inst`, decidable equality) are `…FirstOrder.Syntax`, with
`holds_subst`, `holds_shift`, `holds_inst`.

* `locallySound`: every rule instance preserves validity in every structure; hence
  `treeDerives_le_consequence` and `treeDerives_soundFor M`.
* `orderTheory_tree_consistent`: over `orderSig`, the order theory does not derive `¬⊤` (model ℕ).
* Concrete syntax: `silmaril.fol.sequent` v1, the tree and lines formats, `elabRule`, and
  `checkTree` / `checkLines` with `checkTree_sound`, as for PA.
* Kernel-checked proofs (`…Derivation.Examples`): `orderTheory ⊢ ∀x ¬ succ x < succ x` (trees and
  lines), `⊢ ∀x ∀y ¬(x = y ∧ ¬ y = x)`, and three rejections. All are registered on the FOL row.

## Lean-NDJSON: lean4export files of proof declarations (`Silmaril.ProofFormats.LeanNDJSON`)

**The format** is lean4export's NDJSON, format version **3.1.0** (`.lake/packages/mathlib/lean4export`,
the exporter the pinned Mathlib vendors; its `format_ndjson.md` is the specification). A file is a
metadata line, then name (`in`), level (`il`) and expression (`ie`) table records and declaration
records (`axiom`, `def`, `thm`, `opaque`, `quot`, `inductive` blocks).

**Decoding and validation** (`Silmaril.Formats.LeanNDJSON`, region Formats; the event types, strict
decoder and reference validator are adapted from the moria project's Lean-NDJSON decoder, with
the `quot` and `inductive` records added):

* `parseFile`: strict JSON decoding of every record (exact keys, non-negative ids, 3.1.0 shapes
  only; `mdata` is refused); errors name the line.
* `SerialValid` / `serialValid?` (`serialValid?_iff`): each record defines the next id of its
  table and refers only to entries written before it, which excludes duplicates, forward
  references and cycles; `Valid` adds distinct declared names (`validate?_iff`).

**Import** (`…ProofFormats.LeanNDJSON.Arithmetic`, region ProofFormats, which depends on Logic and
Formats): `importCheck T bytes d` decodes and validates the file, requires `d` to be a `def` with no
universe parameters (an axiom, theorem, opaque, quotient or inductive is refused), translates its
**value** by a fixed table of constructors (proof trees, lists, `SE`, `Seq`, formulas, terms,
numerals and string literals, and parameterless definitions in the file) into
`silmaril.derivation.tree`, and checks that with `checkTree T`. The declared type and the metadata
are never used as evidence. `importCheck_sound`: an accepted declaration is a derivation of the
reported judgment, from a `Valid` file.

**The fixture** `tests/lean-ndjson/pa-derivations.ndjson` (14 636 records) is lean4export's output,
run with no options (no `--export-unsafe`, `--export-mdata` or `--ignore-missing`), for the proof
declarations of `…Arithmetic.Derivation.Exported` (constructor normal form, each `rfl`-equal to its
`Examples` proof) and for `Examples.zeroAdd`. `scripts/lean-ndjson/export-fixtures.sh` regenerates
it, and `--check` compares a fresh export with it. `…LeanNDJSON.Arithmetic.Examples` reads it at
build time: five accepted imports with the Lean proof objects' conclusions, two checker
rejections, four refusals before checking (an unsupported encoding, a formula that is not a proof,
a λ-abstraction, a missing name), a declaration turned into an axiom or a theorem, a replaced
declared type (no effect) and a replaced value (a different conclusion), and seven byte mutations
of the real file (a duplicated record, a forward reference, a self-reference, an unknown field,
`mdata`, a wrong format version, an empty line), each refused with its reason.

## Alethe: a propositional fragment, with real cvc5 proofs (`Silmaril.ProofFormats.Alethe`)

**The clause system** (`Silmaril.Logic.Consequence.Resolution`): judgments are clauses of SMT terms;
a valuation interprets atoms, and `true`, `false`, `not`, `or`, `and` are interpreted (every other
term is an atom, so only **propositional** reasoning is claimed). Rules: `resolution` with explicit
pivots, `orElim`, `andElim`, `notOrElim`, `orPos`, `orNeg`, `andPos`, `andNeg`, `contraction`,
`trueTaut`, `falseTaut`; a step is an instance when its computed conclusion is a subset of the
stated one. `locallySound`, and `refutes_units`: the empty clause derived from asserted formulas
shows that no valuation satisfies them.

**The adapter**: `checkRefutation problem proof` reads an SMT-LIB problem (assertions; `define-fun`
and other meaning-changing commands are refused) and an Alethe proof (`assume`, and `step` with
`:rule`, `:premises`, `:args`), expands `(! t :named @n)` sharing, maps premise names to earlier
lines, elaborates each supported rule (untrusted), and checks the lines against the assertions;
the proof must end with `(cl)`. Unsupported rules (theory rules, `trust`, …), subproofs (`anchor`,
`:discharge`), resolution without pivots, unknown or later premises, and assumptions that are not
assertions are refused by name. `checkRefutation_sound`: an accepted proof refutes the problem's
assertions.

**Fixtures** (`tests/alethe/cvc5-1.4.2/`): five problems and the proofs the official cvc5 1.4.2
static release printed for them, plus one printed without `--proof-alethe-res-pivots`;
`receipt.json` records the release archive and executable hashes, the exact arguments and limits,
and every file's hash. `scripts/alethe/check-fixtures.sh` verifies the hashes and, given the
executable (`CVC5=…`), regenerates every proof and compares. At build time
(`…Alethe.Examples`): four refutations accepted (`or_pos`, `or`, `and`, resolution chains, `:named`
sharing); the theory proof (`not_symm`) and the pivot-less proof refused; six mutations of the
real files refused with their reasons.

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
| **FOL** (unsorted; signature `orderSig`) | ◆ `UFOL.Formula` (existing); ✓ renaming, substitution, decidable equality (`…FirstOrder.Syntax`) | ◆ `silmaril.fol.formula` v1 over named signatures (arity-checked; `decodeFormula_eq_some_iff` ✓); ✓ `silmaril.fol.sequent` v1 and the proof formats | ✓ classical natural deduction over any signature with decidable symbols (`FirstOrder.ND.system`), checked trees and lines | ◆ one specified structure (`inStructure natStructure`, ℕ) and all structures (`consequence`) | ✓ `treeDerives_le_consequence` (every structure), `treeDerives_soundFor` (ℕ), by `locallySound` | ✓ model existence `orderTheory_satisfiable`; ✓ nontrivial consequence `orderTheory_nontrivial`; ✓ `orderTheory_tree_consistent` | ✓ `orderTheory_entails_succIrrefl`, `succIrrefl_true`; ✓ `succIrrefl_derives` (a checked proof, trees and lines), `eqSymm_derives` |
| **PA** (and Q) | ◆ `Arithmetic.Formula` (existing) | ◆ `silmaril.arithmetic.formula` v1 (default), `….words` v1; ✓ bytes round trip for every formula | ◆ `PAProof`, `QProof` (existing natural deduction); ✓ as a derivation system with checked proof trees and lines (`treeDerives_pa`, `treeDerives_q`), S-expression proofs `silmaril.derivation.tree` / `….lines` | ◆ standard model ℕ (`standard`) | ✓ `pa_soundFor`, `q_soundFor` | ✓ `pa_consistent`, `q_consistent`, `paConcrete_consistent` | ✓ `zeroAddZero`, `zeroOrSuccessor` (decoded, derived, true in ℕ) |
| **Second-order arithmetic**: `RCA0`, `WKL0Sep` (Σ⁰₁ separation), `ACA0`, `Z2`, `Z2Full` | ◆ `SecondOrderArithmetic.Formula` (existing, named) | ◆ `silmaril.soa.formula` v1 | ◆ `Proof` (existing Hilbert), `HProof` with hypotheses | ◆ **full** standard (`full`: ℕ and every subset) and **Henkin** (`henkin S`: structures validating `S`'s axioms) | ✓ `derives_soundFor_full`, `derives_soundFor_henkin` | ✓ `consistent S` for every subsystem, `concrete_consistent` | ✓ `succNeZero` (RCA0), `comprehensionEq` (Z2) |
| **HOL** (HOL Light kernel, initial signature) | ◆ existing; ✓ type checker `Tm.typeOf?` sound and complete | ◆ `silmaril.hol-light.prop` v1 (decode, type-check, require `bool`; errors exact: `decodeProp_eq_none_iff`), `silmaril.hol-light.term` v1 | ◆ `HOLLight.Derives` (existing), on propositions `kernel`, `kernelFrom … classicalTheory` | ◆ standard models (`points`: model in `Type u`, type valuation, assignment); `denote` of typed terms; `standardPoint` | ✓ `kernel_soundFor`; ✓ `kernelFrom_soundFor` (models of a theory, any signature) | ✓ `kernel_consistent` (pure), `classical_consistent'` (ETA, SELECT, INFINITY); ✓ `cTheory_consistent` (user signature `coinSig`, axiom `c`) | ✓ `truthProp`, `reflProp` (derived, true), `emProp` (derived from the classical axioms); ✓ `cProp`, `cReflProp` over `coinSig` |
| **MLTT** | ◆ existing | ◆ `silmaril.mltt.judgment` v1 (extensional); ✓ `silmaril.mltt.judgment.bounded` v1 (`boundedCodec`) | ◆ existing (`ECtx.JEqB`, `ECtx.JEqH`, original intensional rules) | ◆ ZFSet towers (extensional), realizability (intensional); ✓ `boundedTowers levels`, the finite-tower interpretation at fixed low universes | ✓ `bounded_soundFor_one/two/three`; ✓ existing (as inclusions) | ✓ nontriviality: extensional with 1, 2, 3 universe levels (`bounded_consistent_one/two/three`), intensional with J at every stage (`intensional_consistent`); ✓ `⊢ 0 : 𝟘` not derivable (`bounded_empty_consistent_one/two/three`) | ✓ `⊢ 0 : ℕ` (`bounded_zero_derived`, `bounded_zero_true`) |

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

1. **FOL**: the derivation system is done (natural deduction for `=`, relations, `⊤`, `¬`, `∧`,
   `∀` over any signature with decidable symbols, sound for every structure). Completeness is not
   claimed; disjunction, implication and `∃` are not primitive in this syntax (they are defined
   connectives), and FOL proofs are not imported from Lean-NDJSON yet.
2. **HOL**: done over a user signature too (`…HOL.UserSig`): `pointsOf S Δ` restricts the standard
   interpretation to models of a theory, `kernelFrom_soundFor` holds over any signature, and over
   `coinSig` (one boolean constant `c`) the theory `c` is consistent by the model `c ↦ true`, with
   two registered problems (`c` from its axiom; `c = c` by REFL). Not done: the kernel has no
   definition rules (`new_definition`, `new_type_definition`), and HOL is not yet a derivation
   system with explicit proof objects in the sense of `…Derivation`.
3. **MLTT**:
   - Done: bounded extensional MLTT (1, 2, 3 universe levels) is sound for its finite ZFSet towers
     at fixed low universes (`bounded_soundFor_*`), does not derive `⊢ 0 : 𝟘`, and has a registered
     problem (`⊢ 0 : ℕ`, derived and true in every tower).
   - Not done: an interpretation in Lean *types* (rather than ZFSets). The syntax is untyped and
     derivability is a `Prop`-valued relation, so a type-valued interpretation would recurse into
     typing derivations as data; that is a separate development, deliberately not started here.
   - Unbounded extensional MLTT is sound only relative to an assumed `SetHierarchy`, so its
     consistency is not claimed.
4. **Derivation systems**: the framework, checkers, PA/Q instance, and registry, database and
   explorer pages are done (above). Not yet done: second-order arithmetic, HOL and MLTT as
   derivation systems; derivation-system morphisms.
5. **Proof formats**:
   - the S-expression tree and lines formats are done, with PA/Q elaboration;
   - Lean-NDJSON is done for PA and Q (above); other logics' proof objects are not imported yet,
     and kernel-level checking of the exported environment (typing of declarations) is out of
     scope;
   - the Alethe fragment is done for propositional reasoning (above); theory rules (equality,
     arithmetic, quantifiers) and subproofs are refused, not checked.
6. Standard JSON and DASL syntaxes are future plans, outside this scope.

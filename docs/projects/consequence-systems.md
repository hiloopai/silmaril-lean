# Consequence systems in a silmaril project

A project can name **consequence systems** — `Silmaril.Consequence.System Ax C`, relations
`S : Ax → C → Prop` from contexts to conclusions, `S Γ φ` read `Γ ⊢ φ`
(`Silmaril.Logic.Consequence.Defs`) — say how each was built, and ask the standard questions
about them as ordinary project problems, answered by Lean proofs. It reuses the registry's
problems, instances, answers and statuses (`@[answers "N" thm|sat|uns|csa]`); nothing here
adds a status or a tag.

This page is the presentation and roadmap of the consequence-system work; the core API
(`System`, `WSystem`, `Sound`, `Complete`, `pullback`, `Translation`, consistency notions) is
described in [consequence.md](consequence.md), and checkers and SZS protocols in
[consequence-protocols.md](consequence-protocols.md).

| Piece | Where |
| --- | --- |
| Record kind `consequence_system` | `Silmaril.Project.Registry.Consequence.Defs` |
| Standard shapes `silmaril.shapes.consequence.*` | `Silmaril.Project.Shapes.Consequence.Defs`, readings in `….Thms` |
| Worked fixture (the self-test) | `examples/project/ProjectSelfTest/Consequence.lean` |
| Database tables | `tools/silmaril-project/src/project/schema/consequence.rs` |
| Explorer page | `tools/silmaril-project/src/project/explore/views/systems.js` (`#/systems`, `#/system/<name>`) |
| Browser test | `tools/silmaril-project/tests/explore/systems.mjs` |

## What a system is

`Ax` is any type of contexts — a finite list `C₁, …, Cₙ`, a finite set, a single formula — and
`C` any type of conclusions. **No structural rule is implicit**: a system is reflexive
(`φ ∈ Γ → Γ ⊢ φ`), monotone or closed under cut only when a proof says so. The registry checks
types only (`Ax → C → Prop`, universe-monomorphic); every property is a problem.

A **witness system** `W : Ax → C → Type` (a `WSystem`) gives a type of derivations of each
`Γ ⊢ φ`; it is registered through its erasure `WSystem.erase W` (`Nonempty (W Γ φ)`), so that a proof of `Γ ⊢ φ` is a
derivation and a refutation shows that no derivation exists.

## Registering systems

```lean
-- an existing definition (op := decl, the default)
silmaril consequence_system my.raw := My.raw (title := "One rule step") (source := some-bib-key)
-- the erasure of a witness system
silmaril consequence_system my.derivable := My.Deriv (op := erase)
-- constructions: Lean generates the definition
silmaril consequence_system my.both (op := union) (args := [my.raw, my.hyp])    -- my.raw ⊔ my.hyp
silmaril consequence_system my.checked (op := inter) (args := [my.derivable, my.entails])
silmaril consequence_system my.gap (op := diff) (args := [my.entails, my.derivable])
```

| `op` | fields | definition |
| --- | --- | --- |
| `decl` | `decl := S` | the existing `S : Ax → C → Prop` |
| `erase` | `decl := W` (`W : Ax → C → Type`) | `Silmaril.Consequence.WSystem.erase W`; `witness := W` is kept |
| `union`, `inter` | `args := [A, B, …]`, at least two | `A ⊔ B ⊔ …`, `A ⊓ B ⊓ …` (Mathlib's pointwise lattice) |
| `diff` | `args := [A, B]`, exactly two | `A \ B` |
| `artifact` | `value := X`, `interpretation := I` | `ConsequenceSystems.artifactSystem X I`: `Γ ⊢ φ` iff the CID-pinned bytes of `X` decode to `v` with `I v Γ φ` |

The operands of a construction must have definitionally equal context types and conclusion
types (Lean checks this with `isDefEq`; the printed `contexts` and `conclusions` columns are
for reading only). There is no nullary union or intersection: register the empty or universal
system with `op := decl`. Lean fills `decl`, `contexts`, `conclusions` and `term` (the defining
constant as instance arguments print it, which is how the database relates problems to
systems). `title`, `doc` and `source` (a `references.bib` key) are kept as written.

**Over a logic's room.** `(room := R) (room_at := "a …") (reading := semantic | derivability)`
places a system over the sentences of a registered room (`docs/projects/logic-graph.md`). Lean
checks that the conclusions are `R.Sen` (or that `R.Sen` is `ULift` of them) and the contexts
lists of them. With `reading := semantic` Lean also checks that the system is the room's
consequence, `roomSeq R` or `roomTheorySeq R T`. The explorer lists these systems at
`#/logic-consequence/`.

## Systems of registered artifacts

`op := artifact` mirrors `language … (op := artifact)`. An interpretation is its own record:

```lean
silmaril consequence_interpretation wasm.core.check_rel :=
  Silmaril.Project.ConsequenceSystems.WasmExport.checkRel
  (abi := Silmaril.Project.Languages.WasmExport.checkExport)
  (environment := Silmaril.Project.Languages.WasmExport.allHosts)
silmaril consequence_system my.checker (op := artifact)
  (value := my.checker_value) (interpretation := wasm.core.check_rel)
```

`I : V → System Ax C` reads the value's decoded type `V` (Lean checks it against the value's
type); the ABI and environment, when given, must occur in `I`'s definition — a check of the
metadata, not a proof that `I` models execution. `wasm.core.check_rel m` is
`as ⊢ c` iff some run of the export `check(ptr: i32, len: i32) -> i32` answers `1` on the bytes
`c :: as` written into memory 0 (`Profile.spec`, every Core host), over the export semantics
`Silmaril.Wasm.Game.Accept.Export`.

**Decode failure is not an empty checker.** When the bytes do not decode, `artifactSystem X I`
is `⊥` only because there is nothing to interpret. The value's `.is` problem — a kernel-checked
certificate that the bytes decode to a given Lean module — is what ties the system to the
module the theorems are about: `X.Is v → artifactSystem X I = I v` (`artifactSystem_of_is`).
The system's page shows that certificate as **decode evidence** next to the artifact (CID,
format) and the interpretation (definition, ABI, environment); an artifact's page lists the
systems its bytes denote.

`examples/project/ProjectSelfTest/Consequence/Wasm.lean` registers the checkers of
`ProjectSelfTest.WasmAcceptors`:

| system | problems (all proved) |
| --- | --- |
| `wasm.member_check` (`member_check.wasm`, 108 bytes) | equal to `MemberCheck.accepted Profile.spec allHosts` (sound and complete, by the `.is` certificate); equal to membership `c ∈ as` **for `as.length + 1 < 2 ^ 32`** (the export ABI's bound), both directions for a nonempty host set; `1, 2 ⊢ 2` true, `1 ⊢ 2` false |
| `wasm.empty_check` (`empty_check.wasm`, 45 bytes) | derives nothing, for every host set; its bytes decode (`.is`), so this is a verified checker that accepts nothing |

Statements and assumptions are bytes (`UInt8`); no component wraps either module.

## Partial interpretations (core `Interp`)

`consequence_interpretation N := I` also accepts a core partial interpretation
`I : Silmaril.Consequence.Interp Env V Ax C` (`Silmaril.Logic.Consequence.Interp`; `Interp₀` is
the case `Env = PUnit`). Lean recognises it from the type's `Interp` application (through aliases,
before `Interp` unfolds) and records `definedness := partial` and the configuration type `env`;
the earlier form `V → System Ax C` is `definedness := total`, unchanged.

```lean
silmaril consequence_interpretation my.reading := My.reading          -- : Interp Env V Ax C
silmaril consequence_system my.sys (op := artifact) (value := X) (interpretation := my.reading)
  (env := My.config)                      -- a closed term of type Env; optional when Env is PUnit
silmaril instance my.sys_defined := silmaril.shapes.consequence.artifact_defined
  (X := X) (I := My.reading) (e := My.config)
```

The system is `artifactSystem X (I.orBot e)`: the reading of the decoded value at `e`, or `⊥`
where it is undefined (core's compatibility projection). Whether it is defined is a separate
certificate, `artifact_defined X I e` (`∃ v, X.parse = some v ∧ I.Defined e v`); the page never
infers it:

* **defined (certified)**: `artifact_defined` is proved;
* **defined, empty (certified)**: also `derives` over all `Γ, φ` refuted (UNS);
* **undefined**: `artifact_defined` refuted *and* the bytes decode (a proved `.is` or `.parses`);
  without that, **undefined or undecodable**;
* **not certified**: no `artifact_defined` problem for that interpretation and configuration.

The self-test `ProjectSelfTest.Consequence.Partial` exercises these on the registered bytes
`hello.txt` with test readings (`prefix_exact` over `ℕ`, `nonempty_whole` as `Interp₀`); they
are registry tests, not Wasm semantics.

**Wasm modules through `coreInterp`.** The protocol track's `coreInterp`
(`Silmaril.Wasi.Consequence`, configurations `CoreConfig`: profile, hosts, export name, codec) is
registered as `wasm.core.seq` (partial, `Env = CoreConfig`), and
`ProjectSelfTest.Consequence.WasmSeq` reads `member_check.wasm` and `empty_check.wasm` at
`memberConfig Profile.spec allHosts`: both **defined** (`artifact_defined`, from the values' `.is`
certificates); `member_check` sound for single-succedent membership (every host set) and complete
for it within `Γ.length + 1 ≤ 2 ^ 32 - 1` (nonempty hosts), by the protocol theorems
`member_sound` and `member_completeOn` applied through `coreBytesInterp_member`;
`empty_check` **defined and empty** (`coreBytesInterp_empty`). The two registrations of
`member_check.wasm` agree on single conclusions: `c ↦ [c]` translates its `wasm.core.check_rel`
reading into its `wasm.core.seq` reading and reflects it back, by the project-side bridge
`ConsequenceSystems.WasmSeq.coreSeq_single_iff_checkRel` (`coreSeq Profile.spec allHosts m "check"
memberEnc Γ [c] ↔ checkRel m Γ c`, for every module).

## Typed shapes, views and the Gentzen view

Lean records each system's shape from its types (the `Expr`, never printed text): for contexts
and conclusions separately, `unit`, `list`, `finset`, `set` or `other` (a scalar carrier), the
element type, and whether that element type is `Signed A`; `raw_sequent` when both sides are
lists of one formula type. The Systems page filters by these: **artifacts**, **acceptors**
(unit contexts), **rejectors** (unit conclusions), **list/finset/set contexts**, **multiple
conclusions**, **signed formulas** (either side; each side is shown), **raw sequents**, and
**Gentzen-closed**: the raw sequents with a *proved*
`silmaril.shapes.consequence.gentzen_closed rs S` for a named rule profile `rs`
(`Gentzen.defaultRules`, …), shown with the profile. A raw sequent relation is not called
Gentzen-closed without that proof; a refuted closure stays visible as counterevidence. There is
no separate Gentzen registry: the view is a filter on the same systems.

Acceptors and rejectors of a module are core adapters applied to the module's export
languages: `wasm.core.check_acceptor m := liftTTC () (checkAccept m)` and
`wasm.core.check_rejector m := liftAxFF (checkReject m) ()`. The self-test proves the acceptor
of `member_check.wasm` equal to its registered language `lang.member_check.accepted` read
through `liftTTC ()`.

**Bounded completeness.** `silmaril.shapes.consequence.complete_within_at S T μ b Γ φ :=
μ Γ φ ≤ b → T Γ φ → S Γ φ`: `S` is complete for `T` on the pairs with `μ Γ φ ≤ b`, the measure
`μ : Ax → C → ℕ` and the bound shown exactly. `member_check.wasm` is complete for `c ∈ as`
within `as.length + 1 ≤ 2 ^ 32 - 1`.

**Evidence and relations.** A system's page groups every soundness, completeness (bounded or
not), translation and Gentzen-closure problem about it: **established** (the universal or closed
statement is proved), **counterevidence** (a counterexample or refutation, kept with its
witness), **partial** (only an instance), **unknown**. The Systems page lists the same relations
for all systems, with constructions and artifacts by definition.

**Shape evidence.** Closed shapes state the core predicates of
`Silmaril.Logic.Consequence.Shape` about a system: `context_free`, `conclusion_free`,
`supported_ax S tt`, `supported_c S ff` (support at a designated context or conclusion is a
different property from context- or conclusion-freeness), and, per conclusion, the context
policies `ctx_perm_inv`, `ctx_set_inv`, `ctx_up_closed` (left `⊆`-weakening) and
`ctx_append_extensive` (not `AppendClosed`). A proved one shows on the Systems page as a pill
naming exactly that property; a refuted one is counterevidence. The self-test proves the raw
system permutation-invariant but not weakening-closed (`p ⊢ q`, not `p, p ⊢ q`), derivations
weakening-closed and set-invariant, the pair test the same and the bounded test not, the
acceptor of `member_check.wasm` context-free and its rejector conclusion-free, and
`member_check.wasm`'s relation not context-free.

**Finite sets, sets and translations.** `ProjectSelfTest.Consequence.Structural` registers the
structural track's systems with their theorems: the identity calculus on atoms and its signed
lift (explosion `p, ¬p ⊢` and excluded middle `⊢ p, ¬p`; translated and reflected along
`Signed.pos`, `posPart_signedLift`); validity of literal sequents on finite sets (`onFinset`)
and on sets (`onSet`), which agree along the inclusion of finite sets (`onFinset_iff_onSet`);
and over `m ⊨ n ↔ m ≠ n`, finite validity read on sets is sound for infinitary validity but
not complete — `ℕ ⊨ ∅` has no finite witness (`not_onSet_valid`; no compactness).

**Restrictions.** `gentzen.valid_via_unsat_restriction` is validity rebuilt from its UNSAT
restriction (`viaUnsat (toUnsat (Valid lsat)) lneg`, `Gentzen.Calculus`): sound and complete for
validity (`Calculus.Examples.lit_eq_viaUnsat`). The TAUTO restriction is the same:
`gentzen.valid_via_taut_restriction` (`viaTauto (toTaut (Valid lsat)) lneg`) is sound and complete
for validity by `eq_viaTauto_toTaut` under its hypotheses (closed under the default rules, `NegL`
and `NegR` from `lneg_sound`/`lneg_complete`). Without negation rules the restriction loses
sequents: the identity calculus (closed under the default rules) is not sound for its UNSAT
rebuild — `p ⊢ p` holds and `p, ¬p ⊢` does not (counterevidence kept).

**Closure certificates across translations.** The signed lift of the identity calculus is closed
under the default rules (`closed_signedLift`), and so is its pullback along `succ`
(`closed_pullback`, `Rules.Hom.default`), which `succ` translates into and reflects from the
identity calculus by the definition of pullback. These and the earlier certificates make up the
Gentzen-closed view, each with its rule profile.

**Evidence matrices.** `silmaril consequence_matrix N := rows` records an evidence matrix, one
row per cell, verbatim: `rows : Silmaril.Project.MatrixRows` (variant, reading, supporting
declarations, evidence, strength, note). Lean checks that the reading and each listed
declaration exist and records their modules — provenance, not a check that the classification
is right. `silmaril.protocols.signed_matrix` registers the protocol track's
`SignedMatrix.cells` (12 cells: 8 `definitions`, 2 `specStrategy`, 2 `execution`); the
Interpretations page shows it as the protocol-provided classification with the supporting
declarations (specification strategies are not compiled components).

**Interpretations.** The Interpretations page lists every `language_interpretation` (`V → Set T`)
and `consequence_interpretation` (`V → System Ax C`): what it reads and gives, its ABI and
environment, its definedness (both kinds are total definitions today; applying one to an
artifact can still fail when the bytes do not decode, which the decode evidence shows), and the
languages and systems built from it. Partial and environment-parametrised interpretations will
follow the core's interpretation API.

## The standard problems

Each shape keeps the context `Γ` and the conclusion `φ` last; an instance fixes the systems
(and maps, and `ff`) and asks about what is left free. The readings are proved in
`Silmaril.Project.Shapes.Consequence.Thms` for exactly the binders that remain, in order;
nothing is assumed inhabited (over an empty type of contexts, `derives S` is THM and UNS at
once).

| shape | statement | THM | SAT | UNS | CSA |
| --- | --- | --- | --- | --- | --- |
| `derives S Γ φ` | `S Γ φ` | `S.Universal` (`S = ⊤`) | `S` derives something | `S` empty (`S = ⊥`) | `S` not universal |
| `context_universal S Γ` | `∀ φ, S Γ φ` | every context derives everything | some context is context-universal | none is | some context is not |
| `derives_bottom S ff Γ` | `S Γ ff` | every context derives `ff` | some context derives `ff` | no context derives `ff` | some context does not |
| `sound_at S T Γ φ` | `S Γ φ → T Γ φ` | `S.Sound T` (`S ≤ T`) | | | a counterexample |
| `complete_at S T Γ φ` | `T Γ φ → S Γ φ` | `S.Complete T` (`T ≤ S`) | | | a counterexample |
| `translates_at S T f g Γ φ` | `S Γ φ → T (f Γ) (g φ)` | `S ≤ T.pullback f g`: the translation preserves consequence | | | a consequence not preserved |
| `complete_within_at S T μ b Γ φ` | `μ Γ φ ≤ b → T Γ φ → S Γ φ` | complete on `μ ≤ b` | | | a counterexample within the bound |
| `gentzen_closed rs S` (closed) | `Gentzen.Closed rs S` | closed under `rs` | | false: not closed | |
| `tarski_closed S` (closed) | `Structural.Closed tarskiRules S` | identity, weakening along list inclusion and cut | | false: one of them fails | |
| `reflects_at S T f g Γ φ` | `T (f Γ) (g φ) → S Γ φ` | `T.pullback f g ≤ S`: the translation reflects consequence | | | a translated consequence not reflected |

(all named `silmaril.shapes.consequence.<shape>`; THM of `translates_at S T f g` is exactly
what the core's `Translation S T` with maps `ax := f`, `c := g` needs as its `sound` field; with `Γ` fixed, `context_universal` is
`S.ProvesAll Γ`, and `derives_bottom` is `S.ProvesFalse ff Γ`, its refutation
`S.ConsistentWrt ff Γ`.)

* Fixing `Γ` in `derives` asks about one context: THM says `Γ` derives every conclusion,
  CSA that some conclusion is not derived. Fixing `Γ` and `φ` is the **member judgment**
  `Γ ⊢ φ`: THM true; a refutation is stored as UNS (false), so a closed negative example
  expects `UNS`.
* **Three properties, not one "inconsistency".** *Universal*, *context-universal* and
  *derives `ff`* coincide only under structural rules a system may not have; the shapes, the
  explorer and these docs always name which one is meant
  (`derivesBottom_not_contextUniversal`, `contextUniversal_not_universal`).
* **Soundness is directional**: `sound_at S T` asks whether the derivation system `S` is
  sound for its target `T`; completeness is `complete_at S T`. A CSA proof written
  `⟨Γ, φ, h⟩` records `Γ` and `φ` as the witness, so a counterexample is kept with the answer.
* **Expected outcomes**: `(expect := CSA)` (or `UNS` when closed) marks an expected negative
  result, which the explorer's shared status badge shows as a match (✓), not a failure.
* **Unknown is not false.** A problem with no answer is unknown; only a Lean proof changes it.

## The self-test example

`examples/project/ProjectSelfTest/Consequence.lean` has four sentences `p q r ff`, finite
lists as contexts, and the rules `p ⇒ q`, `q ⇒ r`:

| system | construction | what the problems show |
| --- | --- | --- |
| `raw` | `decl`: one rule step from a one-element context | `p ⊢ p` fails (no reflexivity); sound for `derivable` |
| `hyp`, `raw_or_hyp` | `decl`; `union` | one step does not chain: not complete for `derivable` (`p ⊢ r`) |
| `derivable` | `erase` of the derivation type `Deriv` | `p ⊢ r` holds, `r ⊢ p` fails; sound for `entails`, **not complete** (`ff ⊢ p`); `ff` is not context-universal, some contexts derive `ff` and some do not; a translation preserves but does not reflect it |
| `entails` | `decl`: truth in every model of the rules where `ff` is false | `ff` is context-universal |
| `gap`, `checked` | `diff`, `inter` | something is entailed but not derivable; `checked` is complete for `derivable` (by soundness) |
| `empty` | `decl` | derives nothing (UNS) |

`examples/project/ProjectSelfTest/Consequence/Gentzen.lean` registers the literal sequents of
`Silmaril.Consequence.Gentzen.Examples` (`Γ ⊢ Δ` over lists of literals), answered by that
module's theorems: validity and the complementary-pair UNSAT test are sound and complete for
each other; `p ⊢ q, p` is valid and `p ⊢ q` is not; a test bounded to three literals and its
closure under the default Gentzen rules are sound for validity, while the bounded test is
**not complete for its own closure** (the cut of `p, r ⊢ p` and `p, q ⊢ p` is the kept
counterexample); `p ⊢ r` holds in the cut closure of `p ⊢ q, q ⊢ r` and not in the raw
sequents. Closures are registered as `op := decl` of the library's `Derives rules S`.

## Database and explorer

`sil project sqlite` writes `consequence_systems` (name, op, decl, term, contexts,
conclusions, witness, provenance), `consequence_operands`, `consequence_shape_roles` and the
view `consequence_problems` (each instance of a consequence shape with the systems its
arguments name, role `S` or `T`, expected status, summary and verdict). Systems are matched by
`term`, the defining constant exactly as Lean prints an instance argument, not by `decl`: a
generated system `silmaril.x` prints as `«silmaril».x` (`silmaril` is a keyword), and the
self-test's generated systems are such names. A database written by an older `sil project` has
none of these tables; the explorer then shows a notice instead of the Systems page. The explorer's
**Systems** page lists the systems — construction (operands only on the system's page), types,
closed judgments counted true / false / unknown, questions over free arguments, and expected
statuses met — and what each status of each shape means. A system's page shows its definition
(with a source link when the page has sources), its construction, a line of **expectations**
(met, not yet established, unexpected: whether the project's stated expectations hold, which is
not whether the statements are true — an expected refutation that is refuted is met), then two
tables: **judgments**, closed propositions that are true or false, and **questions over the
free arguments** with their SZS status; each row has the outcome (the shared status badge), the
reading and the Lean answers with their witnesses. Lean terms are shown compactly (qualified
names cut to their last two components) with the full term as the title. Browsing never runs
anything.

The browser test runs on a built site (`make project-check` writes the database;
`sil project explore` the page):

```sh
node tools/silmaril-project/tests/explore/systems.mjs SITE_DIR [SHOTS_DIR]
```

## Roadmap

| Track | Owns | Status |
| --- | --- | --- |
| Core | `Silmaril/Logic/Consequence/{Defs,Thms,Translation,Ax,Semantic}` ([consequence.md](consequence.md)) | on main |
| Structural derivations | `Silmaril/Logic/Consequence/Structural/…`, `Gentzen`, closures under structural rules | on main; Gentzen examples registered here |
| Checkers and SZS protocols | [consequence-protocols.md](consequence-protocols.md) | on main |
| Registry and explorer | this page: `consequence_system`, `silmaril.shapes.consequence.*`, tables, the Systems page, fixtures | this page |

Fixtures register what the other tracks prove, with their theorems as answers: Gentzen
literal sequents, the multiple-conclusion `litMulti` judgements, and the registered Wasm
checkers (`op := artifact`). A Wasm-backed system appears here only when its bytes are a
registered artifact with a registered interpretation.

## Not yet here

Closure operators and structural rules (reflexivity, monotonicity, cut; the core's
`Silmaril.Consequence.Structural`) as shapes or `op := closure`, and translations between
systems as records, are planned; today a translation is the pair of maps given to
`translates_at`/`reflects_at`.

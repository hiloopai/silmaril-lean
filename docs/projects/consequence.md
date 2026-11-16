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

* `Sys`, the bundled systems, form a Mathlib `Category` whose morphisms are all **sound**
  translations. Conservativity is a separate predicate on a translation (`Conservative`,
  closed under identity and composition); the category does not require it.
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

## Multiple conclusions and signed formulas

`MultiSystem C D := System (List C) (List D)`: `Γ ⊢ Δ`, with **conjunction on the left and
disjunction on the right**. A raw multi-system has no structural rule. Weakening defaults to
membership inclusion: `WeakL`, `WeakR`, `Weak`. Order- and multiplicity-sensitive weakening
stays opt-in through `MonoWrt` with `List.Sublist` or `List.Subperm`.

| name | meaning |
|---|---|
| `M.single` | the restriction to singleton succedents, `Γ ⊢ [d]` |
| `rightExt R` | `∃ d ∈ Δ, R Γ d`, the least right-weak extension of a single-conclusion `R` (`rightExt_le_iff`); it never proves `[]` |
| `multiEntails satC satD` | every model of all of `Γ` satisfies some member of `Δ` |
| `roomMulti R`, `corridorMulti f` | the room version, and its translation along corridors (functorial) |
| `posPartAlong e M`, `posPart M` | the part of `M` on formulas embedded by an explicit `e`; for `Signed`, `e := pos` |

* `rightExt` is not the semantic completion. In `rightExt_ne_multiEntails`, `⊢ [true, false]`
  holds semantically, but neither `⊢ true` nor `⊢ false` does.
* Empty sides:
  * `Γ ⊢ []` says that `Γ` has no model, i.e. the conjunction is inconsistent
    (`multiEntails_nil_right`).
  * `⊢ Δ` says that the disjunction is valid (`multiEntails_nil_left`).

`Signed A` (`pos a`, `neg a`) has Mathlib's `InvolutiveNeg`, and `negateEach l` negates every
member of a list.

* An arbitrary involutive negation may have fixed points, so it does not single out the
  positive formulas. That is why positive parts always go through an explicit embedding.
* `Signed` really does decompose: `Signed.eq_of_isPos_atom` and `Signed.neg_ne_self`.
* For heterogeneous `C` and `D`, `SignedCarrier C D A` holds the explicit maps into one carrier,
  and nothing more is assumed.
* The structural modules own the conversions `Γ ⊢ Δ` ↔ unsatisfiability of
  `Γ ++ negateEach Δ` (and the tautology form).

## Acceptors

A language `L : Set _` (the convention of `Silmaril.Accept`) lifts to a system in four ways.
Each lift is the least system with its property (`…_le_iff`):

| lift | judgements | language recovered as |
|---|---|---|
| `liftAxFF L ff` | `a ⊢ ff` for accepted `a` | `{a | a ⊢ ff}` |
| `liftTTC tt L` | `tt ⊢ c` for accepted `c` | `{c | tt ⊢ c}` |
| `liftAxAll L` | `a ⊢ c` for accepted `a`, every `c` | `{a | ProvesAll a}`, only if `C` is nonempty |
| `liftCAll L` | `a ⊢ c` for every `a`, accepted `c` | `{c | a ⊢ c}` for any `a` |

### Acceptor values, interpreters and encoded programs

The lifts above take one language. A CSLib acceptor type `X` (`Cslib.Automata.Acceptor X α`,
whose values accept words `List α`) is itself a system with acceptors as contexts, and so are
the interpreters that read programs as acceptors (`Acceptor/`):

| view | system | `· ⊢ w` holds iff |
|---|---|---|
| `System.ofAcceptor X` | `System X (List α)` | `x` accepts `w` |
| `System.ofInterpreter interp` | `System W (List α)` | `interp m` accepts `w` |
| `System.ofDecoder decode interp` | `System B (List α)` | `decode b = some m` and `interp m` accepts `w` |

The row `{w | x ⊢ w}` of a context is its language (`ofAcceptor_row`, `ofInterpreter_row`), so
`≤` between interpreter systems is language inclusion program by program
(`ofInterpreter_le_iff`). `ofInterpreter interp` is `(ofAcceptor X).pullback interp id`; along
an encoder that the decoder inverts, the bytes system restricts to the program system
(`ofDecoder_pullback_of_roundtrip`). Bytes that do not decode prove nothing
(`ofDecoder_of_eq_none`), the same row as a program that accepts nothing; keep an `Interp`
when the difference matters. One acceptor as the only context is `liftCAll` of its language
(`pullback_const_ofAcceptor`).

For Wasm (Lean names relative to `Silmaril.Wasm.Game.Accept` and `Silmaril.Wasi.Accept`):

| view | module | component | either shape |
|---|---|---|---|
| acceptor | `ofAcceptor ModuleAcceptor` | `ofAcceptor ComponentAcceptor` | `ofAcceptor ByteAcceptor` |
| interpreter | `A.withModule` | `ComponentAcceptor.interp C L acc rej mode` | `ByteAcceptor.interp A I` |
| program system | `A.moduleSystem` | `ComponentAcceptor.compSystem C L …` | `ByteAcceptor.programSystem A I` |
| bytes system | `A.bytesSystem` (`Binary.Core.decode?`) | `ComponentAcceptor.binarySystem C L …` (`parseComponent`), `bytesSystem … decode` | `ByteAcceptor.bytesSystem A C L …` |

**Simple entry points, one shape each:**

* `Silmaril.Wasm.Game.Accept.moduleBytesSystem (P := .spec) : System ByteArray (List UInt8)`:
  module binaries under the default interpretation (`env.accept(ptr: i32, len: i32)`, memory 0,
  every Core host; the interpretation of `wasm.core.accept_bytes32`). `b ⊢ w` iff `b` decodes to
  `m` and `w ∈ bytesLang P m` (`moduleBytesSystem_iff`). No template.
* `Silmaril.Wasi.Accept.componentBytesSystem C (mode := .imp)`: component binaries, through the
  component's own import and export names (`Layout.ofComp`) and its world-level `accept`. Only
  the core semantics `C : CoreSem CoreMod` is required. The library's only instance is the
  loosest, `Project.WasmComponents.topSem` (every legal play); there is no execution-based one.
  `componentBytesSystem_iff`, and `componentBytesSystem_eq_binarySystem` relates it to the general
  form.
* Each proves nothing on the other shape's binaries or on invalid bytes
  (`Wasi/Component/Accept/Consequence/Examples.lean`).
* **`list<u8>` components on the reference machine.** `Silmaril.Wasi.Accept.Ref.refBytesSystem prof`
  decodes and validates a component binary on the reference machine (REF, the full canonical
  ABI with linear memory). `b ⊢ w` iff the component, linked to a host `accept` that records
  its arguments, receives `list<u8> w` in some run: the host invokes exports, ticks and
  cancels. `acceptRun` is the executable driver and `acceptRun_sound` its soundness. A real
  `accept(list<u8>)` binary decodes in the kernel and accepts `"hi!"` by a `#guard`ed run
  (`Ref/Examples.lean`). Caveats: `docs/projects/component-caveats.md`.
* **`list<u8>` is a lowering and semantics gap, not a parser gap.**
  * Every component parser reads `list<u8>`: `Binary.parse`, `Codec.decode` and the reference
    semantics' `Conformance.decodeRef`.
  * Every lowering into the component IR (`Binary.parseComponent`, `Perf.LowerF.parseComponentF`,
    `Perf.JcoMain.parseComponentWith`) rejects it (`defValTy_list`), because the IR's `ValTy`
    has no list type and no memory-based canonical ABI.
  * The reference semantics reads lists but has no trace semantics with imports.
  * The jco model (`Silmaril.Wasm.Jco`) handles `list<u8>` only for wrapper components it
    builds from a core module, and meets the IR only on the memory-free fragment.
  * So a typical `accept(list<u8>)` binary proves nothing through `componentBytesSystem`, while
    fixed-arity `accept(tuple<u8, …>)` binaries do decode. The examples check both binaries in
    the kernel (`listAcceptBytes`, `tupleAcceptBytes`).

A template `ModuleAcceptor` `A` is the module interpretation: profile, `accept`/`reject`
imports, memory, address width and environments; `A.withModule m` replaces only the module.
Component interpretations take a core semantics `C : CoreSem M` and a layout `L`. For the
lowered `CoreMod` of `parseComponent` (partial, unverified lowering), the library has only the
loosest semantics `Project.WasmComponents.topSem`, so the component byte systems take `C` as a
parameter. The either-shape decoder
tries the core decoder first, then the component one. Examples:
`Silmaril/Logic/Consequence/Acceptor/Examples.lean` (a toy acceptor) and
`Silmaril/Wasi/Component/Accept/Consequence/Examples.lean` (the empty-module binary, the
specification component).

## Clausal acceptors: UNSAT, TAUTO, CNF, Gentzen and DIMACS

`Silmaril.Consequence.Gentzen.Clausal` (`Gentzen/Clausal/{Defs,Thms,Examples}`) relates four
kinds of acceptor over a formula type `C`. An acceptor is a plain predicate (a policy);
its semantics and its soundness are separate notions.

| kind | type | reading |
|---|---|---|
| UNSAT `U` | `List C → Prop` | conjunction, accepted when refuted |
| TAUTO `T` | `List C → Prop` | disjunction, accepted when valid |
| CNF `A` | `List (List C) → Prop` | conjunction of disjunctions, accepted when refuted |
| Gentzen `S` | `Seq C` | sequent `Γ ⊢ Δ` |

Semantics over `sat : M → C → Prop`: `CnfSat`, `CnfUnsat` (no model *in `M`*; satisfiability is
relative to the model type), and `CnfSound` / `CnfComplete` for an acceptor. Weakening is
membership inclusion `⊆` (`ListPred.UpClosed`); ordered or substructural policies are not
covered by these equivalences. Negation is an explicit `neg : C → C`, never assumed involutive.

**Closure laws.** `UnsatClosed neg` (`⊆`-weakening, explosion, unit cut
`U (neg a :: Γ) → U (a :: Γ') → U (Γ ++ Γ')`); `TautClosed neg` (dually: excluded middle and
cut); `GentzenClosed neg` (`Closed defaultRules`, `NegL`, `NegR`). CNF acceptors have two layers:

* `CnfClosed`, *representation*: clause-set weakening, clause strengthening, splitting
  `A ([a] :: F) → A (K :: F) → A ((a :: K) :: F)`, the empty clause. No negation. It holds
  exactly when `A` is determined by its unit restriction `unitsOf A` through hitting sets
  (`cnfOf U F := ∀ Γ, Hits Γ F → U Γ`).
* `CnfUnsatClosed neg`, *logic*: `CnfClosed` plus complementary units `A [[c], [neg c]]` and unit
  resolution `A ([neg a] :: F) → A ([a] :: G) → A (F ++ G)`. `cnfUnsatClosed_iff`: these are
  exactly what makes `unitsOf A` `UnsatClosed`. "Contains the empty clause" is `CnfClosed` and
  sound but not `CnfUnsatClosed` (`Examples.emptyClause_not_unsatClosed`).

**Equivalences** (order isomorphisms between the closed acceptors; an arbitrary acceptor is not
the restriction of any calculus, e.g. the sound `bounded 3` test is not up-closed):

| equivalence | maps | hypotheses in the subtypes |
|---|---|---|
| `unsatEquiv neg` | `toUnsat` / `viaUnsat · neg` | `GentzenClosed neg` ≃ `UnsatClosed neg` |
| `tautEquiv neg` | `toTaut` / `viaTauto · neg` | `GentzenClosed neg` ≃ `TautClosed neg` |
| `cnfEquiv C` | `cnfOf` / `unitsOf` | `ListPred.UpClosed` ≃ `CnfClosed` |
| `cnfUnsatEquiv neg` | `cnfOf` / `unitsOf` | `UnsatClosed neg` ≃ `CnfUnsatClosed neg` |
| `gentzenCnfEquiv neg` | `cnfOf ∘ toUnsat` / `viaUnsat (unitsOf ·) neg` | `GentzenClosed neg` ≃ `CnfUnsatClosed neg` |
| `signedEquiv A` | `signedUnsat` / `atomSeq` | `Closed defaultRules` on `Seq A` ≃ `UnsatClosed (-·)` on `List (Signed A)` |
| `signedCnfEquiv A` | `cnfOf ∘ signedUnsat` | `Closed defaultRules` on `Seq A` ≃ `CnfUnsatClosed (-·)` on `List (List (Signed A))` |

`UnsatClosed.dne` derives the double-negation step `NegR` needs from explosion and cut. Over
signed formulas the Gentzen side is a calculus on the atoms `A` — the existing positive
embedding `Signed.pos` (`MultiSystem.posPart`, `signedLift`) — and no positive part is derived
from an involution: `signedUnsat S Γ = S (posAtoms Γ) (negAtoms Γ)`,
`atomSeq U = posPart (viaUnsat U (-·))`; `atomSeq_signedUnsat` needs no hypothesis.

Semantics: `CnfUnsat sat` is `CnfClosed` always, and `CnfUnsatClosed neg` given `NegSound`
(complementary units) and `NegComplete` (unit resolution); `cnfOf_toUnsat_valid`
(`cnfOf (toUnsat (Valid sat)) = CnfUnsat sat`); `cnfOf_signedUnsat_valid` for signed atoms
under a valuation. Soundness transfers separately: `cnfSound_cnfOf`, `checkSound_unitsOf`,
`viaUnsat_unitsOf_le_valid`.

### DIMACS and LRAT

`Gentzen/Clausal/Dimacs/{Defs,Thms,Examples}` connects this to `Silmaril.Logic.SAT` (`Lit :=
Int`, `CNF := List (List Int)`, `Dimacs.read`, `LRAT.check`):

* `CnfUnsat litSat F ↔ SAT.CNF.Unsat F` (`cnfUnsat_litSat_iff`), so `SAT.CNF.Unsat` is
  `CnfClosed`; on `0`-free clauses it is `Refutation.Unsat csat` of `Refutation.CNF`
  (`cnfUnsat_toCNF_iff`). `lratAccepts` (some proof passes `LRAT.check`) is a *sound* CNF acceptor
  (`lratAccepts_sound`); no closure or completeness of LRAT acceptance is claimed.
* `Dimacs.write F` (each clause followed by `0`) is read back exactly by the existing reader
  when no clause contains `0` (`Dimacs.read_write`, `Dimacs.cnf_write`); `[[0]]` is not
  (`Dimacs.write_zero_not_inverse`).
* The image of signed clauses along `v : A → Nat`: `encLit v (pos a) = v a`,
  `encLit v (neg a) = -(v a)`, `encode v F`. `Coherent v F`: `v` is nonzero (the terminator `0`
  is never a literal) and injective (no collision) on the finite support `atoms F`.
  `encLit_neg`: the sign flip commutes with the image for every `v`.
* Direction of the transfer, for `sat : M → Signed A → Prop` with `NegSound sat (-·)` (a model
  of `neg a` is not one of `pos a`; true of `signedSat τ`): source satisfiable in `M` ⇒ image
  satisfiable (`sat_encode`), hence image `Unsat` ⇒ source `CnfUnsat` in `M`
  (`cnfUnsat_of_encode`), and an accepted LRAT proof of the image — or of the formula read from
  its DIMACS stream — refutes the source through `LRAT.check_sound` (`cnfUnsat_of_lrat`,
  `cnfUnsat_of_lrat_stream`, `signedSat_cnfUnsat_of_lrat`).
* The converse is not claimed. `Examples.converse_fails`: in a model type with one model making
  every atom true, `[[¬x]]` is unsatisfiable while its coherent image `[[-1]]` is satisfiable.
  `Examples.collision`: with every atom on variable `1`, the satisfiable `[[x], [¬y]]` has an
  LRAT-refuted image, showing why a hypothesis like `injOn` is needed for the general theorem
  (not that it is necessary for every formula). `Examples.src_unsat`: the four clauses over
  `x, y` encode to `LRAT.fourClauses`, whose existing proof is checked by `decide`.

## Institutions, logics and their propositions

`roomSys` (`Set Sen ⊢ Sen`) and `roomMulti` (`Sen* ⊢ Sen*`) already read a room as a system.
`Institution/` adds the list form, syntactic entailment, and point-wise semantics:

| construction | system | semantics |
|---|---|---|
| `roomSeq R` | `Sen* ⊢ Sen` | every model of all of `Γ` satisfies `φ` (= `Room.Entails` on the members) |
| `roomMulti R` | `Sen* ⊢ Sen*` | every model of all of `Γ` satisfies **some** `δ ∈ Δ` (= `Gentzen.Valid R.Sat`) |
| `institutionSeq I σ`, `corridorSeq f` | translations | reindexing along signature morphisms / corridors |
| `ER.listSys E`, `LogicalSystem.listSys L S` | `Sen* ⊢ Sen` | syntactic (Tarskian) entailment; `≤ roomSeq` when `L` is sound |
| `Refutation.Entails (localSat sat)`, `Gentzen.Valid (localSat sat)` | point-wise | one valuation satisfies the premises and the (some) conclusion |
| `… (validIn sat)` | model-wise | validity in a model (every valuation) |

Closure: every `Refutation.Entails sat` is `Structural.Closed tarskiRules` (reflexivity, `⊆`-weakening,
hence exchange and contraction, and multi-cut); every `Gentzen.Valid sat` is
`Gentzen.Closed defaultRules` (reflexivity, `⊆`-weakening of both sides, cut). Maps with a
satisfaction condition (`valid_map_of_sat`, `entails_map_of_sat`) are the reusable
reindexing/substitution lemma. Point-wise single conclusion is below model-wise
(`entails_localSat_le_validIn`). The converse fails, and the two multiple-conclusion systems are
incomparable (`Institution/Examples.lean`). **A model-wise succedent is not a disjunctive (LK)
succedent.**

**The four laws.** Identity, weakening and cut are `Structural.Closed tarskiRules`. Substitution
(structurality) is `Structural.Substitutive act R`: for an action `act : Sub → C → C` of
substitutions on formulas, `R Γ c → R (Γ.map (act s)) (act s c)`. The logic chooses `Sub`, and
with it the substitutions that are allowed (well-formed instantiations in HOL, syntax rewrites in
Metamath). Derivability and semantic consequence are separate systems, related only by proved
soundness (`≤`).

### HOL (`HOL/`)

The HOL institution's sentences are sequents `H ⊢ p`, satisfied valuation by valuation. At the
level of propositions `HOLProp S` (bool-typed terms):

| system | Lean | reading |
|---|---|---|
| `HOLProp* ⊢ HOLProp` | `HOL.seq S` | HOL Light's sequent semantics: `seq_iff_entails`, `seq_iff_valid_toSeq` (`Γ ⊢ p` valid in the institution) |
| `HOLProp* ⊢ HOLProp*` | `HOL.gentzen S` | LK: one valuation, disjunctive succedent; `gentzen_single : gentzen.single = seq` |
| model-wise | `HOL.globalSeq S`, `HOL.globalGentzen S` | consequence between hypothesis-free sentences `⊢ p` (`globalSeq_iff_roomSeq`) |

Closure, all proved for `seq` and `gentzen`: structural (`seq_closed`, `gentzen_closed`,
`seq_exchange`, `seq_contraction`), signature extension (`seq_map`, `gentzen_map`), type
instantiation (`seq_tySubst`, `gentzen_tySubst`) and term instantiation (`seq_freeSubst`,
`gentzen_freeSubst`); `seq_substitutive_ty` and `seq_substitutive_free` restate the last two as
`Structural.Substitutive`. Soundness: `derives_le_seq` (HOL Light kernel, pure logic) and
`logic_listSys_le_roomSeq` (sequent level).

**Derivability on propositions.** `HOL.kernelFrom S Δ` is the HOL Light kernel as
`HOLProp* ⊢ HOLProp`: a derivation from the axioms `Δ` whose hypotheses are the members of `Γ`;
`HOL.kernel S` has no axioms. It satisfies identity, weakening and cut, which are admissible in
the kernel (`kernelFrom_closed`), and substitution along `INST_TYPE` and `INST`
(`kernelFrom_substitutive_ty`, `kernelFrom_substitutive_free`). `kernel_le_seq` is soundness. `HOL/Examples.lean` proves, over the initial
signature, `x ⊢ y` in `globalSeq` but not in `seq`, and `⊢ x, ¬x` in `gentzen` but not in
`globalGentzen`.

### Theories (`Theory/`)

`theoryOf D T Γ φ := D (T ∪ Γ) φ` reads a relation on sets of premises relative to a theory `T`.
`ER.theorySys E T` is derivability from `T`, and `roomTheorySeq R T` is semantic consequence
over the models of `T`. Both are the list reading of the entailment relation `ER.withTheory E T`,
so both satisfy identity, weakening and cut (`theorySys_closed`, `roomTheorySeq_closed`). A
derivability relation sound for a room is sound relative to every theory
(`theoryOf_le_of_sound`, `theorySys_le_roomTheorySeq`). With `T = ∅` they are `ER.listSys` and
`roomSeq`.

### Metamath, PA, ZF and ZFC (`Metamath/`)

Over a Metamath grammar `X` (`Metatheory.MMSig`), sentences are well-formed tree assertions,
including their disjoint-variable conditions:

| system | Lean | reading |
|---|---|---|
| derivability | `Metamath.derives X` | `A` is tree-derivable with the `Aᵢ` as axioms (`Grammar.TDerivable`) |
| semantic consequence | `Metamath.entails X` | Carneiro's models (`Metamath.Model.Satisfies`) |
| from a theory | `Metamath.theory X T`, `Metamath.theoryEntails X T` | `Γ ⊢_T A` |
| PA | `Metamath.paTheory` | the 30 axioms of `peano.mm` |
| ZF, ZFC | `Metamath.zfTheory`, `Metamath.zfcTheory` | set.mm's axioms over its set-theory fragment (`ZF0` omits `ax-ac`) |
| set.mm's ZFC | `Metamath.setMMZFCTheory` | over all of set.mm's grammar |

**Disjoint-variable conditions** are part of the assertions. They are not premises and not side
conditions of the consequence relation: a derivation applies an assertion only under a
substitution that is DV-safe for it. **Substitution** is along syntax rewrites (a typecode map, an
injective variable renaming and a template per syntax rule): `derives_rewrite`,
`derives_substitutive`. For theories, a rewrite must map each axiom to a theorem
(`theory_rewrite`, `theory_substitutive`). Soundness: `derives_le_entails`,
`theory_le_theoryEntails`. Also: `zfTheory_le_zfcTheory`, and `setMMZFCTheory_sound_zfSet` (every
theorem of set.mm's ZFC holds in the `ZFSet` model). The arithmetic soundness of ZF and ZFC
(`Peano.ToZF.arithSound_ZFC`) concerns one translation of arithmetic sentences. It does not
translate PA derivations, so it is not a map between these systems.

### Martin-Löf type theories (`TypeTheory/`)

| theory | derivability | semantic consequence | soundness |
|---|---|---|---|
| extensional MLTT | `extensionalDerives` (`ECtx.JEqH`) | `extensionalEntails` (set hierarchies) | `extensionalDerives_le_entails` |
| intensional MLTT, original rules, at a stage | `intensionalDerives stage` | `intensionalEntails stage` (realizability) | `intensionalDerives_le_entails` |
| `λΠ` modulo rewriting | `lambdaPiDerives C` | none: the library pairs it with closed theories, which coincide with derivability by construction | — |

Premises are whole judgments used as hypotheses. The context `Γ` of a judgment `Γ ⊢ J` is part
of the sentence, not a list of premises. Identity, weakening and cut on judgment hypotheses hold
(`…_closed`); weakening and substitution *of `Γ`* are admissible rules of each type theory, stated
over judgments, and are not laws of these consequence relations.

### Concrete syntax: S-expressions (`Concrete/`)

HOL and extensional MLTT have a concrete syntax over the S-expressions of `Silmaril.Logic.Smt.SE`,
whose ASCII reader and writer are proved to round-trip (`read_render`):

| | grammar and codec | round trips |
|---|---|---|
| HOL types and terms | `Silmaril.Logic.HOLLight.SExp`: `(-> A B)`, `(tyapp n A*)`, `(bvar n)`, `(fvar n A)`, `(= A)`, `(@ A)`, `(const n A*)`, `(app t u)`, `(lam A t)` | `decodeTm_eq_some_iff` (the decoder accepts exactly the canonical forms), `parseTm_printTm` (bytes, every term) |
| extensional MLTT terms, contexts, judgments | `Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp`: `(pi A B)`, `(lam A b)`, `(bv n)`, `(fv x)`, …, `(ctx (x A)*)`, `(jdg Γ A a b)` | `decodeJdg_eq_some_iff`, `parseJdg_printJdg` (bytes, exactly the judgments whose names are legal atoms: `legal_encodeJdg_iff`, `legalNames_of_parseJdg`) |

Numerals are canonical decimals (`Silmaril.Logic.Concrete.SExp`). A malformed input decodes to
`none`: an unknown keyword, a wrong number of arguments, a non-canonical numeral, a de Bruijn index
out of scope (examples in each `SExp/Examples.lean`). **The relation to the abstract syntax** is
*denotation*, `e` denotes `t` when `encode t = e`. It is a bijection between the canonical
S-expressions and the abstract syntax.

`Silmaril.Logic.Consequence.Concrete` defines institutions and consequence systems over the
concrete syntax:

| | concrete sentences | consequence systems | institution, and its comorphism into the abstract one |
|---|---|---|---|
| HOL at a signature `S` | `HOLSen S` (propositions), `HOLSequent S` (`(sequent (h*) c)`) | `holKernel S Δ`, `holSeq S` | `holRoom S`, `holInst S`, `holToAbstract S` |
| extensional MLTT | `MLTTSen` (judgments) | `mlttDerives`, `mlttEntails` | `mlttRoom`, `mlttInst`, `mlttToAbstract` |

Consequence over concrete syntax holds iff it holds over the abstract syntax it denotes
(`holKernel_ofProp_iff`, `mlttDerives_ofJdg_iff`, and translations both ways). Identity,
weakening, cut and soundness carry over (`holKernel_closed`, `holKernel_le_holSeq`,
`mlttDerives_closed`, `mlttDerives_le_entails`). The comorphisms keep the models, so they are
model-expansive, and semantic consequence over concrete sentences is semantic consequence over what
they denote (`holRoom_seq_iff`, `mlttRoom_seq_iff`). A concrete HOL sequent lists its hypotheses,
which the institution's sentences hold as a finite set, so many concrete sequents denote one
sentence.

### Dependent type theory: the lambda cube (`Silmaril/Calculi/LambdaCube/Consequence/`)

The dependent corners of the lambda cube
(`lambdaP` … `cc`) are the existing dependent institutions, and their sentences are judgements
`Γ ⊢ t : A`, `Γ ⊢ t ≡ u : A` that carry their own dependent context. `Semantics.seq M`
(`roomSeq`) relates lists of whole judgements. It is Tarski-closed in that outer list
(`seq_closed`) and never splits `Γ`. `derivableSys c` is theoremhood: it weakens and cuts, is
below every semantics (`derivableSys_le_seq`), and is monotone in the corner. Reflexivity is not
claimed. There is deliberately no Gentzen instance. `admissible c` (examples) is the one-model
semantics whose `seq` is admissibility.

### Also proved

* `roomSeqSys : Room ⥤ Sys` and `institutionSeqSys I` (functorial `Sen* ⊢ Sen`), instantiated for
  propositional and first-order logic in the examples; `corridorSeq_reflect` (conservative
  along corridors whose model reduct is surjective on objects).
* HOL: `gentzen_iff_seq_disjList` (`Γ ⊢ Δ` iff `Γ ⊢ ⋁Δ`, HOL's defined disjunction) and
  `derives_le_globalSeq` (kernel derivations from axioms `Δ` are model-wise consequences of
  `Δ`; not point-wise ones, since the kernel instantiates axioms).

### Gaps

* HOL: no completeness (standard semantics is incomplete for the kernel).
* No completeness is claimed for Metamath (Carneiro's models) or for the type theories.
* Lambda cube: no hypothetical-judgement calculus (judgements as premises of derivations), no
  concrete model of a dependent corner, and no substitution closure for judgements. These would
  be new developments, not adapters.
* Wasm: no concrete binary with a proved nonempty byte language yet. Component binaries with
  `accept(list<u8>)` parse but do not lower into the IR, and no component semantics with
  imports and list types exists to read them.

## Interpretations

`Interp Env Value Ax C := (e : Env) → Value → Option (System (Ax e) (C e))` reads a value, under a
typed configuration, as a system (`Interp/`).

* `Env` is static configuration: an export or function index, an ABI, a profile, a set of
  hosts. `Interp₀` is the case without configuration (`Env = PUnit`). How a runtime host
  behaves is modelled separately and enters only through `Env` or `Value`. `Ax` and `C` are
  families over `Env`, in independent universes.
* `none` means the value cannot be read, for example because it does not parse. `some ⊥` is a
  system, verified to prove nothing.
  * `sysOrBot` (and `Interp.orBot`) is the explicit projection that sends `none` to `⊥`. It
    loses the difference (`sysOrBot_not_injective`).
  * The registry's `artifactSystem X I` is `sysOrBot (X.parse.map I)` (`sysOrBot_map_iff`).
  * No lattice is claimed on `Option (System …)`; only raw systems form one.
* Operations: `ofDecode`, `map`, `pullback`, `reindex`, `comap`.
  * `pullback` commutes with the projection.
  * A general `map f` commutes only if `f ⊥ = ⊥`, and there is a counterexample without it.
* Evidence against a specification `ref`: `SoundFor`, `CompleteFor`, and `CompleteOnFor P`,
  which is completeness on a slice such as a size bound.
  * These quantify over defined readings only.
  * Soundness can be read off the projection.
  * Completeness can be read off the projection only given definedness, stated as a premise
    (`Defined`).
  * Evidence of this kind never shows that a reading is defined. That a value can be read at
    all (in the registry, that the artifact decodes and its interpretation is defined) needs its
    own certificate.

## Shapes

Descriptors for shape filters (`Shape/`):

| shape | meaning | recovers the system as |
|---|---|---|
| acceptor, `System Unit C` | a language of conclusions (`acceptorEquiv`, an order isomorphism) | `liftTTC ()`, `liftCAll` |
| rejector, `System Ax Unit` | by convention, the contexts deriving the unique bottom (`rejectorEquiv`) | `liftAxFF · ()`, `liftAxAll` |
| `SupportedAx S tt` | only `tt` proves anything | `S = liftTTC tt (ttSlice S tt)` |
| `SupportedC S ff` | only `ff` is ever proved | `S = liftAxFF (ffSlice S ff) ff` |
| `ContextFree S` | proofs do not depend on the context | some `liftCAll L` |
| `ConclusionFree S` | each context proves all or nothing | some `liftAxAll L`; `L` is unique only if `C` is nonempty |

Outside these shapes a slice does not determine the system (`slice_counterexample`).

Checker predicates on list contexts (`ListPred`):

* `SetInv` (depends only on the members) implies `PermInv`. The converse fails: the predicate
  `length = 1` is a counterexample.
* `UpClosed` (closed under membership weakening) is `SetInv ∧ AppendExtensive`.
  `AppendClosed` (closed under concatenation) is a different property: the predicate `l = []`
  has it but is not extensive.
* `SetInv` is exactly factoring through `List.toFinset`.
* `finExt` is an explicit, non-canonical extension of a checker predicate to sets. It is false
  on infinite sets.

Raw `System` stays rule-free. Bundled, proof-carrying closed systems and rule bundles belong to
the structural modules (`Structural/`, `Gentzen/`), and `MultiSystem` is the raw type of
Gentzen sequents.

## Modules and ownership

| module | contents | owner |
|---|---|---|
| `Silmaril/Logic/Consequence/Defs.lean`, `Thms.lean` | systems, order, consistency notions | core |
| `Silmaril/Logic/Consequence/Translation/{Defs,Thms}.lean` | translations, `Sys`, `WSys`, erasure functor | core |
| `Silmaril/Logic/Consequence/Ax/{Defs,Thms}.lean` | context shapes and their maps | core |
| `Silmaril/Logic/Consequence/Semantic/{Defs,Thms}.lean` | satisfaction, SZS, rooms, institutions | core |
| `Silmaril/Logic/Consequence/Accept/{Defs,Thms}.lean` | acceptor lifts | core |
| `Silmaril/Logic/Consequence/Acceptor/{Defs,Thms,Examples}.lean` | CSLib acceptors, interpreters and decoders as systems | core |
| `Silmaril/Logic/Consequence/Institution/{Defs,Thms,Examples}.lean` | list-premise room systems, logics, point-wise vs model-wise | core |
| `Silmaril/Logic/Consequence/HOL/{Defs,Thms,Examples}.lean` | HOL propositions: `seq`, `gentzen`, the kernel (`kernelFrom`), closure, substitution | core |
| `Silmaril/Logic/Consequence/Theory/{Defs,Thms}.lean` | consequence relative to a theory, syntactic and semantic | core |
| `Silmaril/Logic/Consequence/Metamath/{Defs,Thms}.lean` | Metamath derivability and models; PA, ZF, ZFC | core |
| `Silmaril/Logic/Consequence/TypeTheory/{Defs,Thms}.lean` | extensional and intensional MLTT, `λΠ` | core |
| `Silmaril/Logic/Consequence/Concrete/{Defs,Thms}.lean` | institutions and consequence systems over S-expression syntax | core |
| `Silmaril/Logic/Consequence/Signed/{Defs,Thms}.lean` | signed formulas, `negateEach`, carriers | core |
| `Silmaril/Logic/Consequence/Multi/{Defs,Thms}.lean` | multiple conclusions, `rightExt`, `multiEntails`, rooms | core |
| `Silmaril/Logic/Consequence/Interp/{Defs,Thms}.lean` | interpretations, projection, evidence | core |
| `Silmaril/Logic/Consequence/Shape/{Defs,Thms}.lean` | acceptor/rejector shapes, slices, checker predicates | core |
| `Silmaril/Logic/Consequence/Gentzen/Clausal/{Defs,Thms,Examples}.lean`, `…/Clausal/Dimacs/…` | UNSAT, TAUTO, CNF and Gentzen acceptors, closure laws, equivalences; DIMACS image and LRAT bridge | structural derivations |
| `Silmaril/Logic/Consequence/Examples.lean` | worked examples | core |
| `Silmaril/Logic/Consequence/Structural/…` | structural rules and derivation closures | structural derivations |
| Wasm acceptor and SZS protocol modules | Wasm evidence for the lifts | Wasm/SZS protocols |
| explorer pages, [consequence-systems.md](consequence-systems.md) | presentation and master roadmap | explorer/examples |

## Next steps for the core

* Reindexing as a functor between fibres, using the order category of `System Ax C`. Mathlib
  gives `Ax → C → Prop` its pointwise `Pi` category first, so this needs an explicit
  order-category wrapper and was left out instead of being stated for the wrong category.

* A signature-indexed version of `Satisfaction` (a functor `Sign ⥤` satisfactions) whose
  restriction to rooms is `institutionSys`.
* Whether conservative translations reflect `ProvesAll` and `ConsistentWrt`, and which
  structural properties pullbacks preserve, once the structural track has fixed its closures.

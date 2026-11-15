# Acceptance: generic languages, checkers and verdicts

`Silmaril.Semantics.Accept` (namespace `Silmaril.Accept`, region `Semantics`, Mathlib only)
is the generic vocabulary for saying that a checker, a program or a runner *accepts* a set of
values. It contains nothing specific to WebAssembly, WIT or bytes; those developments
instantiate it.

A language over `α` is Mathlib's `Set α`: there is no wrapper type, so all of Mathlib's set
lattice, images and preimages apply directly.

## Stable API

These names are intended for downstream integration; changes go through review.

### `Silmaril.Semantics.Accept.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `ofBool check` | `{a \| check a = true}` |
| `Sound check L` | `∀ a, check a = true → a ∈ L` |
| `Complete check L` | `∀ a, a ∈ L → check a = true` |
| `Decides check L` | `∀ a, check a = true ↔ a ∈ L`; `decides_iff` (sound ∧ complete), `decides_iff_ofBool_eq` |
| `checker L` | `decide (· ∈ L)`; `decides_checker` |
| `acceptsSome run acc` | some outcome of `run a` is in `acc` (existential acceptance) |
| `acceptsAll run acc` | every outcome of `run a` is in `acc` (vacuous with no outcome) |
| `rejectsSome run rej` | some outcome of `run a` is in `rej` |
| `neverRejects run rej` | no outcome of `run a` is in `rej` (universal safety) |
| `detRun f` | the runner `fun a => {f a}` of a total function |
| `upTo size n L` | members of `L` with `size a ≤ n` |

Key laws: `compl_rejectsSome` (never-rejection is the complement of *some* rejection, not of
acceptance), `compl_acceptsSome`, `acceptsAll_subset_neverRejects` (needs disjoint verdicts),
`acceptsAll_subset_acceptsSome` (needs every input to have an outcome),
`neverRejects_not_subset_acceptsSome` (an input with no outcome separates them), the
deterministic collapse `acceptsSome_detRun`/`acceptsAll_detRun`/`neverRejects_detRun`,
`Decides.and`/`or`/`not`/`comp`/`upTo`, and `iUnion_upTo`/`eq_iff_upTo_eq` for size slices.

### `Silmaril.Semantics.Accept.Order.Defs` / `Thms`

Programs of any carrier `X`, compared by `lang : X → Set α`.

| Name | Meaning |
| --- | --- |
| `LangPre lang` | type synonym of `X`, **preorder** `x ≤ y ↔ lang x ⊆ lang y`; `LangPre.of`, `.val`, `.toLang` |
| `LangPre.map f hf` / `LangPre.embed f hinj hf` | monotone map / order embedding along a language-preserving (injective) `f` |
| `LangPre.subtypeEmb p` | sub-carrier `Subtype p` as an order embedding |
| `langSum l₁ l₂`, `inlEmb`, `inrEmb` | two shapes `X ⊕ Y` in one preorder; inclusions are order embeddings |
| `langSigma lang`, `sigmaEmb lang i` | a family of shapes `Σ i, X i` |
| `RespectsLang s lang` | class: `s x y → lang x = lang y` |
| `LangQuot s lang` | `Quotient s` with the descended language; a **preorder** (`mk_le_mk_iff`) |
| `LangQuot.toLangEq` | monotone, order-reflecting, surjective comparison with `LangEq`; injective iff `s` identifies all equal-language programs (`toLangEq_injective_iff`) |
| `LangEq lang` | `Quotient (Setoid.ker lang)`, a **partial order** (`mk_eq_mk_iff : mk x = mk y ↔ lang x = lang y`) |
| `LangEq.toSetEmb`, `LangEq.rangeIso`, `LangEq.antisymmIso` | `LangEq lang ↪o Set α`, `≃o Set.range lang`, `≃o Antisymmetrization (LangPre lang) (· ≤ ·)` |

For Mathlib languages (`Language α`, including `Silmaril.Formats.Accept.ByteLang`), wrap the
map with `toSets`. `Language α` is a non-reducible `def` of `Set (List α)`, so instance search
finds no order on `LangPre lang` for `lang : X → Language α`. For example,
`LangEq (toSets fun m => Silmaril.Wasm.Game.Accept.bytesLang P m)` is the partial order of
modules by byte language. See `LangPre.toSets_le_iff` and `LangEq.toSets_mk_eq_mk_iff`.

Shapes are disjoint as programs, but not up to language: `inl_antisymmRel_inr_iff` and
`LangEq.mk_inl_eq_mk_inr_iff` show that a left and a right program are identified exactly when
their languages agree. A supplied equivalence must be proved to respect the language
(`RespectsLang`) before its quotient carries an order.

Examples: `Silmaril/Semantics/Accept/Order/Examples.lean`.

### `Silmaril.Semantics.Accept.Bounded.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `within μ b` | `{a \| μ a ≤ b}` for a measure `μ : α → β` into any preorder (length, format depth, pairs of them via `within_prod`) |
| `SoundOn D c L` | `∀ a ∈ D, c a = true → a ∈ L` |
| `CompleteOn D c L` | `∀ a ∈ D, a ∈ L → c a = true` |
| `DecidesOn D c L` | `∀ a ∈ D, (c a = true ↔ a ∈ L)`; outside `D` the checker may answer anything |

Laws: `decidesOn_iff`, `decidesOn_univ` (and the sound/complete versions) recover the
unrelativised notions; `SoundOn.anti`/`CompleteOn.anti`/`DecidesOn.anti` (smaller domain),
`DecidesOn.within_mono` (smaller bound), `SoundOn.mono`/`CompleteOn.mono` (language),
`…union`/`…iUnion`; exhaustion `complete_of_forall_within`/`decides_of_forall_within`;
`decides_inter_iff : Decides c (L ∩ D) ↔ DecidesOn D c L ∧ Sound c D` and
`DecidesOn.andBound` for checkers that enforce their bound; `upTo_eq_inter_within`.

Bounded completeness is a modelling choice, not a law of the library. A one-shot interface
with a fixed input buffer can only be complete on inputs that fit. A streaming checker can be
complete on inputs of unbounded total size. A semantic specification needs no bound, and an
executable total checker may or may not need one. Use `Decides` when the checker is complete
everywhere and `DecidesOn (within μ b)` when it is complete only up to a bound.

Examples: `Silmaril/Semantics/Accept/Bounded/Examples.lean` (a toy document format with
depth, a total checker and a depth-enforcing one).

### `Silmaril.Semantics.Accept.Items.Defs` / `Thms`

Sequences of items (for example JSON Lines). The layer is generic over the item type and the
measures; concrete validity belongs to the format developments. **Finite item lists**
(`List ι`: finitely many items, but arbitrarily many) are kept apart from **infinite item
sequences** (CSLib's `ωSequence ι`, names ending in `ω`).

| Name | Meaning |
| --- | --- |
| `everyItem L` | finite lists with every item in `L` |
| `itemsWithin μ n` | per-item bound: every item has `μ x ≤ n` |
| `totalWeight w s`, `totalWithin w n` | whole-list bound: `(s.map w).sum ≤ n` |
| `countWithin n` | at most `n` items |
| `everyItemω L`, `itemsWithinω μ n` | infinite counterparts (only per-item bounds) |

Laws: `itemsWithin_not_subset_totalWithin` says a per-item bound bounds no whole-list weight.
`totalWithin_subset_itemsWithin` gives the per-item bound from a whole-list one when
`μ ≤ w`, and `itemsWithin_inter_countWithin_subset` gives a whole-list bound from a per-item
bound plus an item count. Checkers lift with `List.all` (`Decides.everyItem`), and
`DecidesOn.everyItem`/`DecidesOn.itemsWithin` carry correctness on per-item bounded domains to
lists of any total size. Also: `mem_everyItemω_iff_take` (every finite prefix) and
`kstar_eq_image_flatten` (Mathlib's Kleene star).

Examples: `Silmaril/Semantics/Accept/Items/Examples.lean`.

### Choosing a quantifier

* A *validator* or *parser* that must accept the value: `acceptsSome` (some run succeeds) or,
  for a deterministic checker, `Decides`.
* A *safety* property (“this input never makes the program reject/trap”): `neverRejects`.
  It holds vacuously for inputs with no outcome, so it does not imply acceptance.
* A *robust* acceptance (“every run accepts”): `acceptsAll`.

Examples and regression tests: `Silmaril/Semantics/Accept/Examples.lean`.

### `Silmaril.Semantics.Accept.Rel.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `α -|> β` | scoped notation (`open scoped Silmaril.Accept`) for Mathlib's `SetRel α β = Set (α × β)` |
| `outcomes R` | `fun a => {b \| (a, b) ∈ R}`, the runner of a relation |
| `pullSome R L` | `R.preimage L`: some output in `L` |
| `pullAll R L` | `R.core L`: every output in `L` (vacuous with none) |
| `ofPartial f` | relation of `f : α → Option β` (`f a = some b`) |
| `ofTotal f` | `Function.graph f` |
| `partialComp f g` | Kleisli composition `fun a => (f a).bind g` |
| `pdom f` | `{a \| (f a).isSome}` |
| `IndexedLang A` | `∀ i, Set (A i)` |
| `eraseSigma L` / `fiberLang M` | to and from `Set (Σ i, A i)`; `indexedLangIso` is an order isomorphism |
| `eraseSome L` / `eraseAll L` | `⋃ i, L i` / `⋂ i, L i` over a common carrier |

Rejection quantifiers: `neverRejects (outcomes R) rej = pullAll R rejᶜ`;
`compl_pullSome : (pullSome R L)ᶜ = pullAll R Lᶜ`; for a partial function, `none` is in every
`pullAll` and no `pullSome` (`mem_pullAll_ofPartial_of_none`,
`not_mem_pullSome_ofPartial_of_none`), and `pullSome_ofPartial_eq`/`pullAll_ofPartial_eq`
relate them through `pdom`. `not_mem_eraseSome` (rejected at every index) and
`not_mem_eraseAll` (rejected at some index). Composition: `pullSome_comp`, `pullAll_comp`,
`ofPartial_partialComp`, `ofTotal_comp`, `ofPartial_some_comp`. Checkers:
`Decides.optionAny`, `Decides.optionAll`, `Decides.sigma`, `Decides.fiber`.

Examples: `Silmaril/Semantics/Accept/Rel/Examples.lean`.

### `Silmaril.Semantics.Accept.Success.Defs` / `Thms`

Successful-value projections of relations whose outputs carry a status (`Option`, `Except`,
or a sum with `inl` = `ok`, the convention of the WIT `result<T, E> ↦ T ⊕ E` interpretation
in `Silmaril/Wasm/Component/Reference/WIT/Interp/Defs.lean`).

| Name | Meaning |
| --- | --- |
| `succ f R` | `R ○ ofPartial f` for an extractor `f : γ → Option β`: outputs `c` with `f c = some b`, as `b` |
| `optionOk` | `id : Option β → Option β` |
| `exceptOk` / `exceptErr` | `.ok b ↦ some b` / `.error e ↦ some e` (`exceptOk_eq_toOption`) |
| `sumOk` / `sumErr` | `inl b ↦ some b` / `inr e ↦ some e` (`sumOk_eq_getLeft?`) |
| `someVals R` | `succ optionOk R`; `mem_someVals : (a, b) ∈ someVals R ↔ (a, some b) ∈ R` |
| `okVals R` / `errVals R` | `succ exceptOk R` / `succ exceptErr R`; `mem_okVals`, `mem_errVals` |
| `inlVals R` / `inrVals R` | `succ sumOk R` / `succ sumErr R`; `mem_inlVals`, `mem_inrVals` |

Laws: failures are dropped (`not_mem_dom_succ`: an input whose outputs all fail is outside
`(succ f R).dom`; `not_mem_dom_someVals`/`okVals`/`inlVals`; `mem_dom_succ`); functoriality
`succ_comp : succ g (succ f R) = succ (partialComp f g) R`, `succ_some`, `succ_mono`,
`succ_union`, `succ_empty`; `succ_ofPartial : succ f (ofPartial g) = ofPartial (partialComp g f)`,
`succ_ofTotal : succ f (ofTotal g) = ofPartial (f ∘ g)`; pullbacks
`pullSome_succ : pullSome (succ f R) L = pullSome R {c | ∃ b ∈ L, f c = some b}` and
`pullAll_succ`; `succ_single` (single-valued `R` gives single-valued `succ f R`, stated
directly).

Limitations: `succ` only *drops* failures. Whether an input fails on every run, on some run,
or has no run at all is not distinguished by `succ f R`; keep `R` (or use `errVals`) to see
failures. In particular `pullAll (succ f R) L` holds vacuously for inputs that always fail.

Examples: `Silmaril/Semantics/Accept/Success/Examples.lean`.

### `Silmaril.Semantics.Accept.Session.Defs` / `Thms`

Relational acceptance of export-driven client sessions. A host calls exported entrypoints
`process(a)`/`input(a)` (returning nothing), `output() : Q` and `reset()`; answers are
arbitrary values of `Q`. The Bool-answer specialisation, with `process`/`query`/`reset`
acceptors and `Language` correctness, is the incremental-acceptor development of draft
PR #255 (`Silmaril.Semantics.Acceptors`); this topic does not depend on it.

| Name | Meaning |
| --- | --- |
| `Call A Q` | a returned top-level call: `feed a`, `query q` (answered `q`), `reset` |
| `T : Set (List (Call A Q))` | session model: call sequences a fresh instance returns from |
| `feeds w` | the fed values of `w`, in order |
| `segments T` | reset-free `w` with `pre ++ w ∈ T`, `pre = []` or ending in `reset` |
| `freshSegments T` | reset-free traces of `T` (`pre = []` only) |
| `feedQuery T : A -|> Q` | (5) `[feed a, query q] ∈ segments T` |
| `feedsQuery T : List A -|> Q` | (6) `as.map feed ++ [query q] ∈ segments T` (no intermediate queries) |
| `feedsQueryAny T` | (6) with intermediate queries: `w ++ [query q] ∈ segments T`, `feeds w = as` |
| `freshFeedQuery`, `freshFeedsQuery`, `freshFeedsQueryAny` | the same on `T` itself (from a fresh instance only) |
| `PrefixClosed T` | `u ++ v ∈ T → u ∈ T` |
| `QueryDrop T` | `u ++ query q :: v ∈ T → u ++ v ∈ T` |
| `QueryInsert T` | `u ++ [query q] ∈ T → u ++ v ∈ T → u ++ query q :: v ∈ T` |
| `QueryPure T` | `QueryDrop T ∧ QueryInsert T` |
| `ResetSound T` | `pre ++ [reset] ∈ T → (pre ++ reset :: w ∈ T ↔ w ∈ T)` |
| `ByteChunk` | `List UInt8`, one `process(bytes)` argument |
| `flatRel R` | `{(xs, q) \| ∃ cs, cs.flatten = xs ∧ (cs, q) ∈ R}` (`flatRel_eq_image`) |
| `FlatInvariant R` | `cs.flatten = cs'.flatten → ((cs, q) ∈ R ↔ (cs', q) ∈ R)` |
| `chunksQuery T` / `flatQuery T` | (7) `feedsQuery T` on chunks / `flatRel (chunksQuery T)` |
| `ChunkInvariant T` | `FlatInvariant (chunksQuery T)` |
| `Machine S A Q`, `Machine.traces`, `Machine.respond` | deterministic model (init, step, answer), its traces, and the answer after feeds |
| `Machine.chunked init step answer` | feeds each chunk element by element |

Laws:

* (5) is (6) at singletons: `mem_feedQuery_iff_feedsQuery`.
* Resets: `freshFeedsQuery_subset_feedsQuery` always; `segments_eq_freshSegments` and
  `feedQuery_eq_fresh`/`feedsQuery_eq_fresh`/`feedsQueryAny_eq_fresh` under `ResetSound` and
  `PrefixClosed`; `segments_eq_freshSegments_of_resetFree` for models without resets.
* Interleaving: `feedsQuery_subset_feedsQueryAny` always; `feedsQueryAny_eq` under
  `QueryDrop` (only the drop direction is needed), `feedsQueryAny_eq_of_queryPure`;
  `queryDrop_segments`.
* Status filters (with `Success`): `mem_someVals_feedsQuery : (as, b) ∈ someVals (feedsQuery T)
  ↔ as.map feed ++ [query (some b)] ∈ segments T`, `mem_okVals_feedsQuery` (`.ok b`),
  `mem_inlVals_feedsQuery` (`inl b`), and the `feedQuery` versions.
* Chunks: `mem_flatRel_of_mem`/`mem_flatQuery_of_mem_chunksQuery` always;
  `FlatInvariant.mem_iff`/`ChunkInvariant.mem_chunksQuery_iff` (`(cs, q)` iff
  `(cs.flatten, q)`), `flatInvariant_iff`, one chunk and element-at-a-time
  (`FlatInvariant.flatRel_eq_single`/`_singletons`, `ChunkInvariant.flatQuery_eq_single`/
  `_singletons`), empty chunks (`FlatInvariant.cons_nil`, `append_nil`); with resets,
  `chunkInvariant_iff_fresh`.
* Machines: `Machine.prefixClosed_traces`, `queryPure_traces`, `resetSound_traces`;
  `Machine.feedsQuery_traces : feedsQuery m.traces = ofTotal m.respond` (also
  `feedsQueryAny_traces`, `feedQuery_traces`); `Machine.chunkInvariant_chunked`.

Counterexamples (`Examples`): `feedsQueryAny_ne_feedsQuery` (an `output()` that counts its own
calls), `not_resetSound_badReset`/`feedsQuery_ne_fresh_badReset` (a reset that does not
restore the fresh behaviour), `not_chunkInvariant_chunkCount` (answers count chunks; an empty
chunk is still a call).

Limitations:

* Traps and non-returning calls are modelled by *absence*: `T` records only returned calls and
  nothing follows a trap. Every relation here is a successful-return relation; there is no
  trap/partial-call observation inside a session, and a session that traps before `output()`
  contributes nothing.
* No concurrency or reentrancy: calls are sequential top-level calls.
* Every session starts from a fresh instance; host-visible state outside the component (and
  any other exports) is not modelled.
* `segments` ignores what happened before the last reset; it agrees with the fresh relations
  only under `ResetSound` (and `PrefixClosed`).

Examples: `Silmaril/Semantics/Accept/Session/Examples.lean`.

Finite automata (Mathlib, CSLib) as presentations of languages: see [automata](accept-automata.md).

Context-free grammars (Mathlib's `ContextFreeGrammar`) as presentations of acceptor sets, with checker bridges and a proved `(ⁿ )ⁿ` example: see [grammar presentations](accept-grammar.md).

Byte languages, simple WIT types and the inputs accepted by Wasm modules and components
instantiate this vocabulary: see [accepted inputs](projects/accepted-inputs.md).

### `Silmaril.Semantics.Accept.Func.Defs` / `Thms`

The functional shape of a relation `R : α -|> β`, for example the (input, output) pairs
observed from program traces.

| Name | Meaning | Mathlib / CSLib bridge |
| --- | --- | --- |
| `Total R` | every input has an output (left-total) | `Relator.LeftTotal`, `R.dom = univ`, CSLib `Relation.Serial` (homogeneous) |
| `SingleValued R` | at most one output per input (right-unique) | `Relator.RightUnique`, `∃ f : α →. β, f.graph' = R` |
| `Surjective R` | every output is produced (right-total) | `Relator.RightTotal`, `R.cod = univ` |
| `Injective R` | an output determines its input (left-unique) | `Relator.LeftUnique`, `SingleValued R.inv` |
| `Functional R` | `Total R ∧ SingleValued R` | `∀ a, ∃! b, a ~[R] b`, `∃! f, Function.graph f = R` |
| `OneToOne R` | `Functional R ∧ Injective R ∧ Surjective R` | `OneToOne (ofTotal f) ↔ Function.Bijective f` |
| `toPartial R` | classical choice of an output, `none` if there is none | `ofPartial (toPartial R) = R` if single-valued; `toPartial (ofPartial f) = f` |
| `toFun h` | classical choice of an output, for `h : Total R` | `Function.graph (toFun h) = R` if single-valued; `toFun_ofTotal` |

`SingleValued R ∧ Injective R ↔ Relator.BiUnique`. `ofPartial f` is single-valued, total iff
`pdom f = univ`, and injective iff `Set.InjOn f (pdom f)`; `ofTotal f` is functional,
surjective iff `Function.Surjective f`, injective iff `Function.Injective f`. Composition
(`○`) preserves all four notions; `R.inv` swaps `Total` with `Surjective` and `SingleValued`
with `Injective`; subsets preserve `SingleValued` and `Injective`, supersets `Total` and
`Surjective`. Pullbacks: `SingleValued.pullSome_subset_pullAll`,
`Total.pullAll_subset_pullSome`, `Functional.pullSome_eq_pullAll`.

Examples (total but not single-valued, single-valued but not total, injective but not
surjective, surjective but not total): `Silmaril/Semantics/Accept/Func/Examples.lean`.

### `Silmaril.Semantics.Accept.IO.Defs` / `Thms`: relational I/O acceptance

Namespace `Silmaril.Accept.IO`. A program that reads inputs and writes outputs accepts a
*relation*. "Input `a` triggers output `b`" is defined by **scopes** (call IDs or protocol
boundaries), not by temporal order: only events of the same scope are related, so outputs of
interleaved invocations, of nested/reentrant calls, and outputs before the input are not
attributed to it.

| Name | Meaning |
| --- | --- |
| `Ev K X I O C` | role-decoded event of scope `k : K`: `enter k x` (entry point invoked, `x : Option X`, `none` = unobserved), `inp k i`, `out k o`, `exit k c` (`c : Option C`, `none` = trap/abort/undecoded) |
| `localView k t` | the events of scope `k`, in order (`Loc X I O C`) |
| `Run I O C` | `input`, `outputs` (in order), `result : Option C` |
| `windows l` | one run per input occurrence: outputs after it up to the next input or the exit; result the exit's value when the scope exits first |
| `entryRun l` | the run of an observed entry: argument as input, all outputs of the scope, return value |
| `inputRuns t` / `entryRuns t` | runs over all scopes of a trace (computable) |
| `inputRunsOf T` / `entryRunsOf T` | runs of a trace model `T : Set (List (Ev …))` |
| `ScopeViews T` | the local views of `T`; runs depend only on it (`inputRunsOf_congr`) |
| `triggers S` | (1) `(a, b)`: some run with input `a` outputs `b` (every occurrence, returned or not) |
| `episodes S` | (2) `(a, (bs, c))`: a run with input `a` output exactly `bs` then returned `c` |
| `retTriggers S` | (3) `(a, b, c)`: `b ∈ bs` for an episode `(a, (bs, c))` |
| `returns S` | (4) `(a, c)`: classic input/return relation (outputs forgotten) |
| `Tag`, `bracket`, `decode dec` | scope assignment for well-bracketed traces by a stack (IDs = position of `enter`) |

Key laws: `mem_windows`, `mem_inputRuns`, `mem_entryRuns`, `localView_insert_other`,
`inputRuns_congr` (interleavings with equal local views have equal runs), `returns_eq_image`,
`triggers_of_mem_retTriggers`, `image_retTriggers_eq` (needs every run to return; a trapped run
is a counterexample in `Examples`), `mem_episodes_iff_run`, transport `triggers_image_map`,
`episodes_image_map`, `returns_image_map`, monotonicity.

Choosing the reading: an *imported* `input()` (or `input(a)`) whose value drives later
imported `output(b)` calls is the window reading (`inputRunsOf`); an *exported* `f(a)` is the
entry reading (`entryRunsOf`). The decoder decides which raw events have which role, so both
call directions are explicit in the decoded data. Successful-value projections of `Option` or
`result`-like returns compose with a partial function (`SetRel.comp R (ofPartial f)`).

Limits: `bracket` assumes well-bracketed traces (nested calls close before their callers);
asynchronous or overlapping calls need a decoder that supplies call IDs and uses `Ev`
directly. The decoder must tag every scope-opening and -closing event (`enter none` for
unobserved entry points). Within a scope, the window reading attributes an output to the most
recent input; a protocol with another causal structure needs its own decoder. Examples:
`Silmaril/Semantics/Accept/IO/Examples.lean`.

### `Silmaril.Wasi.IOAccept.Defs` / `Thms`: I/O acceptance of component traces

Namespace `Silmaril.Wasi.IOAccept`. The bridge from the named traces of a WASI component
(`Silmaril.Wasi.World`: `WEv`, `wtrace`; `Silmaril.Wasi.Accept.Traces σ = wtrace '' σ.plays`)
to the scoped runs above. A component is `σ : Strategy (nsig Im) (nsig Ex)` (imports `Im`,
exports `Ex`).

| Name | Meaning |
| --- | --- |
| `Roles X I O C` | role decoders: `entry f args` (export call observed as an entry; `none` = unobserved scope), `result f args r` (successful return), `callIn f args` (import call carrying an input), `answerIn f args r` (host answer carrying an input), `callOut f args` (import call issuing an output; wins over `callIn`) |
| `tag ρ : WEv → Option (Tag …)` | `call` is always `enter`, `ret … (some r)` is `exit (result …)`, `ret … none` (trap) is `exit none`; `req` is `out` or `inp`; `imp … (some r)` is `inp` or nothing; host traps `imp … none` are never tagged |
| `ioRuns σ ρ` / `entryIORuns σ ρ` | `inputRunsOf` / `entryRunsOf` of `decode (tag ρ) '' Traces σ` |
| `importIO inp out decI decO` | input = answer of import `inp`, output = argument of a call to import `out`; entries and results `()` |
| `exportFn f decX decC` | the export `f(x) -> c`, no inputs or outputs (`Empty`) |
| `Shallow b ts` | depth-one bracketing automaton on tags (`b` = inside a scope) |
| `blocks ts`, `wblocks t` | each `enter` (export `call`) with what follows up to the next one |

Key laws: `ioRuns_mono`/`entryIORuns_mono` (refinement), `ioRuns_eq_of_traces`/
`entryIORuns_eq_of_traces` (equal `Traces`, any worlds); the structural bridge
`shallow_of_legal` (legal plays have shallow tags), `ret_after_call` (the next export event
after `call f a` is `ret f a r`), `localView_bracket_of_shallow`/`exists_localView_bracket`
(the scopes of a shallow tag list are its blocks), `blocks_filterMap_tag`, and so
`mem_ioRuns`/`mem_entryIORuns`: the runs of a component are the windows (entry runs) of the
decoded call blocks of its plays, i.e. every import event belongs to the scope of the most
recent export call. Soundness: `triggers_ioRuns_sound`, `returns_ioRuns_sound`,
`returns_entryIORuns_sound` (a related pair comes from an ordered pair of events of one play),
`locOf_eq_out`, `locOf_eq_exit`; the unary link `mem_importAccepted_of_triggers` (triggered
outputs are accepted through the output import, `Silmaril.Wasi.Accept.importAccepted`).

Examples (`Silmaril/Wasi/IOAccept/Examples.lean`): `echo` (`run` reads `input()`, calls
`output(a)`, returns) triggers exactly `a ↦ a` with episode `([a], ())`; `echoTrap` (the call
traps) triggers its output but has no episode; `checked` (`f(x) -> result<u32>`) with
`returns` restricted to `ok` values by `inlVals` (`Silmaril.Accept.succ`).

Limits. What is modelled: single-threaded, synchronous components of the game model
(`Silmaril.Games.Play`), whose legal plays answer each export call before the next and make
import calls only inside an export call. The model has no callbacks from imports into exports,
so **no reentrancy occurs**: scopes have depth one and the nesting support of `bracket` is
unused. Import events outside any export call cannot occur in legal plays; `bracket` would drop
them. A host trap (`imp … none`) is not an event of any run; the component's own trap
(`ret … none`) ends the scope with `exit none` (outputs triggered, no episode). Inputs and
outputs are decoded per event (`Val` lists); typing is the decoders' job. Asynchronous
components (component-model `async`, futures, streams, overlapping calls) are out of scope:
they need call IDs supplied by the decoder and `Ev` directly.

### Presentations: regular expressions

Regular-expression syntax with abstract leaves over Mathlib's `Language α`, and byte
specialisation: [accept-regex.md](accept-regex.md).

# Handle-based tree acceptors: design and coverage

This development answers: *what trees does a module accept* when it talks to its environment
through **handles** (`i32` values the environment interprets as trees), rather than through
bytes in memory? It covers writer (constructor) APIs, reader (inspection) APIs, their
combination, parsing sessions, the tree families they produce, abstract acceptors over those
families, and the link to core Wasm modules.

The checklist below maps every item of the original request (1–9) and the additional cautions
to files, theorem names and tests. Status: **done** (in this branch, built with `--wfail`),
**partial** (what exists and what does not), **planned** (nothing yet). Nothing marked planned
is claimed anywhere in the Lean sources.

## Layers

| Layer | Region | Modules |
| --- | --- | --- |
| Host models (generic) | Semantics | `Silmaril.Semantics.Accept.Host.{Defs,Thms}` |
| Handle APIs: writers, readers, combined, node environments | Semantics | `Silmaril.Semantics.Accept.Handle.{Defs,Thms,Examples}` |
| Parsing sessions | Semantics | `Silmaril.Semantics.Accept.Parse.{Defs,Thms,Examples}` |
| Tree families, AST signatures, APIs, patterns | Formats | `Silmaril.Formats.SExp.Family`, `…SExp.Api`, `…SExp.Pattern` |
| Wasm modules, decoders, checkers | Wasm | `Silmaril.Wasm.Game.HandleAccept.{Defs,Thms}`, `…HandleAccept.Checkers.{Defs,Thms}` |

Proofs longer than a few lines are under `Silmaril/Proofs/<Region>/…` and reached only through
the `Thms` headers.

### The common semantics

A module's behaviour is a set of **event traces**; an event is a call with the answer the
module observed (`Host`). A host model says which answers the environment may give and what a
call makes the module accept; `Host.lang h T` is the union over traces. Three kinds of
environment behaviour are kept apart everywhere:

* *nondeterministic answers* (several responses: interning or not, allocation failure,
  arbitrary data for invalid reads);
* *restriction* of the environment (fewer responses; `Sim` gives inclusion of languages; fixed
  environments `fixedLang`, environment sets `Envs`);
* *traps* versus *undefined behaviour* (`chaos`: the event and everything after accepts every
  tree, the top element). A trap is **call-local** by default, as in Wasm: it aborts the current
  export call (phase `aborted`), the instance and its store persist, and the next export call
  (`enter`, decoded from the export-call move of a play) resumes; a session abort (phase `dead`,
  nothing follows) is an optional stricter policy.

Environments are always explicit: writer stores (`WState.store`), fixed environments
(`fix = some ρ`, `fixedLang … Envs`), reader environment sets (`readerLang … Envs`), parse
environments (`parseRel … Envs`).

## Audit against the request

Each requirement of the original request (1–9) and of the follow-ups, with where it is met at
the abstract level (Semantics/Formats) and in Wasm (core modules with proved soundness and a
run showing acceptance), or why not. "Abstract" results quantify over every module trace set;
Wasm examples are concrete modules.

| # | Requirement | Abstract | Wasm | Limits |
| --- | --- | --- | --- | --- |
| 1 | writer `symbol(string)`, `sexp(list<i32>)`, `accept(i32)`; arbitrary fresh handles, interning | `Handle.Writer`, `Fresh`, `Run.store_extends` | memory `hiMod_lang`, `pairMod_lang`; instance-play `twoWords`, `sxPair` | |
| 1 | invalid accept: mandatory trap (call-local), session abort, ignore, UB, fixed-env UB, error return | `callTrap`/`sessionTrap`/`ignore`/`ub`, `fixedLang`, chain + strictness, `writerLang_eraseErr_eq` | `callTrap` is the Wasm-facing policy (export calls decode to `enter`); error-return `accept`: `errAccept_sound` (within words and `nil`), runs `errAccept_accepts_word`, `errAccept_accepts_nil` (error branch) | |
| 1 | sentinel 0/−1, inclusion with exact assumptions, capacity | `writerLang_noRet_subset`, `writerLang_subset_of_oneFailure`, `sentinel_twice`, `writerLang_sentinel_swap`, `successes_length_le` | `twoWordsZ`, `twoWordsM` | raw inclusion is false (counterexample) |
| 1 | constructed set (downward closed), `accept_all` since start, batches | `writerLang_downClosed`, `batch_not_downClosed` | `allAccept_sound` (bound `allL`, `allL_downClosed`), `allAccept_accepts`; `batchAccept_sound`, `batchAccept_accepts`; **exact batch language** `AcceptVariants.Batch`: import-level ghost bridge `strategy_gag` (`GISpec`, `GAG`, `GhostGameSat`; ghost in the host code, as `MemSound.Ghost`), batch bridge `storeLang_subset_of_gag` (ghost = current batch, `batchGSpec`), `consXLang_sound_of_ghostSat`; `batchAccept_lang` (⊆ `keptL` = `nil` and `(w)`, the kept batch), `batchAccept_drops` (no word, the dropped batch, is accepted), `batchAccept_fixed_lang`, `batchAccept_kept` (with the run `run(3)`) | `batchAccept`: upper bound `keptL` with runs at the fixed argument `3` (not every `(w)` is exhibited); the ghost bridge covers store semantics and fixed environments for policies without UB |
| 2 | readers `tag`/`symbol`/`sexp -> list<i32>`; `children`/`child`; fixed env; module-chosen handles, any export sequence | `Reader`, `readerLang`, `Env`/`Env.ofTotal` | cons checkers, n-ary `count`/`child` checkers, memory `items(h, retptr)`, `string_text`, `keyword_text` | |
| 2 | invalid reads: arbitrary, trap, typed error, default, UB; arbitrary ≠ UB | `OnBadRead`, `error_iff_invalid`, `arbitrary_ne_ub`, `arbitrary_uncertified` | checkers use trap; typed error: `errD_disjoint`, `polLang_subset_of_AG` (every policy but UB), `carCheck_sound`; counterexample runs `carNoCheck_unsound_dflt`, `carCheck_unsound_arbitrary`; `carCheck_accepts` | |
| 2 | atoms `blob`, `string`, `word(i64)`, keywords: writers and readers | Family atoms | writers `atomMod` (symbol/string/blob/keyword), `word_lang`; readers string, keyword, symbol (`symTextMod_lang`), blob (`blobMod_lang`: exactly the 2-byte blobs), `word` | |
| 3 | first-class APIs for the ten families incl. Rivest canonical vs hinted | `Family`, one parameterized API per style | **every family × API pair** has a module proved sound with a positive run: `Families.Matrix` (`<family>_<api>_sound`, `<family>_<api>_live`, `api ∈ naryW, consW, naryR, consR, astW, astR`; 60 pairs of theorems for the 10 families × 5 APIs, AST split into writer and reader), instances of generic modules proved once for every atom type: writers over atom tables `MemSound.Tab` (`tab_pair_lang`: `pairAtomMod` writes exactly `(a b)`; `tab_pairAst_lang`: its `sexpSig` tree; `tab_cons_lang`: `consAtomMod` writes exactly `(a)`), readers `MemSound.Probe` (`probeMod`: `next(h, 0)`, then a memory-returning `leaf(c, retptr)`; `nary_sound` ⊆ `firstAtoms`, `cons_sound` ⊆ `carAtoms`, `ast_sound` ⊆ `firstLeaves`, runs `nary_live`, `cons_live`, `ast_live`; payloads `bytesPay` (`list<u8>`), `kindPay` (`{bytes: list<u8>, kind: u32}`), `hintPay` (`{octets: list<u8>, hint: list<u8>}`, null hint pointer = no hint), `u64Pay`); word trees: `word_lang`, `twoWords`, the `u64` probe. **Full signatures**: every table names all atom imports of its family, one decoder per name (`AtomDec.seg`/`.seg2`): symbols `symbol`; bytes, Rivest `blob`; symStr `symbol`+`string`; symBytes `symbol`+`blob`; symStrBytes `symbol`+`string`+`blob`; symStrKw `symbol`+`string`+`keyword`; symStrKwBytes all four; hinted `blob`+`hinted(hptr, hlen, ptr, len)` (`hintedTab_hinted`); readers decode every kind (`kindD`: kind code `c` ↦ `ks[c]`; hinted: `hintPay`). Earlier examples: `Families/Mem`, `bpairMod`/`rivest_bpairMod`, `hinted_lang`, `hintedSep_lang`, `MemSound.ListCheck` | examples are small fixed languages (one two-element list, one cons pair, one-child reader checks); the soundness bounds are for modules that import and call one atom import each, decoded through the full table: a mixed family's writer run uses one kind, the hinted writer runs are hint-free (`hinted` is decoded but not called; a module calling it: `MemSound.Hinted`, n-ary only); reader runs read one kind (hinted: with a hint); the word cons writer's run is at the specification profiles; no looped any-length checker |
| 4 | generic branch + leaf tags with WIT payloads; variadic, fixed, mixed arity; SExp correspondence | `AstSig`, `WitSig`, `sexpW_hom`, `SExp.equivAST`, `leaf_children_not_wellArity`; owned handles: `Own.ownHost` (resource table in the host state, moves consume), `resolveOp_congr`, `run_congr`, `ownLang_congr` (dependence on the table only at moved handles), `no_second_move`, `unresolved_step`, `ownLang_eq_of_linear`, `linear_of_ob` (`obProto`), `borrow_rejected` | `astMod`, `calcMod`, `appMod`, `binMod`, `glyphMod`, `addCheck`; owned handles: `ownMod` (`ownMod_sound`, `ownMod_dead`, `ownMod_live`, `ownMod_lang`: exactly `{res(rep)}` for the table's live `own<0>` handle `1`), `twiceMod` (`twice_traces`, `twice_accepts`: the double move accepts nothing; `twice_via`: the stateless reading would accept); canonical-ABI layout for the whole domain (`layout_toWit`, `valsLayout_toWit`); decoding equal to the pure reference loaders for scalar vectors of all nine scalars (`loadVals_loadRecord`), single scalars, floats and chars (`loadVal_scalar`, `loadVal_f32`, `loadVal_f64`, `loadVal_char`) and UTF-8 strings below `maxStringByteLength` (`readVal_string_loadStringFromRange`) | payload domain: every WIT value type with a memory representation and no async semantics (`bool`, the eight integers, `f32`/`f64` (NaNs canonicalised), `char`, `string`, `list<t>`, `list<t, n>`, `record`, `tuple`, `variant`, `enum`, `option`, `result`, `flags`, nested) and the handles `own<r>`/`borrow<r>`: a **top-level** `own` field moves its handle into the tree under the resource-table semantics (`MemSound.WitAst.Own`: the tree holds the representation from an explicit table, consumed once; an `own` nested in a list/option/record is no value), `borrow` is rejected (no value in a stored tree, `borrow_rejected`); not `future`, `stream`, `error-context` (pending async semantics), `map` (use `list<tuple<k, v>>`); lists, fixed lists and composite types are not compared with any reference loader (none is pure); not compared with the monadic `Canon.load`; no length limits; no flattening |
| 5 | cons API with/without nil; SExp vs SExp2; properness; roundtrips | `consW`, `pairW`, `SExp2.toSExp?`, `Pat.toSExp2_image_lang` | cons checkers, `combCheck` (Tree2), `consMod`, `consMix` | |
| 6 | union/intersection, images/preimages, list combinators, patterns, AST→sexp encodings | `Pattern`, `tuple_inter`, `AST.encode_injective`, `enc_collides` | — | abstract by nature |
| 7 | executable checkers: proper lists (SExp2), word lists n-ary and binary, sorted with subset | — | `properCheck` (spine), `recProperCheck`, `recFullCheck` (recursive, total), `wordsCheck`, `sortedCheck`, `wordsNCheck`, `sortedNCheck`, `combCheck`; replays | signed `i64` order; handles are opaque `i32` |
| 8 | combined writer+reader, consistent future reads, persistent meanings | `combined_write_read`, `Reader.Mono.persist`, `write_persists` | `readBack` writes `(x)` and reads it back (`combLang_subset_of_AG`, `crun_facts_init`): `readBack_sound`, `readBack_accepts_0/_5` | upper bound plus runs at fixed arguments |
| 9 | parse(data), append/done, chunks with `used`, cursor, failure advancing, projections | `Parse`, `parseRel_slice(_eff)`, `parseRel_done`, projection laws and counterexample | `nzParse`, `listParse`, `stackParse`, `chunkStack`, `chunkTake`, `chunkRingN`, pull `echoMod`, exact `drainEcho` | `stackParse`/`chunkStack` return newest-first lists |
| F | call-local trap, pre-trap effects persist | `callTrap`, `write_persists`, `persist_seven` | export calls → `enter` | |
| F | combined writer+parser relation with a real parser | `Mixed`, `mixedRel_subset_of_AG` | `listParse`, `stackParse`, `drainEcho` | |
| F | memory-observing soundness; list children, chunk inputs, items reader | `MemSound`, ghost bridge `tagTraces_gpre` | `pairMod`, `itemsMod`, `echoMod`, `drainEcho` | export-argument chunks in memory are not expressible in the traced-session model (pull-style `read` is) |
| F | recursive vs spine properness | `SpineProperList`, `recProperL_ssubset_properL` | `properCheck` vs `recFullCheck` | |

## Coverage checklist

### 1. Writer acceptor API

| Item | Status | Where |
| --- | --- | --- |
| `symbol(string)->i32`, `sexp(list<i32>)->i32`, `accept(i32)` | done (abstract), see 7 for Wasm | `Handle.Writer`, `WEv.write/accept`; S-expression instance `Formats.SExp.Api` |
| successful handles arbitrary, never reused; interning allowed | done | `Fresh`, `Policy.intern`; persistence `Run.store_extends`, `write_persists` |
| invalid accept: mandatory trap (Wasm-facing, call-local) | done | `OnInvalid.callTrap` (the default), `WStep.acceptCallTrap` (`aborted` phase until the next export call `WEv.enter`, `WStep.resume`; `WStep.aborted_inv`: only `enter` follows, store and batch unchanged). Effects before the trap persist: `write_persists`, `Examples.persist_seven` (write `7` at `1`, invalid accept, `enter`, `accept 1` accepts `7`) |
| invalid accept: session abort (optional, stricter) | done | `OnInvalid.sessionTrap`, `WStep.acceptSessionTrap` (`dead` phase: nothing follows, not even an export call, `WStep.not_dead`); within one export call it agrees with `callTrap` (`writerLang_callTrap_eq_sessionTrap`, traces with no `enter` after their first event) |
| invalid accept: ignored, traps permitted as a foreign call | done | `OnInvalid.ignore` (a trace may end anywhere) |
| invalid accept: UB = all behaviour | done | `OnInvalid.ub`, `WStep.acceptChaos`/`chaos` |
| UB restricted to fixed `i32 → tree` environments agreeing with allocations | done | `fix = some ρ`, `Agrees`, `WStep.writeFixed/acceptFixed`, `fixedLang` |
| error-return accept variant | done | `WEv.acceptErr`, `writerLang_subset_eraseErr`, `writerLang_eraseErr_eq` (`ResultOblivious`) |
| relationships under explicit observations | done | `writerLang_mono` (`Policy.Le`, ranks `sessionTrap ≤ callTrap ≤ ignore ≤ ub`), `writerLang_onAccept_mono`, chain `writerLang_sessionTrap_subset_callTrap`, `writerLang_callTrap_subset_ignore`, `writerLang_ignore_subset_ub`; fixed environments `writerLang_subset_fixedLang`, `fixedLang_subset`; strictness `Examples.callTrap_ne_sessionTrap` (invalid accept in call 1, valid in call 2: `[accept 0, enter, write (lit 7) → 1, accept 1]`), `Examples.callTrap_ne_ignore` and `sessionTrap_ne_ignore` (invalid then valid in the same call), `fixed_lt_ub`, `fixed_trace_lt_ub` |
| failure sentinel `0` or `-1` | done | `Policy.sentinel`, `writerLang_sentinel_swap` (the two correspond by the handle swap `0 ↔ -1`, not by numeric identity) |
| acceptance with sentinel ≤ without, exact assumptions | done | The anticipated raw inclusion `writerLang (sentinel s) T ⊆ writerLang (no sentinel) T` is **false** (`Examples.sentinel_twice`: two failures at handle `0` for different trees cannot be read as allocations, since a sentinel-free environment never returns one handle for two trees). What holds: (1) restriction: traces that never receive the sentinel (`writerLang_noRet`, `writerLang_noRet_subset`); (2) reinterpretation: with trapping invalid writes, a trace with at most one failure whose result is never used again (`OneUnusedFailure`) accepts no more than without a sentinel, reading the failure as a successful allocation of `s` (`accepts_subset_of_oneFailure`, `writerLang_subset_of_oneFailure`, `Examples.ten_one_failure`); (3) `0` vs `-1` correspond by the handle swap (`writerLang_sentinel_swap`) |
| finite `i32` capacity, freshness vs aliases/interning | done | `successes_nodup`, `successes_length_le` (no interning: at most `\|{h ≠ sentinel}\|` successes) |
| consistent environments | done | stores only grow (`Run.store_extends`); fixed `ρ` must agree with every allocation |
| constructed set as accepted, downward closed | done | `WEv.acceptAll`, `writerLang_downClosed` (`Writer.ChildRel`) |
| `accept_all()` since start; `accept_all(bool)` batches since previous call | done | `WEv.acceptAll`, `WEv.acceptBatch`; batches are not downward closed: `Examples.batch_not_downClosed` |

### 2. Reader APIs

| Item | Status | Where |
| --- | --- | --- |
| `accept(i32)`, `tag`, `symbol`, `sexp(i32)->list<i32>`; `children` count, `child(i32,i32)` | done (abstract signature), S-expression queries in `Formats.SExp.Api` | `Reader`, `REv` |
| fixed environment `i32 → tree` or `option tree` | done | `Env` (partial), `Env.ofTotal` |
| handles chosen by the module, arbitrary export sequences | done | traces are arbitrary event lists with export-call boundaries `REv.enter`, not a single `check(h)` |
| invalid accept | done | `OnInvalid` as for writers: `RStep.acceptCallTrap` (`aborted` until `enter`), `acceptSessionTrap` (`dead`), `acceptIgnore`, `acceptChaos`; chain `readerLang_sessionTrap_subset_callTrap`, `readerLang_callTrap_subset_ignore`, `readerLang_ignore_subset_ub`; `readerLang_callTrap_eq_sessionTrap` within one export call |
| invalid reads: arbitrary data, trap, typed error, default, UB | done | `OnBadRead.{arbitrary,trap,dflt,ub}`, typed error = `dflt` + `ErrorDisjoint` (`error_iff_invalid`) |
| arbitrary data ≠ UB | done | `Examples.arbitrary_ne_ub`, `Examples.arbitrary_uncertified` |
| relations | done | `readerLang_mono` (`OnBadRead.Le`, accept ranks), `trap_reads_correct`, `readerLang_trap_subset` (certified acceptance, every accept policy but `ub`; `readerLang_trap_subset_callTrap` for the call-local trap, reads stay correct across export calls) |
| more atoms: `blob(bytes)`, `string`, `word(i64)`, keywords | see 3 | `Formats.SExp.Family` |

### 3. First-class family APIs

| Item | Status | Where |
| --- | --- | --- |
| symbols, byte trees, word trees, symbols+strings, symbols+bytes, symbols+strings+bytes, symbols+strings+keywords, symbols+strings+keywords+bytes | done (tree types and writer/reader signatures) | `Formats.SExp.Family.Defs`: `SymbolSExp`, `ByteSExp`, `WordSExp`, `SymStrSExp`, …, `Atom ks`, `AtomKind`; one parameterized writer `Api.sexpW α` and reader `Api.sexpR α H` instantiated per family (no per-family code duplication) |
| Rivest canonical vs display hints | done | `RivestSExp` (hint-free, existing), `HintedSExp` with `HintedSExp.toSpki` into RFC 9804 `Spki.Sexp`, `HintedSExp.toSpki_injective`; the docstring explains that canonical encodings carry hints |
| Wasm import decoders for string/byte-carrying imports (`symbol(string)`, `blob`, `sexp(list<i32>)`) | done (decoders, structural bound) | `Wasm.Game.HandleAccept.Memory`: `memWrite`/`memAccept` roles over memory-observing traced sessions (`memTraces` on `tagTraces`), `memWriterLang` over `SymStrBytesSExp`; `inp_of_tsession`, `memWriterLang_subset_atoms`; 12 kernel-checked decodings in `Memory.Examples`. An assume/guarantee bridge for memory-carrying traces is **not done** |
| memory-observing soundness | done (upper bounds) | `HandleAccept.MemSound`: `MemContract` (call guarantee `pre` sees the callout and memory at the call; `ans` assumption on decoded answers; `reply` host class), `MemSat` (Hoare-logic obligation), bridge `tagTraces_pre` by induction over `TSession`; `memWriterLang_subset`, `memFixedLang_subset`, `memReaderLang_subset` with a canonical-ABI `items(h, retptr)` reader. Examples: `hiMod_sound` (accepts only the symbol `hi`), `pairMod_sound`/`pairMod_fixed_sound` (only `(a b)` of its symbols), `itemsMod_sound`/`itemsMod_sound_callTrap` (only 2-element lists). Host class: answers keep the store's functions and memory count, may rewrite memory, return the import's result shape. Export-argument chunks in memory are not expressible in `TSession` (the embedder never writes memory between export calls); pull-style `read` imports are. Non-vacuity: `MemSound.Live` builds concrete traced sessions (`countEnv` handle host, `itemsEnv` retptr host): `hiMod_lang` (exactly `{hi}`), `pairMod_lang` (exactly `{(a b)}`, no sentinel), `itemsMod_lang_univ` (exactly the 2-element lists over all fixed environments). String/blob/keyword atoms: generic `atomMod` with `str_lang`, `blob_lang`, `kw_lang` (new `keyword(ptr,len)` decoder); `Families/Mem` lists the memory instantiations per family. Pull-style chunks: `read(buf,cap)` answers decode to `PEv.feed` (memory after the answer), `finish(used,h)`; `echo_short` (relates at most 16 bytes), `echo_live` (relates `[68,69]`); the echo tree handle is a constant. Byte/Rivest trees through memory: `bpairMod_lang` (exactly the list of byte strings `61`, `62`), `rivest_bpairMod`, `bytes_bpairMod`. String reader `string_text(h, retptr)`: `textMod_sound` (only 2-byte strings), `textMod_live`. Writer + pull-chunk host `memMixedRel`: `blobEcho_len` (**length only**: the returned atom has as many bytes as were consumed), `blobEcho_live`; exact content is **false** against the admitted hosts (`blobEcho_not_exact`: if `blob` traps after `read`, the next `finish` consumes the stale chunk). **Ghost bridge** `MemSound.Ghost`: `GContract` (call guarantee `pre g o` in a ghost state `g` moved by `upd` over the decoded inputs), `GMemSat` (Hoare obligation in a specification world whose host codes carry the ghost, `gConfig g c = Config.mapH (·, g) c`; host-free steps commute by `Component.Reference.Step.mapH`, re-exported by `Component.Reference.HostMap.Thms`), bridge `tagTraces_gpre` (a call-decoded input meets `pre` in the ghost of the decoded prefix; admitted hosts are `ReplyEnvs reply`, unchanged), `gConfig_erase`. **One-point case**: `MemContract.toG` (ghost `Unit`), `memSat_iff_gMemSat` (`MemSat … K Inv ↔ GMemSat … K.toG (fun _ => Inv) ()`, by transferring step-indexed safety along the host relabelling `gConfig ()` in both directions) and `tagTraces_pre_of_gpre` (the conclusion of `tagTraces_pre` derived from `tagTraces_gpre`). **Exact content** `MemSound.Exact`: `drainEcho z` drains stale bytes with `finish(16|8|4|2|1, z)` before the `blobEcho` body; `drainEcho_exact` (`memMixedRel … ⊆ exactRel` against `blobReply`, **every** sentinel `z`, no UB; the instantiation shape `deOk_all` and the spec instance `deSpec_all` are kernel evaluations with `z` free, by `kernel_rfl`), `drainEcho_finish_bound` (≤ 16 bytes buffered at every `finish`), `drainEcho_no_stale` (the `blobEcho` stale pair is not related), non-vacuity `drainEcho_live`, `drainEcho_repeat` (two invocations), `drainEcho_after_trap` (the stale-chunk host: the drain consumes the stale bytes); liveness needs `onOverrun` `callTrap` or `ignore` (under `sessionTrap` the first drain overrun ends the session). **Keyword reader** `MemSound.KwText`: `keyword_text(h, retptr)` (`kwTextRoles`, `kwTextReaderLang_subset`), `kwTextMod_sound` (only keywords of two UTF-8 bytes), `kwTextMod_live_of` (every two-byte UTF-8 text `b₀ b₁`: the live session is parameterized by the bytes, against the host `itemsEnv (kwWord b₀ b₁) 0` writing them as the text), `kwTextMod_live` (`:hi`), `kwTextMod_bounds`, and **exact language** `kwTextMod_lang` (`= twoByteKws` over every set of fixed environments naming each two-byte keyword), `kwTextMod_lang_univ` (over all fixed environments). **Word trees** `MemSound.WordAtom`: `word(ptr)` reads the little-endian `i64` at `[ptr, ptr + 8)` (`wordWrite`, also `sexp(ptr, len)` nodes, `wordWriterLang` over `WordSExp`); `wordMod` (`i64.store 42`, `accept(word(0))`): `word_sound`, `word_live`, `word_lang` (exactly `{42}`). **Hinted Rivest atoms** `MemSound.Hinted`: `hinted(hptr, hlen, ptr, len)` (display hint and octets from memory; `blob` gives hint-free atoms; `hintedWriterLang` over `HintedSExp`); `hintedMod` (`accept(hinted(0, 2, 0, 2))`): `hinted_sound`, `hinted_live`, `hinted_lang` (exactly `{[hi]hi}`; hint and octets read from the same segment); separate segments: `hintedSepMod` (`i32.store 0x62616968` at `0`, `accept(hinted(0, 2, 2, 2))`: hint at `[0, 2)`, octets at `[2, 4)`): `hintedSep_sound`, `hintedSep_live`, `hintedSep_lang` (exactly `{[hi]ab}`), with the slice lemma `segment_sub` |

### 4. Generic branch/leaves and tagged ASTs

`Wit.Fragments.Thms` provides named `ScalarType` and `CompoundType` families, with
injective embeddings and partial inverses for `PTy` and WIT types. Scalars include
`char` and floats but not `string`. Compound constructors use existing payload types
for their members, and do not certify well-formedness or resource support.
`MemSound.WitAst.Fragments.Thms` relates their memory32 layouts and transports
existing decoder results without changing success or failure. The scalar `calcSig`
and compound `glyphSig` examples recover the existing signatures, so they use the
same ASTs, Core modules and accepted languages after embedding.

`WIT.Endpoints.Thms` embeds the non-async WIT fragment in the endpoint-capable
interpretation. Extending the environment with stream and future carriers leaves
the old value interpretation unchanged and induces an equivalence on sets of
those values. `Wit.Async` adds typed endpoint identities and dispatches creation,
copy, cancellation, polling and closure to the reference component built-ins.
An old call list yields the identical effect program (`runCalls_legacy`). The
machine examples resolve and close a future, cancel a pending stream read, and
reject inspection of a closed slot. A `stream<u8>` session additionally checks no
event before a matching read, the copied bytes and exact write-completion event,
then disconnects and closes the set and both endpoints. These are component-machine
sessions, not yet Core acceptor tree payloads; the checked tree writer still rejects
async types.

| Item | Status | Where |
| --- | --- | --- |
| generic `branch(children)` + designated leaves `tag(args)` | done | `AstSig`, `AST S := TExpr1 (Σ t, S.Arg t)` (reuses `TExpr`), `AST.WellArity`, `Api.astW` |
| typed heterogeneous WIT payloads | done | `PTy` (`bool`, `s8`…`u64`, `f32`, `f64`, `char`, `string`, `list t` (`bytes = list u8`), `fixedList t n`, `record`, `tuple`, `variant`, `enum`, `option`, `result`, `flags`; nested inductive, `DecidableEq` via `PTy.beq_iff`), `PTy.Val` (the Lean interpretation: floats as IEEE bits, `char` as `Char`, products, sums, `Fin n`, `BitVec n`), `PTy.Vals`, `WitSig.toAstSig`; `Wasm.Game.HandleAccept.Wit`: `toWit : PTy → WIT.ValType`, its left inverse `ofWit` (`ofWit_toWit`, defined exactly off names, `map`, handles and async types), `toWit_simple`, `toWit_injective`, `valEquiv E t : PTy.Val t ≃ (toWit t).Interp E` (with `valsEquiv`, `fieldsEquiv`, `casesEquiv`, `optEquiv`) |
| variadic `tag(args…, children: list<i32>)`, fixed arity `tag(args…, c₁…cₙ)`, mixed arities | done | one writer `astW`; Wasm fixed-arity decoders `Wasm.Game.HandleAccept.Ast` (`moduleAstWLang`, `moduleAstWLang_wellArity` for every module, `astWLang_sound_of_gameSat`); AST reader `moduleAstLang`, `astLang_sound_of_gameSat`; variadic imports carry a memory list (see `Memory`). **Through memory** `MemSound.Ast`: `tag(tagptr, taglen, children, n) -> i32` decodes the UTF-8 tag name at `[tagptr, tagptr + taglen)` and `n` little-endian `i32` child handles at `[children, children + 4n)` of the memory at the call (`Callout.tagNode`, `astWrite`, `astRoles`, `astWriterLang` over `astW strSig`; `strSig`: string tags, no payload, `Arity.star`); bridges `astFixedLang_subset`, `astWriterLang_subset` (instances of `rolesFixedLang_subset`/`rolesWriterLang_subset`); example `astMod` (`tag(16, 1, 0, 0)` for the leaf `a`, the returned handle stored at `[0, 4)`, then `accept(tag(16, 1, 0, 1))`): `astMod_fixed_sound`, `astMod_sound` (Hoare proof `ast_sat` in every fixed environment), `astMod_live` (traced session against the counting host), `astMod_lang` (exactly `{f(a)}`, no sentinel, no UB). **Typed payloads, fixed arities through memory** `MemSound.WitAst`, for every `S : WitSig` with tags numbered by `tagOf`: `node(tag, payload, children, n) -> i32` reads the payload vector of `S.params t` at `payload` **in the canonical ABI layout** (memory32): `PTy.layout`/`PTy.width`/`PTy.align` (`bool` 1/1, `s32`/`u32` 4/4, `s64`/`u64` 8/8, `string`/`bytes`/`list t` the `(ptr, len)` pair 8/4), the vector as the WIT tuple of its types (`valsLayout = ABI.recordLayout`, fields at aligned offsets, tail padding, padding never read; `readFields`, `readVals`), agreeing with the repository's ABI layout `ABI.layout .i32` through `Wit.toWit` (`layout_toWit`, `width_toWit`, `align_toWit`, `valsLayout_toWit`, `valsWidth_toWit`, `valsAlign_toWit`; sizes `ex_width_*`); `payload` must be aligned to `valsAlign` and `children` to four (REF `trap_if(ptr != align_to(ptr, alignment))`); `string`: UTF-8 of `[ptr, ptr + len)`, `bytes`: the octets, `list t`: `len` elements at `ptr + i * t.width` with `ptr` aligned to `t`, recursively (`list<string>`, `list<list<t>>`); payload lemmas `readPtrLen_encode`, `readVal_rest`, `readVal_string`, `readVal_bytes`, `readVal_list`, `readVal_list_misaligned`, `readVals_single`; kernel-checked examples over `exMem` (`ex_string`, `ex_string_utf8`, `ex_bytes`, `ex_bytes_not_utf8`, `ex_list_u32`, `ex_list_string`, `ex_list_list`, `ex_vals`, `ex_vals_padded`, `ex_vals_padded64`); **malformed inputs** decode to no value (`ex_bad_utf8`, `ex_out_of_bounds`, `ex_list_oob`, `ex_list_misaligned`, `ex_list_string_bad_utf8`, `ex_list_string_oob`, `ex_list_list_misaligned`, `ex_short`) and malformed calls to no event (`ex_node_misaligned_payload`, `ex_node_payload_oob`, `ex_node_one_child`, `ex_node_three_children`, `ex_node_leaf_child`, `ex_node_misaligned_children`, `ex_node_children_oob`, `ex_node_unknown_tag`, `ex_node_bad_utf8`, `ex_node_string_oob`, `ex_node_misaligned_pair`, with controls `ex_node_num`, `ex_node_add`, `ex_node_var`); `witWrite_none`: a rejected call has no write event, so under the bridges it makes no handle denote a tree. The supported domain (WitAst docstring): payloads are all of `PTy`, i.e. the WIT value types with a canonical-ABI memory representation and no resource or asynchronous semantics: `bool`, `s8`, `u8`, `s16`, `u16`, `s32`, `u32`, `s64`, `u64`, `f32`, `f64`, `char`, `string`, `list<t>` (`bytes = list<u8>`), `list<t, n>`, `record`, `tuple`, `variant`, `enum`, `option`, `result`, `flags`, nested to any depth; layouts `PTy.layout` (narrow integers 1/1 and 2/2, `f32`/`char` 4/4, `f64` 8/8, records/tuples `ABI.recordLayout`, variants/`option`/`result` `ABI.variantLayout` with the smallest discriminant (`discBytes`) and the payload at `caseOffset`, `enum` its discriminant, `flags` 1/2/4 bytes, `list<t, n>` in place), agreeing with `ABI.layout .i32` mutually over fields, cases and options (`layout_toWit`); decoding with the canonical trap conditions: floats with NaNs canonicalised (`ex_f32_nan`, `ex_f64_nan`), `char` only a Unicode scalar value (`ex_char_surrogate`, `ex_char_too_big`, `ex_record_bad_char`), discriminants in range (`ex_option_bad_disc`, `ex_record_bad_disc`, `ex_variant_bad_disc`, `ex_enum_bad_disc`, `ex_result_bad_disc`), `bool` any nonzero byte (`ex_bool_two`, REF `convert_int_to_bool`), flag bits above the label count ignored (`ex_flags_high`, REF `unpack_flags_from_int`); controls `ex_s8`, `ex_u16`, `ex_s16`, `ex_f32`, `ex_f64`, `ex_char`, `ex_char_astral`, `ex_fixed`, `ex_tuple`, `ex_record`, `ex_option_none`, `ex_option_string`, `ex_variant`, `ex_variant_a`, `ex_enum`, `ex_result_ok`, `ex_result_err`, `ex_flags`, `ex_list_tuple`, `ex_vals_glyph`, sizes `ex_width_glyph`, `ex_width_option_u64`, `ex_width_result`, `ex_width_variant`, `ex_width_enum257`, `ex_width_flags`, `ex_width_fixed`; `readVal_rest` (every value consumes exactly its width) for the whole domain; resource handles (`MemSound.WitAst.Own`, resource-table semantics): an `own<r>` payload field is read as its `u32` table index (`rawSig`, `ownRaw`), resolved in an **explicit resource table** `RT` (index ↦ resource type, representation, live) to the resource's representation (`resolveOp`; dead, missing or foreign-type handles and a double move inside one payload do not resolve) and **consumed**: the resource host `ownHost` keeps the table in its state, a second move of a handle is an invalid write under `onWrite` (`no_second_move`, `unresolved_step`), acceptance depends on the initial table only at the moved handles (`resolveOp_congr`, `run_congr`, `ownLang_congr`), and on traces moving no handle twice (in particular those the ownership protocol `obProto` accepts, `linear_of_ob`, `ownLang_eq_of_ob`) it is the stateless reading `viaRT` (`ownLang_eq_of_linear`); `ownMod` (the module owns handle `1` in the table; `ownMod_sound`, `ownMod_dead`, `ownMod_live`, `ownMod_lang`: exactly `{res(rep)}`) and `twiceMod` (`twice_accepts`: moving `1` twice accepts nothing; `twice_via`); only **top-level** `own` fields are resolved (nested ones are no value); `borrow<r>` is rejected in stored trees (`PTy.Val (.borrow r) = Empty`, `readVal_borrow`, `borrow_rejected`); not payloads: futures, streams, error contexts (pending async semantics) and `map` (despecialised to `list<tuple<k, v>>`). Arity: `Callout.witNode`, `witWrite`, `witRoles`, `witWriterLang` over `astW S.toAstSig`; `witNode_admits`, `witWrite_admits` (every decoded write has `(S.arity t).Admits` children); bridges `witFixedLang_subset`, `witWriterLang_subset`; example `calcSig` (`num`: one `s64`, arity `fixed 0`; `add`: no payload, arity `fixed 2`) and `calcMod` (`i64.store` of `1`, then `2`, at `[16, 24)` right before each `node(0, 16, 0, 0)`, the two handles at `[0, 8)`, `accept(node(1, 0, 0, 2))`): `calcMod_fixed_sound`, `calcMod_sound` (Hoare proof `calc_sat`), `calcMod_live` (traced session against the counting host), `calcMod_lang` (exactly `{add(num 1, num 2)}`, no sentinel, no UB). **String payloads**: `appSig` (`var`: one `string`, arity `fixed 0`; `app`: no payload, arity `fixed 2`) and `appMod` (`i32.store8` of the byte of `"f"` at `24`, then the pair `(24, 1)` as one `i64.store` at `[16, 24)`, right before each `node(0, 16, 0, 0)`, the same with `"x"`, the two handles at `[0, 8)`, `accept(node(1, 0, 0, 2))`): `appMod_fixed_sound`, `appMod_sound` (Hoare proof `app_sat`, decoding `var_node`), `appMod_live` (traced session against the counting host), `appMod_lang` (exactly `{app(var "f", var "x")}`, no sentinel, no UB). **Byte-string and list payloads**: `binSig` (`blob`: one `bytes`; `seq`: one `list<u32>`; both arity `fixed 0`; `pair`: no payload, arity `fixed 2`) and `binMod` (the byte `FF` at `24` and the pair `(24, 1)` before `node(0, 16, 0, 0)`; the `u32`s `7`, `9` as one `i64.store` at `[24, 32)` and the pair `(24, 2)` before `node(1, 16, 0, 0)`; the two handles at `[0, 8)`, `accept(node(2, 0, 0, 2))`): `binMod_fixed_sound`, `binMod_sound` (Hoare proof `bin_sat`, decoding `blob_node`, `seq_node`), `binMod_live` (traced session), `binMod_lang` (exactly `{pair(blob [0xFF], seq [7, 9])}`, no sentinel, no UB). **Against the pure canonical ABI reference loaders** `MemSound.WitAst.Canon` (memory32): `loadVals mem ps ptr` is the payload step of `node` at the call's memory (`witNode_loadVals`: every decoded node's payload is `loadVals` at its payload pointer); for scalar vectors (`SPTy`: `bool`, `s32`, `u32`, `s64`, `u64`) `loadVals_loadRecord` proves `(loadVals mem ps ptr).map toScalarValues = ABI.loadRecord ts mem ptr` (`Reference/ABI/Memory`), an equation of options, so values and failures (misalignment, out of bounds) coincide, with an injective value translation (`toScalarValues_injective`); `readPtrLen_load`: a `(ptr, len)` pair is the two reference `ABI.Scalar.load .u32` loads; `readVal_string_loadStringFromRange`: given its pair, a `string` payload is `ABI.loadStringFromRange? .utf8 .i32` (`Reference/ABI/String`) for `len ≤ ABI.maxStringByteLength` (same text or same failure: bounds, invalid UTF-8), while above the limit the reference traps and the decoder does not check. `SPTy` now covers all nine canonical scalars (`bool`, `s8`…`u64`); single values `loadVal mem t a`: `loadVal_scalar` (`ABI.Scalar.load`), `loadVal_f32`, `loadVal_f64` (`ABI.loadFloat`: NaNs canonicalised), `loadVal_char` (`ABI.loadChar`: surrogates and values `≥ 0x110000` fail in both), equations of options. There is no pure reference list, record-with-non-scalar-fields, variant or flags loader under `Reference/ABI/` (REF `load_list*`, `load_record`, `load_variant`, `load_flags` exist only as the monadic `Canon.Load` programs), so `bytes`, `list t`, fixed lists and the composite types are not compared with a reference loader. **Records, options and chars end to end**: `glyphSig` (`glyph`: one `record { ch: char, size: option<u8> }` (`glyphTy`, eight bytes), arity `fixed 0`; `pair`: no payload, arity `fixed 2`) and `glyphMod` (the record `{ 'a', some(7) }` as one `i64.store` at `[16, 24)` before `node(0, 16, 0, 0)`, the same with `{ 'λ', none }`, the two handles at `[0, 8)`, `accept(node(1, 0, 0, 2))`): `glyphMod_fixed_sound`, `glyphMod_sound` (Hoare proof `glyph_sat`, payloads `readVals_glyphA`, `readVals_glyphB`), `glyphMod_live` (traced session), `glyphMod_lang` (exactly `{pair(glyph { 'a', some(7) }, glyph { 'λ', none })}`, no sentinel, no UB) |
| simple APIs are special cases | done | `Api.sexpW_hom` (writer homomorphism), `sexpLang_eq_astLang`, generic `writerLang_hom`/`writerLang_hom_subset` |
| SExpr ≅ single payload-free variadic branch tag + atom leaves | done | `sexpSig`, `SExp.equivAST : SExp α ≃ {x // WellArity x}`; atoms are not unlabelled internal nodes: `leaf_children_not_wellArity` |

### 5. Cons API and n-ary vs dotted

| Item | Status | Where |
| --- | --- | --- |
| `nil()`, `symbol`/atoms, `cons(i32,i32)`; cons without `nil` | done | `Api.consW` (`SExp2`), `Api.pairW` (`Tree2`), `consW_childRel`. Through memory: `MemSound.Cons` (`consWrite`: `symbol`/`string`/`blob(ptr, len)` atoms from memory, `nil()`, `cons(a, b)`; `consWriterLang` over `SExp2 MemAtom`; generic bridges `rolesFixedLang_subset`, `rolesWriterLang_subset` for any roles and writer); `consMod` (`accept(cons(symbol(0, 2), nil()))`): `consMod_fixed_sound`, `consMod_sound`, `consMod_live`, `consMod_lang` (exactly `{(hi)}`, no sentinel, no UB); mixed atom kinds: `consMix` (`symbol(0, 2)` and `string(0, 2)` over `68 69`, re-stored before each call since hosts may rewrite memory, `nil()`, two `cons`): `consMix_fixed_sound`, `consMix_sound`, `consMix_live`, `consMix_lang` (exactly `{(hi "hi")}`, a symbol and a string atom) |
| n-ary vs `SExp2` (improper lists), properness, roundtrips | done | existing `SExp.toSExp2`, `toSExp2_injective`, `proper_iff_exists`; new `SExp2.toSExp?` with `toSExp?_toSExp2`, `toSExp2_of_toSExp?`, `isProper_iff_toSExp?` |
| tagged AST embeddings | done | existing `TExpr.equivSExp`, `TExpr1.equivTree2`, `TExpr1.equivSExp2`; new `SExp.equivAST` |

### 6. Abstract acceptors

| Item | Status | Where |
| --- | --- | --- |
| union/intersection, images/preimages (incl. `SExp → SExp2`) | done | languages are `Set`s; `Set.image SExp.toSExp2` etc.; homomorphism images `writerLang_hom` |
| combinators `(a₁ a₂)`, `(a₁ … aₙ)`, `star` | done | `pair`, `tuple`, `star`; `mem_pair`, `tuple_inter`, `pair_inter_left`, `pair_union_left`, `tuple_subset_star` |
| patterns over SExpr/SExpr2/AST with acceptors as an extra atom | done | `Pat`, `Pat2`, `PatAST` and their `lang`; `Pat.lang_ground`, `Pat.lang_mono`, `Pat2.lang_ground`, `Pat2.lang_mono`, `Pat2.lang_ofList`, `PatAST.lang_ground`, `PatAST.lang_mono`; `Pat.toPat2` with `Pat.toSExp2_image_lang` (image of a proper pattern's language along `SExp → SExp2`) |
| AST→sexp `(tag arg₁…argₙ child₁…childₙ)`, per-tag layouts, soundness assumptions | done | `AST.encode`, `AST.encodeWith`, `AST.encode_injective` (`ArgLenFixed`), `encode_image_injective`; counterexample `Formats.Examples.enc_collides` |

### 7. Executable Wasm checkers

| Item | Status | Where |
| --- | --- | --- |
| module languages grounded in core Wasm | done (definitions) | `Wasm.Game.HandleAccept`: `playEvents enter decAsk decAns`, `handleTraces` over `(instOf m).strategy P s` plays (every profile, every environment, any export sequence); export-call moves `.inr (.ask _)` decode to `enter` (`some .enter` in every module language: `moduleConsLang`, `moduleSExpLang`, `moduleAstLang`, `moduleTree2Lang`, `Writers.moduleTraces`; `Memory.memTraces` reads `Tag.enter` likewise), so module languages see call boundaries and a trapped call is followed by further export calls on the same store |
| link from Hoare-logic specifications to language soundness | done | `readerLang_subset_of_AG` (generic, every `oa ≠ .ub`), `consLang_sound_of_gameSat`, `consLang_sound_callTrap`, `consLang_sound_of_forall` via `GameLink.strategy_sound`; writers `fixedLang_subset_of_AG`, `writerLang_subset_of_AG` |
| proper lists in `SExp2`, `[i64]` word lists, sorted word lists, subset theorem | done (soundness) | modules `properCheck`, `wordsCheck`, `sortedCheck` (validated by `decide +kernel`); `properCheck_sat`, `wordsCheck_sat`, `sortedCheck_sat` (`GameSat` with store invariant `consInv`, every profile, every environment `ρ`); unconditional `properCheck_sound`, `wordsCheck_sound`, `sortedCheck_sound` (`moduleConsLang P m consIx .trap oa Envs ⊆ L` for every `Envs` and every accept policy `oa ≠ .ub`, in particular the Wasm-facing `callTrap`). `properL` is **spine** properness (`SpineProperList`: nil-terminated `cdr` spine, any elements), which is what `properCheck` checks; recursive properness `recProperL` is strictly smaller (`recProperL_ssubset_properL`, with `dottedElem_mem_properL`/`dottedElem_not_mem_recProperL`); `sortedL_subset_wordsL`, `wordsL_subset_properL` |
| deeper properness | done | depth two: `recProperCheck` (`recProperCheck_sound` ⊆ `nestL`, `wordsL_ssubset_nestL`, `nestL_ssubset_recProperL`); full depth: `recFullCheck` (Wasm recursion; recursive calls proved by a size-indexed specification, `X.callSpec`): `recFullCheck_sat`, `recFullCheck_sound` (⊆ `recProperL`), `recFullCheck_accepts_deep1` (`(((1)))`), `recFullCheck_accepts_nested`, `recFullCheck_separates_deep1` (accepted by `recFullCheck`, rejected by `recProperCheck`). Non-proper inputs make the export trap. **Termination**: `recFullCheck_tsat` (`TGameSat` against `consISpec consIx ρ recProperL`, every profile and every `ρ`: every export call returns or traps; the variant is the number of cons cells of the tree the cursor denotes, finite since `ρ` maps handles to finite trees and correct `car`/`cdr` answers name subtrees; total rules `T.*`, `RT.*`, recursion `RT.self` in `Proofs/…/RecFull/Total.lean`), `recFullCheck_dsound` (the divergence-observing strategy refines `dagStrat`, via `dstrategy_sound`) |
| non-vacuity of the checkers | done | `Checkers.Examples`: replayed instance plays (`Silmaril.Wasm.Resource.Replay`, `replayExport_play`) decoded into reader runs (`mem_consLang_of_replay`; a replay starts with its export call, decoded as `enter`, which the Boolean checks pass), under the call-local trap: `properCheck_accepts_12`, `wordsCheck_accepts_12`, `sortedCheck_accepts_12` (`ofAtoms [1, 2]`), `wordsCheck_accepts_21`, `properCheck_accepts_dottedElem`, for every profile admitting the deterministic interpreter's steps (`hP`) and every specification profile (`_spec`); negative: `sortedCheck_rejects_21`, `wordsCheck_rejects_dottedElem`, `properCheck_rejects_atom`. So `sortedL ⊊ wordsL ⊊ properL` is witnessed by the modules |
| signed `i32` handles vs `i64` payloads, sorting | done (stated) | `Checkers.Defs` docstring; `sortedL` uses signed `BitVec.sle` (`i64.le_s`) |
| other styles in Wasm (proved examples) | done | shared rules `Proofs/Wasm/Game/HandleAccept/Checkers/Generic.lean`. N-ary reader (`count`/`child`): `pairCheck_sound`, `wordsNCheck_sound` (`SExp.ofAtoms ws`), `sortedNCheck_sound`, `sortedNL_subset_wordsNL`. AST reader: `addCheck_sound` (`add(num a, num b)`). Parsing export: `nzParse_sound`/`nzParse_input` (one-shot inputs are single nonzero words; the tree is unconstrained because the export spec cannot constrain its imports). Binary trees (`Tree2`, cons without nil): writer/reader decoders, `combCheck_sound` (right combs of words). Writer: `twoWords_sound`, `twoWords_fixed_sound` (accepts only `(x x+1)`), for policies without a sentinel (the module does not test for failures). Structural bounds for every module: `moduleConsWLang_subset_atoms2`, `moduleSxWLang_subset_arities`, `moduleAstWLang_wellArity`, `moduleParseRel_input_oneShot`, `memWriterLang_subset_atoms` |
| sentinel writers `0` and `-1` | done | `twoWordsZ`, `twoWordsM` test each write result against the sentinel: `twoWordsZ_sat`/`twoWordsM_sat`, `twoWordsZ_sound`/`twoWordsM_sound` (store semantics, `pol.sentinel = some 0` resp. `some (-1)`), fixed-environment versions, `twoWordsZ_accepts_0/_5`, `twoWordsM_accepts_0/_5` (handle `0` valid under sentinel `-1`), failure replays `twoWordsZ_fail_accepts_nothing`, `twoWordsM_fail_accepts_nothing`, `twoWordsZ_lateFail_accepts_nothing` |
| family × API audit | done | `HandleAccept.Families`: 10 families × 5 APIs as named instantiations (table in `Families/Defs.lean`, every row names its Wasm theorems). `Families.Matrix`: for every pair a core Wasm module over the family's own atom type with a Hoare-logic language bound (`_sound`) and a traced session accepting a tree (`_live`): n-ary writer `pairAtomMod` (exactly `(a b)`; words `wordMod`, exactly `42`), cons writer `consAtomMod` (exactly `(a)`; words `twoWords`), AST writer the n-ary module read at `sexpSig` (`tabAstWriterLang_eq`), n-ary/cons/AST readers `probeMod` (`firstAtoms`, `carAtoms`, `firstLeaves`). No pair is left without a module |
| non-vacuity of the other styles | done | generic replay decoding `Proofs/Wasm/Game/HandleAccept/Replay.lean` (`mem_readerLang_of_replay`, `mem_writerLang_of_replay`); `pairCheck_accepts_12`, `wordsNCheck_accepts_12`, `sortedNCheck_accepts_12`, `wordsNCheck_accepts_21`, `sortedNCheck_rejects_21`; `addCheck_accepts_12`; `combCheck_accepts_123`; `twoWords_accepts_0`, `twoWords_accepts_5` (fresh-handle host); `nzParse_relates_7` (needs `replayExportR`, which also records the export's answer). All for profiles admitting the deterministic interpreter's steps (`hP`) and every specification profile (`_spec`) |

### 8. Combined writer + reader

| Item | Status | Where |
| --- | --- | --- |
| successful writes agree with any future read; persistent immutable meanings; interning | done | `CEv`, `combined`, `combined_cut`, `combined_write`, `combined_read`, `combined_write_read`, `Reader.Mono.persist`; monotone readers `sexpR_mono`, `consR_mono`, `astR_mono` |
| all reader invalidity and writer failure policies | done | `CStep` reuses `WStep` and `answers` (every `OnBadRead`) |

### 9. Parsing variants

| Item | Status | Where |
| --- | --- | --- |
| a. `parse(data) -> i32`, sentinel failure | done | `PEv.parse`, `resolve`, `oneShotRel` |
| b. `append(data)`, `done() -> i32` | done | `PEv.append/done`, `parseRel_done`, `pending`, `doneClears` |
| c. chunks, `done() -> (used, tree)`, cursor, failure advances, unconsumed suffix, bounds | done | `PEv.feed/finish`, `Returns`, `run_cursor`, `parseRel_slice` (for the session-abort overrun policy `onOverrun = .sessionTrap`), `onOverrun`, `usedOfI32`/`usedOfI32_lt`, `Examples.chunk_example`, and for every overrun policy without UB (incl. call-local) `run_cursor_eff`, `parseRel_slice_eff` (`effConsumed` counts only answered `finish` calls; `effConsumed_eq_consumed` under session abort) |
| invalid returned handle, overrun: traps | done | every parsing event is itself an export call ending with its returned handle, so a call-local trap (`callTrap`, the default) is that call relating nothing while the session continues; it coincides with `ignore` (`PStep.retBadIgnore`, `PStep.overrunIgnore`). `sessionTrap` aborts the session (`PStep.retBadSessionTrap`, `dead`; an overrun has no answer) |
| repeated `done`, sessions, `reset` | done | `doneClears`, `PEv.reset`, `Examples.done_twice` |
| projections, membership, monotonicity, unions, non-preservation of intersections | done | `inputLang`, `treeLang`, `inputLang_union`, `inputLang_inter_subset`, `parseRel_mono`, `parseRel_union`, `Examples.projection_inter_strict` |
| trees resolved in consistent environments; mixed APIs with parsing; Wasm tie-ins | done (one-shot `parse` in Wasm) | `Semantics.Accept.Mixed`: `mixedRel` resolves returned handles in the **current writer store** (`run_resolve_stable`, `mixedRel_constructed`), `mixedFixedRel` over fixed environments, `mixedRel_subset_parseRel`, `mixedRel_subset_of_AG`; Wasm `HandleAccept.Mixed`: `moduleMixedRel`, `moduleMixedRel_sound_of_gameSat` (writer import answers agree with ρ, export spec constrains the returned tree); example `listParse`: `listParse_sound`/`listParse_rel` (every related pair is `([x], (x))`, `x ≠ 0`), non-vacuous `listParse_relates_7`, `listParse_rel_eq_7`. Streaming: ghost-state export specifications (`SSpec`, `SGameSat`, `strategy_sag`, `moduleMixedRel_sound_of_streamSat`, semantic `mixedRel_subset_of_streamAG`); example `stackParse` (`append(x)`/`done()`): `stackParse_sound`, `stackParse_rel` (every pair is `(vs, ofAtoms vs.reverse)`), `stackParse_relates_78`, `stackParse_rel_eq_78` (replayed session of three export calls). Requires no writer sentinel and `doneClears`. Chunk exports (`feed`/`finish -> (used, tree)`): `Mixed.Chunk`, `chunkSSpec` (ghost = chunk buffer), `moduleMixedRel_sound_of_chunkSat` (with the semantic `Semantics.Accept.Mixed.Chunk`: `chunkStep`, `chunkFold`, `pstep_buf`, `mixedRel_subset_of_chunkAG`, `mixedFixedRel_subset_of_chunkAG`, assume/guarantee along the chunk buffer), over fixed environments `moduleMixedFixedRel_sound_of_chunkSat` (every writer policy), `chunkStack_fixed_sound`; example `chunkStack` (`feed(x : i64)`, `finish(n) -> (used, tree)`, all-or-nothing consumption): `chunkStack_sat`, `chunkStack_sound`, `chunkStack_relates_78`, `chunkStack_relates_nil`, `chunkStack_rel_eq_78` (replayed `feed(7) feed(8) finish(1) finish(5)`: the values stay buffered across a `finish` that consumes none). Partial consumption: `Mixed.Chunk.Take`, `chunkTake` (two `i64` slots and a count in globals; `finish(n)` consumes exactly the oldest `n` when `0 < n ≤` count and returns their list, otherwise `(0, ())`): `chunkTake_sat`, `chunkTake_sound`, `chunkTake_fixed_sound`, `chunkTake_rel` (every pair is `(vs, ofAtoms vs)`), replayed `feed(7) feed(8) finish(1) finish(1)`: `chunkTake_relates_7` (`used = 1` of `2` buffered), `chunkTake_relates_8` (the value left buffered), `chunkTake_rel_eq_8`. Memory buffer: `Mixed.Chunk.Ring`, `chunkRingN cap` (a ring buffer of up to `cap` `i64`s in linear memory, start slot and count in globals, slots `8 * ((st + i) mod cap)`; `feed` traps without writing when the buffer is full; `finish(n)` builds the list of the oldest `n` values in a loop and advances the start slot, consuming exactly `n` when `0 < n ≤` count, otherwise `(0, ())`; `chunkRing = chunkRingN 8`), with **one proof generic in the capacity** for every `RingCap cap` (`0 < cap ≤ 8192`, the buffer within the one page): `chunkRingN_sat` (invariant `ringInv cap`: the memory loads at `slot cap st i` are the chunk buffer; the instance shape, code, globals and memory are kernel evaluations with `cap` free, `kernel_rfl`, `MShape.of_okNB`; slot arithmetic with `cap` symbolic, `slot_addr`, `slot_ne`), `chunkRingN_sound`, `chunkRingN_fixed_sound`, `chunkRingN_rel` (every pair is `(vs, ofAtoms vs)`), restated for eight slots as `chunkRing_sat`, `chunkRing_sound`, `chunkRing_fixed_sound`, `chunkRing_rel`; non-vacuity for every `2 ≤ cap ≤ 8192` at once: `chunkRingN_relates_7`, `chunkRingN_relates_8`, `chunkRingN_rel_eq_8` (`feed(7) feed(8) finish(1) finish(1)`: the second `finish` consumes the value left in memory), instances `chunkRing_relates_7`, `chunkRing_relates_8`, `chunkRing_rel_eq_8` (eight slots) and `chunkRing8192_relates_8`, `chunkRing8192_rel_eq_8` (the whole page); one value for every `1 ≤ cap ≤ 8192`: `chunkRingN_relates_7_one` (`feed(7) finish(1)`, `RingLive.ring_session1`), with the one-slot buffer `chunkRing1_relates_7`, `chunkRing1_rel_eq_7`; for **every profile**, by a play built forwards (`RingLive.ring_session`): the kernel replay used for `chunkTake` does not scale to a 64 KiB page, so the runs between callouts are composed from Core `Step` rules with the store symbolic (straight-line code by `exec_sound`, memory by `load_store_same`/`load_store_disjoint`, slot addresses from `cap` by `mod_small`), and only the decoded moves are checked by kernel evaluation (`mem_moduleMixedRel_of_path`) |

### Cautions

| Caution | Where |
| --- | --- |
| explicitly quantified environments | `Envs` parameters, `fix`, `langOver` |
| restriction vs nondeterminism vs trap vs UB top | `Sim`, `Phase.dead`, `Phase.chaos` |
| well-founded fixed environments, no silent cycles | `NodeEnv`, `UnfoldN`/`Unfold`, `not_unfold_of_cycle`, `realize_realizes`, `Examples.cycle_unfolds_to_nothing` |
| sentinel inclusion via observations/renamings, allocation failure | `writerLang_rename`, `writerLang_sentinel_swap`, `writerLang_noRet_subset`, `sentinel_twice` |
| intersection is not preserved by projection or trace languages | `Host.lang_inter_subset`, `inputLang_inter_subset`, `Examples.inter_strict`, `projection_inter_strict` |

### Hinted family writer coverage

`Families.Hinted.Thms` proves that the family table and the dedicated hinted writer
decode the same call and answer events. Its n-ary and AST writer languages for
`hintedSepMod` are exactly the atom `[hi]ab` (respectively the corresponding typed leaf)
for non-UB policies. This exercises the real four-operand import with disjoint hint
and octet segments.

`Families.Mixed.Examples` runs additional Core exports with checked reply shapes and decodes
their memory callouts through the family tables. The n-ary traces build a symbol/string list
and a blob/keyword list; the AST writer accepts the typed image of the symbol/string trace.
The cons replay calls both `hinted` and `blob` and accepts a two-cell list, retaining the
head's hint. These are acceptance results for the decoded small-memory replay traces, not
soundness or completeness over arbitrary Wasm sessions.

### Reference resource lifecycle

`Wit.Resources` runs the reference `resource.new`, `resource.rep` and `resource.drop`
built-ins, including their destructor dispatcher. `take` uses canonical `liftOwn` and
retains the consumed handle's arena identity as well as its representation. The machine
examples check slot reuse with two different identities that share a representation,
drop, and the observable early slot removal on a wrong-type lift that locks down the
component.

`Own.ReferenceTable` relates usable Core table lookups to the current reference arena.
Successful `Nested.reserve` refines one canonical owner move, whose witness retains the
arena identity; committing that slot preserves the relation at every other lookup. The
relation does not identify equal representations or use guest slots as identity. A failed
checked preflight does not perform the canonical removal: a wrong-type, lent or non-owning
canonical lift removes the slot before trapping. `resolveTypes_refines_eager` lifts the
success refinement through the shared traversal of an entire already-decoded payload, including
nested lists, products and sums. It preserves the typed value, live lookups and reservation
order; the eager path records nominal receipts. An executable compact-UTF-16 record example
compares both memory decoders with two equal-representation owners in different nested fields.
Malformed text gives a checked refusal, but the canonical trap retains both prior removals.
The general refinement starts after byte decoding; it is not whole-memory-decoder equivalence
or a failure equivalence between the host contracts.

## Modelling choices to review

`Wit.Async.Transfer` gives the endpoint interpretation a canonical lift/lower boundary:
it removes the guest slot on successful lift and retains the arena object in the typed
value. Lowering checks that this object is live, correctly typed, idle, not registered
with a waitable set, and currently detached. Duplicate Lean values do not duplicate
ownership. The reference-machine examples exercise a byte stream and a completing unit
future, including rejected retagging and repeat lowering. Schemas containing a borrow
are rejected before any transfer effects.

`Wit.Stored.Endpoints.Future.Examples` verifies a two-instance handoff of a tree
holding a future with a compound `{ word : u16, hint : option<bool> }` element.
It checks single-use transfer, cancellation without a destination write, polling
before and after completion, exact bytes in the reader memory, and removal of both
endpoints and the waitable set. It proves the concrete reference-machine session,
not a scheduling theorem or a Core adapter.

* **Traps are call-local.** The Wasm-facing mandatory trap on an invalid `accept` is
  `OnInvalid.callTrap` (the default): as in Wasm, a trap aborts only the current export
  invocation, while the instance and its store persist (the game strategy
  `ScalarInstance.strategy` keeps the store across export calls) and the environment may make
  arbitrary further export calls. The environment moves to `aborted`; only the next export call
  (`enter`) may follow and resumes `live` with the store unchanged (`WStep.aborted_inv`).
  Effects before the trap are not rolled back: successful writes stay allocated
  (`write_persists`, `Run.store_extends`, `Examples.persist_seven`).
* Aborting the whole session (`OnInvalid.sessionTrap`, phase `dead`) is an optional stricter
  policy. Ranks `sessionTrap ≤ callTrap ≤ ignore ≤ ub` order the languages
  (`writerLang_sessionTrap_subset_callTrap`, `writerLang_callTrap_subset_ignore`,
  `writerLang_ignore_subset_ub` and the reader analogues), both inclusions around `callTrap` are
  strict (`Examples.callTrap_ne_sessionTrap`, `Examples.callTrap_ne_ignore`), and within one
  export call the two traps agree (`writerLang_callTrap_eq_sessionTrap`,
  `readerLang_callTrap_eq_sessionTrap`). Reader soundness (`readerLang_trap_subset`, the
  checker theorems `*_sound`) holds for every accept policy but `ub`.
* Parsing exports are themselves the export calls: a trapped `parse`/`done` relates nothing and
  the session continues (`callTrap` coincides with `ignore` there); the cursor theorems assume
  the session-abort overrun policy.
* Allocation failure with a sentinel is always allowed (capacity is the environment's); without
  a sentinel a failing allocation traps.
* `SExp2.toSExp?` is defined by classical choice (the unique preimage); a computable decoder is
  not provided.
* The Wasm reading uses instance plays (`Verify.instOf`, every profile), which carry argument
  values and results but not memory.

## Remaining obligations

* Memory ASTs: `MemSound.WitAst` has the canonical ABI layout (`layout_toWit`,
  `valsLayout_toWit`), and its decoding is proved equal to the **pure** reference loaders only
  for scalar payload vectors
  (`loadVals_loadRecord` against `ABI.loadRecord`) and for UTF-8 strings of at most
  `MAX_STRING_BYTE_LENGTH` bytes (`readPtrLen_load`, `readVal_string_loadStringFromRange` against
  `ABI.loadStringFromRange?`), failures included. Not proved: `bytes` and `list t` against any
  reference (the repository has no pure list loader; REF `load_list*` exist only as monadic
  `Canon.Load` programs), mixed vectors as one record equation (`loadRecord` has only scalar
  fields), and any equation with the monadic `Canon.load` programs over a component store. The
  legacy memory decoder checks bounds but not `MAX_STRING_BYTE_LENGTH`/`MAX_LIST_BYTE_LENGTH`.
  The checked host boundary (`MemSound.WitAst.Checked.Thms`) applies both limits to payload
  indirections and the list limit to child handles. `checked_string_reference` identifies
  UTF-8, UTF-16 and tagged Latin-1/UTF-16 text decoding with the pure canonical range
  loader, including failure. This uses bounded slices and leaves the legacy UTF-8 trace
  decoder unchanged. The checked path also accepts memory64: `layoutFor_toWit` relates
  the layouts at both widths, and `checked_string_reference` covers all string modes at
  both widths. Its memory64 `node` operands use `i64` payload pointer, child pointer and
  child count; tag, child handles and owning slot indices remain `i32`. Width mismatches,
  high out-of-bounds pointers and overlong child vectors are rejected without narrowing.
  Flat arguments and asynchronous calls are still rejected at this Core entry point.
  This is not a proof of interoperability with monadic component-ABI lifting.
  Floats, `char` and single scalars agree with the pure
  reference loaders (`loadVal_f32`, `loadVal_f64`, `loadVal_char`, `loadVal_scalar`); lists,
  fixed lists, records with non-scalar fields, tuples, variants, enums, options, results and
  flags follow the reference layout (`layout_toWit`) and trap conditions (discriminant range,
  Unicode scalar values, NaN canonicalisation, ignored high flag bits) but are compared with no
  reference loader (none is pure). The end-to-end modules cover `s64`, `string`, `bytes`,
  `list<u32>` and a `record { char, option<u8> }`; nested lists, variants, enums, results,
  flags, fixed lists and floats are covered by kernel-checked decoding examples only.
  **Resource handles**: the public Core host entry point is `MemSound.WitAst.Own`. Use
  `Contract.link` to check the import's name, uniqueness and Core function type and to resolve the
  actual instance memory for `Contract.env`. `Contract.traces` uses that checked host over all
  permitted export sequences, not an arbitrary reply environment. There is no acceptor CLI driver.
  The host validates the complete selected schema, including inactive cases and empty lists.
  It resolves `own` fields recursively and reserves distinct live slots before committing their
  moves. `Contract.attempt` retains typed diagnostics, including unknown, dead, wrong-type and
  repeated handles. Rejection answers the Core redex with a call-local trap and leaves the store,
  resource table and writer state at the import unchanged. `reject_then_invoke` proves a later
  typed export can use that state; `session_le` rules out resurrecting moved slots in this host.
  Stored `borrow` and unsupported async kinds are rejected.
  The Core writer stores representations and has no allocation/drop imports; the separate
  reference resource machine is not a simulation of these slot moves or call-local trap effects.
  `Own.Projection` contains the legacy `ownMod` and `twiceMod` trace-language results. It omits
  failed decodes and is not a host. `Own.Session.Replay.accepts_then_traps` instead uses the linked
  checked host for two actual `ownMod` invocations: the first consumes the live slot and accepts
  `res(rep)`; the second diagnoses that slot as dead and traps without erasing the earlier tree
  or reviving the slot. `Own.Session.Audit` retains the typed diagnostic at the actual reply
  in any checked Core session. `instrument` and `erase` relate the whole session in both
  directions, including export retries; `Audit.reject_then_invoke` records the rejection
  without changing the reached store or writer. `Replay.audited_accepts_then_traps` checks
  the exact three answered imports in the two-export replay. That proof reads only the written
  handle bytes, with the rest of memory symbolic. `Own.Session.Replay.Language.Thms` closes the
  upper bound for this checked example: a Hoare contract fixes the actual node arguments and
  handle bytes on every reached import, and the checked writer can only build then accept one
  tree in an arbitrary export prefix. The language is exactly `{res(rep)}` if slot `1` is live
  at type `0`, and empty if it is absent, dead or of a different type. Live slots elsewhere
  are unrestricted. This theorem describes the move-only example, not the reference-machine
  scheduler's accepted language.
* Wasm writer variants: `errAccept_exact`, `allAccept_exact` and `batchAccept_exact` give their
  exact languages for the zero-sentinel, non-UB policy and profiles admitting deterministic
  Core execution. The lower bounds use symbolic replays for every input word, not just a fixed
  witness. `batchAccept_drops` still rules out the dropped words, and the batch bridge still
  assumes policies without undefined behaviour. `Combined.Exact.Thms.readBack_exact` gives
  exactly the singleton word lists for any sentinel under the same non-UB and profile
  assumptions. Its replay picks one of two disjoint sets of fresh handles.
* Families through memory: `MemSound.ListCheck.Loop` adds variable-length Core checkers for
  symbols and blobs. `symbols_sound` and `blobs_sound` bound the accepted language across all
  permitted export calls under shaped replies and the trapping read policy, excluding UB
  acceptance. The checker rereads `items` after each child call. The invariant tracks the
  denoted prefix, not the memory or the numeric child handles. It traps before any word load
  that would wrap the scaled index or cross the memory32 range; `address_eq` relates the guarded
  Wasm address to the decoder's natural address. `symbols_bounded` and `blobs_bounded` prove
  that no accepted list exceeds `2 ^ 30` children, even with changing vector bases and without
  using the size of any particular host memory image as a session invariant.
  `Loop.Run.accepts_of_plan` uses `remaining_decreases` to build an actual accepting export
  prefix of either checker for every finite vector with correctly denoting replies. The proof
  takes the empty vector straight to `accept`, and reloads each repeated handle at its own
  position without retaining memory across child replies. `compact_reply_plan` constructs
  that plan with the checked `items` encoder when the header and vector fit and the child reply
  bytes keep the same memory size. `checkedPageShape_all` and `checker_instance_pages`
  prove the checked shape and actual specification instance for every memory32 initial
  page count, including zero and the address-space maximum, without evaluating memory
  contents. `byte_reply_accepts_pages` needs only a fitting, correctly denoting byte
  script, not a separately supplied shape or instance proof. The two-page run writes
  a 65,537-byte reply into its actual memory. This lower bound does not establish
  equality with the general memory32 upper bound, guest growth, or termination under
  arbitrary replies. The older `symListMod` and `blobListMod` remain two-child examples.
  `Loop.Growing.mod` runs the same loop after a Core prologue that reserves a requested
  minimum page count. `Growing.validates` covers both variants at every legal initial
  page count. `Growing.reserve_hwp` sends refusal to a trap in the unchanged store before
  any import. Otherwise the loop runs with the requested minimum and a reset index.
  `Growing.bounded` proves the same word-bound result over arbitrary export prefixes
  for a host that preserves the address width and bounded page count; the checked in-place
  byte reply host meets that contract. The executable regression retries from refused
  growth, reads mixed-size and repeated blobs using the second page, rejects a request
  above memory32, and reuses the grown store without requesting more growth.
  `Growing.byte_reply_accepts` constructs an accepting export prefix for every fitting,
  correctly denoting compact script when any necessary growth may succeed. The proof
  executes the actual Core reservation before using the shared read-loop trace; it does
  not bound all host layouts by the compact layout or assert termination for arbitrary hosts.
* Parsing: the fixed-page `chunkRingN` can trap when a slot crosses the page boundary.
  `chunkRingGrowing` reserves the configured capacity on demand, up to the memory32 address
  bound (`0 < cap ≤ 2^29`). Its two exports share the fixed-page ring's chunk soundness
  proof. The full-buffer guard precedes reservation; `chunkRingGrowing_feed_full`
  in `Ring.Progress.Thms` takes the actual export to a call-local trap in finitely many
  Core steps, without allocation, host calls, or any store change. Growth refusal
  also traps before buffer writes or cursor updates. The executable regression retries after grow refusal, fills 8193
  slots, rejects the next feed, finishes a chunk, and retries in the freed slot.
  This is not exact acceptance or a whole-session termination theorem; progress also
  depends on available memory, the writer responses, and the execution profile.

## Reference component payloads

`Wit.Stored` builds the existing `AST` family over closed WIT types and reference `Val` values.
Its memory and flat entry points check their ABI preconditions, then run the canonical effect
programs rather than interpreting an endpoint as a number. A successful lift uses the reference
arena identity while consuming the guest slot. A later reference trap retains earlier moves.
Stored borrows and `own` types are rejected recursively before effects: the reference `Val.own`
alone carries a representation, not the owning identity this tree boundary needs.

`Wit.Stored.OwnedMemory` is the separate ownership-aware tree boundary. Its shared canonical
memory and flat loaders record an ordered, typed receipt at each active `own` leaf, including
inside lists, records and variants. Erasing the receipts recovers the entire canonical load
program, including the flat cursor, access checks, handle removals and traps in their original
order. The reference machine examples distinguish two owners with equal representations and
show that a repeated move traps without publishing a tree or undoing the first move. The flat
examples cover a list's indirect owner and an option's direct owner in the same value; a wrong
slot type in an inactive case is rejected before either move, and a corrected retry succeeds.
Whole-schema validation still rejects stored borrows. The receipts do not by themselves
authorize a transfer back to a guest or connect the checked Core host to the reference machine.

`OwnedMemory.Conservative.Thms` relates the two checked tree boundaries on primitive
payloads, including the named `ScalarType` fragment. After receipt erasure, memory
and flat lifting have the identical effect program, including typed input failures
and canonical traps. Primitive node construction preserves this equality through the
arity check and maps arbitrary existing children in order.

`OwnedMemory.Plain.Thms` gives a typed equivalence for every payload and tree admitted
by the older stored-value schema check. Its recursive proof rules out own receipts in
all compound cases; the inverse preserves values, tags and children. Endpoint identities
stay unchanged even when their element schema contains owners, because lifting an endpoint
does not lift its elements. A borrow anywhere in the schema still rejects.
`OwnedMemory.Plain.Lift.Thms` lifts that equivalence to the entire checked memory and flat
programs, including memory/flat guards, traversal of compound fields and choices, and
node arity. The argument-vector theorem also covers preserved cursor position and the
one-pointer spill. These results do not grant authority, support stored borrows, or equate
entire Core export sessions.

`Wit.Stored.OwnedMemory.Claims` registers owner receipts and readable endpoint claims together
from a freshly lifted root. Held claims, not the accepted observations, authorize a canonical
`lower_own`, destructor request or endpoint transfer. `give` commits spending after insertion
succeeds; `drop` commits it before calling the supplied reference destructor. `giveEndpoint`
spends the validated claim before canonical lower updates the endpoint's owner.
The spend theorems identify the original nominal type, handle object and representation,
preserve other claims and accepted trees, and rule out a second use of the spent identity.
The machine examples create two equal-representation resources, reject a wrong-type transfer,
retry, drop the other owner and reacquire owners in reused guest slots. Reacquiring a newly
issued handle object creates a fresh claim, not another claim on the earlier handle object.
A mixed record replay lifts an owner and a stream from memory and gives each back once after
wrong-type refusals. A late flat-lift trap retains both successful removals but publishes
neither claim nor a tree. The full schema still rejects stored borrows before lifting. This is
a reference host session and does not yet lower a compound containing multiple claims in one call.

`Wit.Stored.OwnedMemory.Claims.Core` uses that same receipt-aware loader and claim state in
the separately linked, synchronous `accept-node` Core contract. A preflight refusal preserves
the entire call-entry state. A later canonical trap keeps prior Core writes and canonical table
effects, but publishes no root or claim. An executable Core replay rejects an inactive nested
borrow, accepts an owner and stream in one root, traps after moving both in a later call, and
accepts a fresh root in a subsequent export. The `accept-node` contract does not yet expose
mixed handoff or scheduled lifecycle imports.

The publication theorem in `Wit.Stored.OwnedMemory.Claims.Core.Trace` uses the same session
invariant as the endpoint-only contract. Across all permitted export sequences and prefixes,
successful replies are exactly the chronological handles of newly published roots. Rejections
never contribute a handle, including in an invocation that traps before a later successful
export. This identifies publication history, not a particular guest's exact payload language.

`Wit.Stored.OwnedMemory.Claims.Core.Plain` proves an exact session correspondence between
the endpoint-only and receipt-aware synchronous Core `accept-node` routes on `PlainSignature`.
The state embedding preserves the reference arena and held endpoint claims and embeds all
accepted trees. Actual calls agree on typed rejection and canonical effects, child lookup,
and the published handle. Both directions preserve all export prefixes, including the same
Core stores and tag traces after rejections and retries. This is a conservative extension
result for this pair of dispatchers, not yet for the scheduled canonical lifecycle API.

`Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain` joins that correspondence to the
actual checked Core embedder for a linked memory accept. Caller admission reads the active
thread, its instance and the live `mayLeave` bit; a wrong caller returns a typed refusal
without lifting or publishing. An admitted plain call agrees with the endpoint-only attempt
on arena effects, embedded writer, status and typed refusal. Success and refusal preserve
the parked Core continuation; a canonical trap locks down the reached store, keeps prior
journal effects and discards the continuations. Binding-resolution traps keep their typed
reason in the journal. Publication and reply remain distinct events. This is a single-call
comparison, not yet a correspondence for scheduled export prefixes, flat bindings or
deferred reply delivery.

`Wit.Stored.Endpoints` tracks readable endpoint claims separately from accepted tree observations.
Lifting a root from memory or flat operands registers the arena identities in its active payload,
including nested futures and streams. Already-built children are not lifted again and create no
claims. `give` checks the reference endpoint's kind, element type, liveness, idle state and
ownership before spending its claim. Spending precedes the canonical owner update and table
insertion, which can trap after the owner changes. A tree remains an observation
after handoff, not a second right to lower it. A verified mixed session lifts a future and a byte
stream into one tree, transfers them back, completes the future, copies two distinct stream bytes,
and closes both channels. This gives endpoints individually; it does not lower an entire compound
endpoint payload in one operation or connect the Core checked writer to the reference machine.

`Wit.Stored.Endpoints.Stream.Examples` moves an `option<stream<record{word: u16,
item: own<resource>}>>` into a tree and hands the readable endpoint to another instance once.
Accepting the endpoint does not lift the later elements or turn observations into ownership.
The reference copy moves two owners and their distinct scalar fields after a cancelled read and
retry; the reader drops both owners, observes peer closure, and a stale read traps without
erasing the accepted tree. Direct owned payloads still require identity receipts, even if
inactive, and stored borrows still reject throughout the schema, including endpoint elements.
This is a reference-machine replay, not checked Core export integration.

`Wit.Stored.Examples` records an `option<future>` from memory and a flat `stream<u8>` as typed
trees in actual reference-machine runs; a repeated slot traps with no new tree and does not
resurrect the slot. The examples do not route Core writer imports into component sessions or
provide a correspondence for their accepted languages.

`Wit.Stored.Endpoints.Core.Trace` observes only successful host replies as commits, not
reached import redexes or traps. For every traced session with the selected import present,
the committed handles are exactly the consecutive handles for the newly published roots, in
chronological order. The proof preserves the initial accepted trees and includes pending
prefixes, instantiation calls, and later exports after a trap. This is a publication trace
invariant, not a characterization of which payload trees a particular guest can produce.

`Wit.Stored.OwnedMemory.Payload` checks the ordered nominal type and representation at
every active owner leaf against its receipt, including maps and nested sum arms. Equal
representations do not make different nominal owners interchangeable. The receipt carries
the arena identity obtained by canonical lifting; shape validation does not by itself
authorize another transfer.

The separately linked `Wit.Stored.Endpoints.Core` contract accepts an indirect payload in a
synchronous atomic `accept-node` import. The canonical load reads the reached Core call's
memory and resolves endpoints in a persistent reference arena. Schema or ABI rejection leaves
both stores unchanged at call entry. Canonical load traps retain earlier arena updates, publish
no tree, and trap only the current Core call. The proofs relate the local load's read/update
prefix to reference machine steps (including the reference machine's own lockdown on trap).
An executable export replay checks an inactive nested borrow refusal, a successful compound
stream move, stale-slot rejection, and a later successful export. This trap-returning contract
does not cover the older split `node`/`accept` writer ABI or interpret scheduling operations.

`Wit.Stored.Endpoints.Core.Scheduled` puts separately linked checked accept and handoff imports
inside the reference scheduler. These imports return `(status, value)` to Core and retain the
typed diagnostic on refusal, so a rejected import does not force reference-machine lockdown.
Acceptance reuses the call-local checked load; handoff checks a separate held claim, the
destination instance, and the live arena kind and element type. Canonical built-ins still use
the unmodified reference dispatcher. The two-instance Core regression creates a stream and two
owners, rejects an unused nested borrow, accepts the owning stream into a tree, hands it off once,
cancels and retries a read, polls completion, transfers and drops both owners, observes peer
closure, and traps on a stale canonical read without erasing the accepted tree. The bounded
driver has a relational trace theorem. The same linked scheduler also runs a one-element
`future<record{word: u16, owner: own<R>}>` through Core exports: cancellation and retry, handoff,
copy, poll, owner drop, both endpoint drops, and a stale read. The future has its own two-operand
copy ABI and completion payload, independent of the stream count. Neither replay states an
exact accepted language for arbitrary exports or replaces the earlier trap-returning ABI.

The mixed owner/endpoint dispatcher `Wit.Stored.OwnedMemory.Claims.Core.Scheduled` records
each import's signature and arguments under a fresh ticket before dispatch. Status returns and
typed refusals record the same ticket; an invalid binding records a diagnostic before its
reference trap. A canonical destructor trap keeps the prior journal and does not manufacture
a status return. `extends_of_session` proves append-only history for arbitrary ordinary
reference-machine sessions. `checked_of_session` additionally restricts every writer change
to registration of a lifted root or a targeted spend; `checked_of_steps` permits raw host
programs only under the same write policy. An observed and spent owner identity cannot
return, even if a Core slot or representation is reused. A newly held endpoint requires a
new publication; unlike an owner receipt, it can be lifted again after a completed handoff.
The reentrant destructor replay checks exact journal order in both successful and trapping
runs, and refusal cannot republish claims. The writer theorem is not an exact accepted
payload language or a conformance theorem for every canonical store transition.

`Wit.Stored.ErrorContexts` copies an observed error context back to a guest slot only if its
immutable arena object exists in the current reference store. Unlike endpoint handoff, this
does not spend a claim. A verified session lifts an `option<error-context>`, drops the original
slot, rejects a missing identity, then gives the same object twice; dropping the first copy does
not invalidate the second. This operation does not lower arbitrary compound tree payloads.

`Wit.Stored.Lower` sends resource-free tree payloads to memory or an exact flat vector through
the reference canonical store/flatten programs. It checks ABI options and nested list/string
allocation preconditions before writing; canonical traps retain their reference effects. The
examples round-trip a nested record in memory64 and as flat operands and show that an
out-of-bounds destination writes nothing. Lowering an endpoint or error-context observation
requires its own checked transfer; this path rejects those schemas, including inactive cases.
`Wit.Stored.Endpoints.Lower` checks all active endpoint claims and error-context identities
before running the shared recursive emitter. A preflight refusal retains the claims for a
corrected retry. Each claim is spent at its transfer, before the endpoint's owner changes;
a late canonical trap preserves that commitment. This direct entry point rejects schemas
that can require guest realloc, even in an inactive
arm. A readable handle is inline even if its future or stream element contains a string,
list or map. Moving the handle does not require the allocator for a later element copy;
the read/write builtins validate their own memory and realloc options separately.
The separate `Wit.Stored.Endpoints.ListLower` path supports dynamic lists of
readable futures or streams. It rechecks all claims after canonical realloc, distinguishes
refusal before allocation from refusal after the allocator's effects, and spends each claim
before canonical lower updates ownership. Checked endpoint lists and the recursive
list/map emitter use the same `Canon.allocateListRange` and `Canon.storeListDescriptor`
programs as the reference: check the returned range in the reached state, and write
the pointer before the length. The post-realloc authority check remains separate.
Neither a late table trap nor an allocator's
reentrant effects roll back an earlier transfer. Arbitrary allocating compounds are still
rejected by the general entry point.

`Wit.Stored.Endpoints.RecordLower.lower` handles recursively nested mixed records, tuples,
options, variants, results, fixed lists and dynamic lists with plain data fields, readable
endpoints and error contexts. It checks
the complete schema, allocation preconditions and cross-field aliases before
any field is written. Fields follow canonical record layout and flat order. A field error identifies
the path to the failing field; completed fields and any realloc effects remain visible. Reference-machine
replays cover both outputs, nested padding, inactive unsupported fields, alias and missing-context
rejection, reentrancy and allocator traps. Every sum arm's schema is checked, including inactive
arms. Only the selected payload allocates or transfers claims; discriminants, payload alignment
and joined flat slots follow the canonical ABI. An allocator trap retains the written
discriminants and any allocator effects, but not an unperformed transfer. List elements use
the canonical element stride, including padding in compound elements. A dynamic list rechecks
its claims after realloc, before writing any element; a refusal then keeps earlier fields
and the allocator's effects. The compound-list replay covers a list of tuples containing fixed
lists of futures. Maps use the canonical key/value entry layout and the same checked
allocation as lists. A string-key allocator can reenter; a later endpoint refusal keeps
completed key writes but does not publish the map pointer and count. Mixed nominal owners
still reject, including in inactive map schemas.

`Wit.Stored.OwnedMemory.Claims.Record.lowerRoot` uses that same emitter for reference
records containing both nominal owners and endpoints. Active owner fields consume ordered
receipts only after checking their nominal type and representation; live authority is
looked up separately by arena identity. The whole plan is dry-run before writing, and
transfers after guest allocation revalidate against the reached state. Root preflight and
dynamic-region rechecks derive their plans from the same compiled fields the emitter
uses, in field order and with only the selected sum arm. `compileValue_plan` and
`compileRecord_plan` identify the diagnostic compiler output with those traversals;
`preflightValue_receipts` identifies the active owner subsequence with the original
list of nominal receipts, not just its representations. `compileValue_value` and
`compileRecord_value` reconstruct the exact input canonical value from the same fields,
including positional fields, ordered list and map entries, and the active sum arm.
`preflightValue_value` gives that equality for the compiler used by `givePayload` and
`giveFlat`. `preflightValue_layout` shows that the same compiled tree has the canonical
nested layout: declared fields, fixed counts, dynamic entry types (including map keys),
and the full layout and selected payload of every sum. The certificate does not confer
live authority or equate the emitter's effects
with the canonical ABI. Single give and the
recursive emitter spend only the targeted owner identity, before canonical allocation of
the owning arena object. A subsequent table insertion failure keeps the allocation and
does not restore the claim. The kernel-checked replays cover distinct equal-representation
owners, duplicate-receipt rejection followed by retry, slot reuse, inactive stored-borrow
rejection, reentrant realloc, and a late trap that preserves the earlier owner transfer and
memory write. `Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Binding.giveRecord` exposes
whole-record lowering to Core as `(tree, destination) → (status, value)`. It resolves the
linked memory and optional realloc slots and checks their live width and function type before
using a tree's claims. Its successful effects spend the same targeted identities as individual
give/drop bindings, so the arbitrary-session writer and transcript theorems include the new
import. The linked Core replay covers invalid destination profiles, successful retry, a nested
stream with two equal-representation owners, reacquisition through reused slots, rejection of
the old root, and successful delivery of the new root.
`Binding.givePayload` uses the same linked ABI and conservation theorem for other supported
roots, rather than requiring a record at the outermost level. It checks the whole payload
type, receipt plan and destination range before transferring the first claim, then uses the
same effect-aware emitter as the record binding. The Core replay also exercises a tuple root
with both owners and an optional stream, distinct typed refusal diagnostics, and exact
destination bytes.
`Binding.giveFlat` links a checked payload schema and returns a Core status followed by
the canonical multivalue vector for that schema. A tree with a different schema is refused
before lowering, even when its flat shape is identical. The transcript records successful
vectors or typed diagnostics; refusal padding has the declared Core types. The same
arbitrary-session writer conservation theorem applies. The Core replay covers a wrong
schema followed by a successful compound owner/stream handoff and then a spent-claim
refusal. This is an explicit Core import convention, not the component ABI's
call-lowering decision about direct versus indirect results. The defensive result-shape
check does not roll back effects of the emitter.

`CoreGrowthSteps` frames the linked memory address, pointer width, and bounds of already
valid regions across certified scheduler prefixes. It permits guest byte writes and memory
growth. Core instructions and canonical memory writes supply growth proofs. The scheduler
carries program certificates through calls, returns, blocking and resumption. The actual
canonical allocator, implicit lift thread, synchronous lift loop, and caller start and
resolve programs supply installation certificates; arbitrary guest callouts and injected
host programs do not inherit one.
In a closed realloc window, a same-instance
reentrant `givePayload` or `giveFlat` with a valid binding takes the actual typed
`wrongContext` reply, journals the refusal, and resumes parked Core without changing the
component store or writer. The resumed control retains its continuation certificates,
so the refusal segment composes with the certified prefixes before and after it.
`parked_closed_give_writer_frame` pairs those segments even if earlier checked spends
made the writers different: the reply, journal update, and resumed Core control are the
same, with each writer left in place. This
does not assume the allocator's bytes are unchanged, certify every callback trace, or validate the
range newly returned by realloc, which canonical lowering checks in the reached store.

The collection program laws factor both canonical outputs into ordered child
programs. Fixed memory lists are in-place; dynamic lists and maps share the
canonical request, reached-range validation and descriptor suffix. Flat maps
store despecialized records; memory maps place the key and value using the
allocation-time width, including when a string key itself calls realloc.
At a reached collection cursor, the canonical width read and the checked dry
run lead to the same realloc request. The saved checked continuation revalidates
claims in the store and writer reached after the callback. A typed refusal there
does not enter the element or descriptor programs; an invalid returned range
traps before the live recheck. These are collection rules for the recursive
comparison, not a correspondence for the complete public export sequence.
The linked-prefix rule discharges the install certificates for the allocator
protocol and callouts resolving to either public give binding, including closed
window reentry. Only other reached installs need a separate certificate. At a
return, the same memory address supplies the checked width and an existing
region still fits; the returned pointer still has to pass alignment and range
validation. None of these rules frames guest bytes or assumes a callback returns.
The canonical record/tuple layout also bounds each aligned field placement
inside the aggregate. With an already-valid aggregate region, the checked
nested-field bounds read succeeds at that placement after a certified prefix.

`RecordDestination.paired_dynamic_call` reaches the same linked realloc
program on both sides, with the two actual continuation programs on the
stack, even with different writers after earlier transfers.
`Machine.HostFrame.paired_steps` replays the actual scheduler through blocked
activations up to a host read that changes the continuation or the return to
the substituted frame. The synchronous lift loop agrees on its residual
program when its blocked threads' reached readiness queries agree, including
constant readiness policies. A closed same-instance reentrant public give
rejoins the paired scheduler after journaling the typed refusal on each side;
its Core reply does not depend on either writer or ticket. Open/raw host
reads need not agree. A prefix that traps or has not returned does not need an
allocator result. After a common return the two continuations check the same
reached range, and the checked one revalidates its own reached live plan before
entering any element. This pairs allocator prefixes, not the subsequent
recursive traversals or the complete exports.

`RecordDestination.compare_handle_leaf` pairs the actual canonical memory and
flat programs for own, stream, future, and error-context leaves. On live-check
refusal it stops the canonical side before the leaf. On admission both sides
reach the same value or canonical trap and the same component store from the
shared cursor, even with different writers and sequence continuations. A late
trap retains canonical table and memory effects and the checked side's spend.

`PayloadPrefix.flat_field` composes those steps through nested records,
tuples, fixed lists and sums with handle-only leaves. Only a common return
advances the sequence; typed refusal stops at an actual reference prefix,
and canonical failure keeps the same trap and reached component store.
`flat_sum` continues from the selected arm to the actual slot coercions
and padding on both sides, matching any canonical choices made on the paired
runs. `parked_giveFlat` uses the compiler's layout certificate to discharge
selected-tag bounds throughout this fragment. It starts at the linked Core
call and reaches the original reply continuation for a returned verdict.
It compares against `lowerFlatAt` on the selected value and schema; it does
not cover allocating children or export delivery.

`PayloadPrefix.parked_givePayload` pairs the linked indirect route with
`Canon.store` for handle leaves and sums with no active payload or a single
active handle leaf. The destination check supplies the width for the actual
canonical discriminant write and child placement. Both runs retain that write
if the live child check refuses or if a later store traps. Typed preflight
and live refusals remain separate from alignment and bounds traps at root
placement: raw `store` assumes valid placement, so the checked route can trap
before the canonical program starts. This fragment does not yet cover nested
memory aggregates or allocator callbacks.

`RecordDestination.memory_cursor` uses the width established by the same destination
check as both public give routes. On a certified prefix the canonical field cursor
takes its actual width-read step and selects the same aligned address and increment
as the compiled sequence. For dynamic lists and maps, `listRange_call` identifies the
real realloc request and the saved continuation. `RecordDestination.listRange_resume`
uses the store reached by a returning allocator: it traps on an invalid alignment or
range without resuming the emitter, or proceeds to claim revalidation in that store.
Neither the cursor nor the allocator-return rule assumes byte preservation, an
allocator return on every trace, or success of the subsequent transfer.

`PayloadPrefix.collection_install` applies that width certificate to the
actual recursive collection programs. After the initial plan check succeeds,
the two machines install the same realloc request with separately saved
continuations. `collection_return` composes an actual paired return with
range validation, the fresh checked plan verdict, element traversal, and the
canonical list descriptor. A refused recheck leaves the reference before
the elements, and a later descriptor trap retains preceding writes. The
rules cover value-mode entries (dynamic lists and flat-map entries); the
memory-map placement mode and the synthesis of paired reentrant runs for
arbitrary nested public outputs remain separate obligations.

`LinkedCallback.Prefix.syncLift` includes the reached synchronous choice
or no-candidate trap in the classified callback replay. Only the host
predicates queried for blocked threads in that instance need to be independent
of the writer; this is automatic for a writer-independent readiness policy.
`Prefix.collection_return` composes the replay (including closed give reentry)
with the reached allocation range and fresh live claim verdict before running
the child comparisons. A pop of an unchanged frame instead leaves the pair
aligned. `Prefix.collection` derives the allocator entry and saved frames
directly from the actual checked and canonical dynamic collection programs;
only the checked run supplies the classified callback path. These rules do
not compare arbitrary host reads or prove that the allocator returns.

`LinkedCallback.PublicCollection.Site.parked` connects the compiled collection
root to both public give calls. At the parked Core activation it follows the
actual dry run, ABI fit, and root placement. Typed refusal reaches the original
reply program; invalid indirect placement traps before allocation. Otherwise
both allocators are installed. `Site.TailRule` receives the actual reached
width, size, alignment, bounds, and successful live-plan verdict; the tail
comparison is used only after these checks pass. `Site.parked_handles` supplies
that rule for a dynamic list of
handle leaves. This does not prove nested allocating children, memory-map
placement, or delivery of the reply.

`PayloadPrefix.primitive_leaf` pairs non-string scalar effects after the
checked width and placement reads. `primitive_list_entry` gets those facts
from a validated list range and a growth-certified prefix, not from a claim
that guest memory bytes stay unchanged. `CollectionTailAt.scalar_entries`
carries Core growth through completed scalar writes to derive placement at
each next cursor, and compares the actual final descriptor. `Site.parked_scalars`
derives the entry shape from compilation in both public give routes, so no
separate child comparison is needed after a classified allocator return for
these lists. This does not cover string elements, nested allocating children,
or unclassified open callbacks.

`closed_memory_aggregate` uses the compiled record or tuple layout to compare
the actual checked bounds read and canonical field cursor for handles and
non-string scalar leaves. Completed transfers and scalar writes keep the linked
memory's width and bounds for the next field; a refusal or trap does not run
the suffix. `parked_givePayload_closed` applies this fragment to the public
indirect binding and retains its original reply continuation. The rule does not
yet compose nested allocating fields or claim reply delivery.

`MemoryChildRule.aggregate` composes reached memory children in a record or
tuple using its compiled layout. `CollectionTailAt.memory_entries` uses the
same child interface for a validated array, deriving the alignment and bounds
of each reached entry. `Site.parked_local_entries` discharges the resulting
tail for lists of arbitrarily nested local records and tuples, on both public
give bindings, and for flat maps in value-entry mode. Its fragment has
non-string scalar and handle leaves. The outer allocator path still uses the
linked callback classification; allocators within entries and indirect map
placement are not covered. Growth preserves the usable bounds, not the bytes.

`Prefix.collection_memory` carries that growth evidence across an actual
dynamic child's allocator install, classified callback, and saved return.
On success its certificate covers the enclosing prefix, the callback, the
entry writes/transfers and the descriptor at the reached store. The
post-return range and live claim checks still run before the child rules.
A common-frame pop stays paired without claiming a return; typed refusal
and canonical trap stop the suffix. This is a rule for a classified reached
path, not a proof that realloc returns or a classification of all nested paths.

`PayloadRoot.Site.parked` shares admission, claim preparation, fit and root
placement across both linked give bindings. `NestedRecord.parked_givePayload`
uses that cut and the compiler's layout to enter a record or tuple whose first
field is an allocating list. It executes the aggregate's checked bounds read
and keeps its nested issue mapping. It compares finite classified allocator
prefixes and advances the real sibling cursor only after a common return and
live recheck. The list entries and later fields use the recursive local-memory
fragment; arbitrary allocating descendants and reply delivery remain separate.

`MemorySequence.parked_givePayload` covers arbitrary record and tuple nesting
with interleaved allocating strings and checked handles. The actual public
fit and placement guards supply the root certificate. Each child placement
comes from the compiled layout, and the induction advances siblings only at
the paired success continuation. String callbacks may mutate memory; each
later handle guard rechecks the reached writer. The comparison retains older
saved frames and finite classified allocator prefixes. This fragment does
not yet cover allocating collection descendants, sums, or reply delivery.

`MemorySequence.value_entries_replay` extends the marked allocator replay
through the reached value-mode collection range, deriving the strided slots
from the entry layouts. Each entry can contain nested records and tuples with
allocating strings and checked handles. After a common success it runs the
actual pointer/count descriptor; a trap on the second write keeps the first.
Range traps and typed refusals run no entries. The rule applies to lists and
flat maps in value-entry mode, not the allocation-time layout of indirect maps.
`MemorySequence.parked_list` applies it to the actual list root on both
public give bindings. The linked destination and public admission supply
the initial memory and live plan without assuming either is unchanged at
the later return. On common success the descriptor reaches the original
continuation; no delivery claim follows.

`Record.Effects.emitValue_eq` gives one recursive checked effect view for both
ABIs. It composes the live handle checks and commitment-time spends with the
canonical leaf programs, then traverses the placed record/tuple fields, list and
map entries, and selected sum arm in order. A dynamic collection validates the
reached range and rechecks the live plan before traversing any entry. The
equality is of effect programs, so it also covers a typed refusal after a
completed prefix or a canonical trap with earlier writes and spends intact.
`GiveEffectRoute.parked` enters that same program from either linked Core give
binding with the original continuation and ticket. `compiled_payload_effects`
identifies its compiled value, layout and ordered receipts after admission.
This is a checked view, not an erasure of guards to unchecked `Canon.store`
or `lowerFlatAt`, and does not prove whole-session event delivery.

`CanonicalTree.field_reference` identifies the recursive reference-side
program with `Canon.store` or `lowerFlatAt` on the certified value and type.
It is equality of programs, including allocator calls, their continuations,
range traps, and descriptor writes at arbitrary nesting depth. In particular,
the flat map uses reached record cursor reads, while the memory map places
both cells using the allocation-time width, even if its key calls realloc.
This factors the canonical comparator; it does not discharge the checked
emitter's live guards or equate its typed refusals with canonical traps.
The `compiled_payload_reference` lemma instantiates it on either public give's
compiled field. At a reached collection return, `linked_dynamic_refusal`
distinguishes the real alignment/range trap from a stopped typed prefix:
valid range plus a failed live plan reaches the diagnostic continuation with
the entire reached state, before any element or descriptor write.
`checked_leaf_prefix` gives the scheduler transition from a reached owner,
endpoint or error-context check to the reference leaf on either output. It
either stops with a typed error or runs the reference leaf after just the
required claim spend; shared contexts spend nothing. The lemma does not
deduce that a later canonical leaf succeeds.

`ChildFrameOver.string_field_replay` compares both actual string field programs
through their allocate/resize plans and memory descriptor or flat result. It
replays classified finite callback prefixes; a returning callback advances the
comparison only when it pops the installed occurrence. Older paired frames stay
paired, and induction resumes on the strictly shorter saved plan. Descriptor
writes use the reached state and may trap after an earlier write. The string
rule takes the reached width, placement and fit facts; it does not require
callbacks to return, preserve guest bytes or preserve live claims. Composition
through arbitrary allocating compounds and both public give bindings is separate.

`ChildFrameOver.collection_replay` applies the same occurrence tracking to
the allocating list and map programs. A finite callback prefix can end
without a return. Both replays certify every edit of the mark, even when
overwriting or trapping removes it. At the installed return the comparison
retires just that frame and
checks the pointer against the reached memory; only a valid range reads the
live plan. An invalid range traps with the callback effects intact. A failed
live check leaves the canonical program before traversal, while the checked
continuation receives a typed refusal. The saved map mode still distinguishes
memory placement at allocation width from reached flat-entry cursor reads.
The cut does not assume or prove equivalence of the subsequent children.

`MemorySequence.parked_list_tree` supplies the recursive placed-child comparison
for an indirect payload, including mixed scalar, string and handle leaves, fixed
arrays, aggregates, active sums, lists and indirect maps. The flat counterpart,
`MemorySequence.parked_recursive_flat`, traverses records, tuples, fixed arrays
and sums, and enters the placed-child comparison at each reached list or map
allocator return. The compiler and public admission supply tag bounds, entry
layouts and string fit within the structural fragment. For a present sum arm,
the actual coercion and padding run on the arm's words only after common success;
an empty arm runs that tail directly. A typed refusal never runs the coercion or
the following sibling. Canonical traps retain earlier effects. Both comparisons
retain finite suspension and the reached callback classification and readiness
conditions; neither asserts whole-export delivery or allocator liveness.

`MemorySequence.parked_compiled_memory` and `parked_compiled_flat` obtain the
active recursive shape from the same successful preflight used by the linked
binding. In a map, the compiler proves that each entry contains its checked
primitive key and recursively compiled value; this does not follow from layout
alone. Neither public theorem takes per-child shape assumptions or a depth
bound. Primitive data, enums, flags and checked handles use the reached local
rules, while strings use their actual allocation plans. The compiler's schema
checks provide the enum and flags evidence, not a separate leaf assumption.
The linked preflight also supplies the allocator option at each allocating
descendant. Pointer-free schemas need no realloc option for either comparison;
pointer-bearing schemas still require it before execution, including inactive
arms and empty containers. This does not establish callback readiness or return.

At a successful reached reply with the original Core frame on top,
`resume_returned_give` runs both machines' Core resume steps with the same
ABI words and reached store. Only the checked machine records completion.
`Site.reached_caller` identifies that frame from a finite occurrence trail,
not from equality of continuation values. `Prefix.under` follows older slots
through the same active or suspended activation as a surviving mark.
`string_return_tracks` constructs the older-slot prefix through an actual
string allocation or resize, using the marked callback and its designated pop.
`CollectionReplayFor` also tracks older slots through the actual checked
preflight reads and the reference width read into each collection allocator.
`Trail.through_return` composes such an install with the marked run and its
actual pop; a surviving suspended mark instead carries older slots by
`Prefix.under`. Loss of the mark does not identify a surviving occurrence.
`parked_memory_rejoined` and `parked_flat_rejoined` thread the older-slot paths
through the entire compiler-derived body: record/tuple and array siblings,
selected sum arms, nested list entries, and allocation-time indirect map
placement. A successful return uses the composed path from the parked give to
resume the original Core caller with the same ABI words and reached store.
The traversal retains finite suspended callback paths and executes range and
live-claim checks at the reached return. Typed stops do not run later siblings;
canonical traps keep the reached effects. Callback classification and readiness
still apply, and Core resumption does not prove async event delivery.
`Site.refusal_resumes` extends a
reached preflight refusal on the checked side only. These local completion
rules do not imply that a suspended callback returns or an async event is
delivered.

The checked recursive emitter supplies the store-invariant certificate for both
public payload bindings. Its proof follows the actual canonical data writes, owner
and endpoint commitment operations, selected sum arm, and collection allocation,
revalidation and descriptor writes. A reached parked `givePayload` or `giveFlat`
callout with the matching binding therefore supplies a scheduler installation
certificate, even when it refuses or traps. Together with the allocator dispatcher
certificates this covers those installs, not arbitrary host code. The invariant
frames memory width and allocated bounds; it is not an effect equivalence or a
claim that a late refusal undoes the prefix.

`Binding.acceptFlat` links a fixed tag and checks the full schema before accepting the
canonical flat operand vector. The child pointer/count and any indirect string or list
contents still refer to the linked memory; the child checks are shared with the indirect
binding. A refused preflight leaves the component store unchanged. The machine-step
theorem for a refused scheduled load records its typed diagnostic, returns `(1, 0)`,
does not publish a tree, and retains the store returned by the loader, including effects
before a later canonical load failure. The Core replay tries an incompatible memory
width and wrong child arity, retries with the same two owners and stream, and hands them
back as a flat result. Stored borrows and asynchronous calling conventions remain typed
errors here; a synchronous call may still carry stream and future endpoints. The older
`MemSound.WitAst` contract still rejects flat inputs. This checked route does not prove
the full component calling convention or exact accepted payload languages across exports.

The scheduled `accept_success_steps` lemma connects both checked loaders' successful
outcomes to a Core reply for the same handle and writer state. `register_claims` identifies
the single published root and its new owner and endpoint claims. The separate
`accept_registration_refusal_steps` lemma covers a successful lift followed by an alias
refusal: there is no publication, the diagnostic is journaled, and prior canonical load
effects are retained. Together with `accept_refusal_steps` these cover all outcomes once
the dispatcher reaches the synchronous accept continuation. They are per-invocation
reduction lemmas, not an exact guest language theorem.

The parked public give rules reach the checked lowering program for the selected
root with the original Core continuation and ticket. The compiled-start rule
identifies its canonical value, recursive layout and ordered nominal receipts,
then steps the initial live dry run and checked width read. A returned result
journals and resumes Core with the reached store; a canonical trap does not
enter this reply continuation. After a valid collection allocation return,
`listRange_recheck` steps the actual claim read against the reached store and
writer. It does not restore pre-allocation claims or assume allocator liveness.
These are boundaries of the recursive execution proof, not yet a correspondence
for the entire body or for a sequence of scheduled exports.

The scheduled flat replay connects a writer and a reader in separate component
instances through actual Core exports. It runs with either a stream or a future of a
record containing an owner. The writer publishes a tree with two distinct
equal-representation owners and a readable endpoint, and the reader receives all
three claims via `giveFlat`. It cancels a blocked read without writing memory, retries,
polls the channel's completion event, and checks the transferred record and owner.
The stream case observes writer closure on a subsequent read. For both channels, a
stale read after drop traps without removing the published tree. The async operations
here are reference built-ins, not async accept calls.

The scheduled journal distinguishes publication from a Core reply. A `published`
entry records the import ticket and handle in the same host write that adds the root
and its claims. Across arbitrary ordinary machine prefixes, `checked_of_session`
proves that the publication journal only grows and that its growth equals the growth
of accepted roots. Each journal entry carries the one-based position of its root,
as a nonzero, non-wrapping Core `i32` handle. A refusal or a trap without publication
cannot count as an acceptance, and a prefix ending between publication and the reply
still records the root. `PublicationDelta.targets` proves that each journaled handle
selects its root from the final writer; `WriterRun.retains_target` extends this to older
handles without reviving spent resource or endpoint claims. Both loaders check capacity
before lifting, and the publication continuation independently refuses to wrap.
This conservation statement does not characterize which roots a given module can accept.

`import_binding_trap_steps` covers mislinked imports from the public dispatcher,
not only its trap continuation. It records the entry and the typed missing, ambiguous
or mismatched-binding diagnostic before taking the reference trap transition. No
loader or claim transfer runs. Core replays verify that the rejected call publishes
nothing and an owner allocated by an earlier export stays in the resource table.

The canonical caller-start receipt observer uses the same `canon lower` start callback
and argument cursor as the reference, including the single-pointer spill path. Erasing
owner receipts yields the entire reference start program, including its effects and
failures, rather than just equal returned values. Reference machine replays check direct
and spilled arguments, an indirect async result, equal representations with different
owner identities, and cancellation before and after start. The observer alone is not a
checked storage boundary.

Install `ComponentCall.hostWithComponent` to join that observer to the public scheduled
writer through actual `canon lower` Core imports. The status-pair dispatcher `host`
does not enable these component callees. A linked callee checks the caller's instance,
memory width, options, signature, whole storable payload schema and child selection. It
resolves a typed WIT `result<u32>` error before lifting owners on preflight refusal.
`ComponentCall.refusal_frame` preserves the instance handle tables, owners, endpoints
and error contexts, including if the error write traps. Guest result bytes and subtask
bookkeeping may change. `ComponentCall.resolve_error_agrees` proves that, given the
same guarded caller record, result resolution has the reference continuation, including
its write and possible traps. It does not equate refusal without a payload lift with a
canonical trap during a lift.
Once lifting starts, canonical traps retain prior reference effects; e.g., a second use
of the same slot traps after the first move. Indirect result writes must finish before
publishing, and publication checks the candidate handle against the live writer.
`ComponentCall.resolve_begin` places the reference result program before the commit.
At the commit continuation, `complete_commit` preserves the reached store and publishes
before recording a reply. `complete_stale` instead records `.wrongResultType` and locks
down without publishing or recording a reply. `resolve_caller` exposes the live reference
result cursor. `resolve_progress` executes the reached subtask's index check before canonical
result lowering: an indexed subtask queues or replaces its pending event; an unindexed one
leaves the slot unchanged. This neither resolves the subtask nor delivers the event.
`lower_result_program` gives the exact canonical program at this cursor in
both memory widths: pointer type, alignment and whole-result range checks precede the writes;
an error only writes its tag, and a successful reply also writes the little-endian handle at
offset four. `resolve_indirect_write` executes both writes in the reached Core store,
derives their success from the full range check, and retains the queued subtask record.
Bad alignment or an insufficient range takes the actual canonical trap before either
write. `resolve_direct_words` reaches subtask resolution with the two ABI words and no
store update. `resolve_commit` connects the post-write subtask resolution to publication
without clearing the pending event or releasing lends. `resolve_linked_commit` composes
these steps from the linked resolve entry: both linked modes spill this result, and
queueing preserves the memory observed at entry. An indexed subtask retains the newly
queued event after resolution; an unindexed one keeps its original slot.
`deliver_pending` takes the actual returned event and applies reference lend release in a
later waitable step. `poll_delivers_returned` derives readiness from a reached member's
pending slot and executes the selected shuffle before consuming that event. The partial trace
includes the actual shuffle label and its persisted order. `unpack_event_write` executes
both event words on a valid buffer. On a late out-of-bounds buffer, `poll_returned_bad_range`
locks down after consumption and lend release without writing either word or changing the
reached host. These rules start at the reached poll body; they do not prove public builtin
admission, wait/cancel sequencing, or that publication guarantees a guest polls.
The linked replays cover a misaligned result pointer, and a late out-of-bounds poll write
that traps after consuming the event while preserving the earlier publication.
`ComponentCall.checked_of_session` gives publication, writer and transcript conservation
across every ordinary machine prefix, including traps and refusals. It does not assert
an exact language for every guest or atomic rollback of reference operations.

Linked Core replays check sync and async direct and spilled calls, refusal and retry,
inactive nested borrow rejection, bad memory width, recycled owner slots, a double-move
trap and a result range trap. In the joined channel replay the async canonical accept
publishes a root with owners and a readable endpoint; another linked instance receives
it via `giveFlat` and exercises a non-unit resource-bearing stream or future, including
read cancellation, polling, closure (stream) and stale handles.

`ComponentCall.Deferred.hostWithDeferred` adds a pending mode for explicitly configured
asynchronous callees. Queuing validates the link and the full schema without lifting
the arguments. The reference `canon lower` installs a waitable; the linked start import
selects its live nominal subtask in the caller's instance, checks the saved caller
record, and invokes the same checked acceptance and publication as the eager route.
The start import acknowledges the callback; the accepted handle or typed WIT error is
written into the original caller's canonical result area. Starting in the wrong
instance, behind a no-leave boundary, or from a stale slot fails with a typed diagnostic.
Before start, `subtask.cancel` calls the checked cancellation callback and resolves via
the reference cancellation path, without moving owners or publishing a tree. Start
lifts and resolves in one callback; it does not expose a suspended post-lift phase.
The deferred session theorem conserves the writer and journal on arbitrary ordinary
prefixes. `Deferred.fresh_lookup_iff_publication` also proves the converse to publication
lookup: a fresh handle is selectable exactly when its journal position records a
publication for it. `Deferred.fresh_lookup_iff_cut` relates the selected tree itself to
a single machine step registering it and appending the matching journal entry. The
actual prefix and suffix retain intervening traps, retries and other effects. A pending
or refused callback cannot account for a new selectable root without a publication.
This is not a statement about delivery or live transfer authority. Linked
direct/spilled replays check cancel, drop, slot reuse, start,
resolution, and stale start after dropping the waitable.
With no configured deferred callees, the complete dispatch is the eager dispatch;
the control name is not reserved. When a live instance has no room for a waitable,
staging records `subtaskTableFull` under the original call ticket without lifting,
queuing or publishing, then returns to canonical lowering for the reference `tableFull` trap.

For a new owner prepared after an ordinary checked export prefix,
`ComponentCall.Deferred.prepared_owner_publication` locates the committed ticket and
Core handle of the root carrying the exact typed receipt. The lookup remains valid
after spending the claim; it observes the receipt without recreating authority.
The deferred replay checks that the successful retry publishes both distinct owners
with the same representation, while the cancelled call has no publication.

`ComponentCall.Deferred.publication_roots` reconstructs the exact chronological list of
new roots from the journal suffix, even for a prefix ending mid-call. Each new entry
selects its root, with no missing or extra occurrence. Direct and spilled Core replays
check ordering across refusal and success, and the deferred replay checks cancellation
and stale start. This reconstructs committed acceptance, not the set of inputs a guest
will accept or a guarantee that an interrupted caller received its result.

`Delivery.LinkedResolution.then_poll` composes the reached indexed result commit
with an actual scheduled prefix and a selected parked Core poll of the same
subtask arena object. The intervening steps must keep the returned event pending;
a final lookup cannot substitute for that prefix. Moving the waitable between
sets preserves the pending event. The poll clears it and releases lends even if
the later output-buffer check traps.

`Delivery.PollAdmission.retains_until_unpack` derives the intervening frame for an
admitted Core poll with no event, or with a reached selection and successful take
from a different subtask, stream, or future. The poll's shuffle and take preserve
the tracked subtask's pending return and the same saved activation at each cut.
`retains_through_reply` extends that path through the checked buffer writes and
reply to the original Core caller or the alignment/range trap. The range check
uses the reached store; a trap retains the other delivery. These are classified
poll paths, not every possible scheduler step.

`Delivery.ParkedWait.then_resolution` starts at an actual Core wait callout with
no event available. It registers the waiter and saves the Core continuation;
after the indexed commit and a retaining prefix, the selected host tick restores
that continuation, decrements the wait count and runs the same canonical event
selection as poll. A valid buffer returns the event code to Core. An invalid
buffer traps after event consumption and lend release. The theorem derives the
exact saved activation at the tick from scheduler edits along the intervening
execution, including the actual result commit. A later equal frame does not
substitute for the original after a resume or overwrite. Tick choice and event
selection remain explicit; the theorem gives neither scheduler liveness nor a
correspondence for arbitrary export sequences.

When the set is already ready, `Delivery.ParkedWait.ready_choice` follows the
profile's reached early-return choice. The non-early branch still installs the
saved wait. `delivers_early` uses the same selection and result-buffer proof as
the resumed wait, but requires no block or tick; a late buffer trap still follows
event consumption and lend release.

`Delivery.WaitResume` separates the reached canonical resume from the policy
that selected it; the selected tick uses the same resume proof. The reached
resume restores the tracked saved activation and updates the wait count without
consulting readiness. `traps_empty` shows that a forced resume of a live set
with no pending event still shuffles before trapping, unlike an empty poll.
`delivers_returned` handles a selected pending return after a retaining prefix.
These theorems do not infer that any particular call will force the resume.

Before resolution, `Delivery.ParkedCancel.requests` derives the live request
and temporary sync waiter before the actual cancellation callback starts. The
closed asynchronous case in `StartedCancel.resumes_blocked` executes a started
guest task's callback with a noncancellable implicit thread: it marks the task
pending cancel, clears the temporary waiter and returns `BLOCKED` to the same
Core caller. This path neither resolves nor delivers the subtask. It does not
classify an initial or immediately resumed callee, a synchronous wait, or an
open host cancellation hook.

For a ready, cancellable started guest, `Delivery.CallbackWait` derives both
saved callback-loop continuations from the canonical YIELD (K2) and WAIT (K3)
branches. The K3 waiter count is decremented on resumption, before the reached
pending-cancellation check. Cancellation takes priority over the selected set's
events: these steps do not consume an event or release lends.
`TaskCancelAdmission.started_calls_core` splices the tracked saved occurrence
into the actual cancellation callout, retakes the callback lock and invokes the
Core callback with `TASK_CANCELLED`, keeping the original Core caller parked.
This prefix requires readiness in the reached post-mark store and does not
assert that the callback returns, resolves the subtask or delivers its reply.

At a reached Core outcome, `CallbackWait.core_trapped` and `core_returned`
distinguish a Core trap, a malformed callback result and a valid next loop
code. `core_reparks` reads the reached task and handle table and installs the
next K2/K3 continuation on a non-early park. `exit_unresolved` traps if EXIT
would discard the last thread of an unresolved task. `exit_resolved` follows
the live registration and lock release, and `unwind_callback` pops the loop's
identity continuations back to the resumer. Returning to that resumer is not
the same as consuming the subtask event or replying to the original caller.

When the callback reaches a canonical `task.cancel` import, the reached
instance, asynchronous option and delivered cancellation are checked before
resolution. `CallbackCancelImport.enters_resolution` separates the live-borrow
trap from entry into `onResolve(none)`. For an indexed started subtask,
`resolves_started` follows the actual lower caller and resumes the Core
callback with the empty import result. The `CANCELLED_BEFORE_RETURNED` event
is pending and its lenders are still attached, not delivered by the import.

`CallbackWait.core_only_cut` derives the component frame of every finite
host-free Core suffix from the machine steps; it leaves the reached Core store
unconstrained. If that suffix returns EXIT, `CallbackCancelImport.delivers_started`
uses the pre-import registration and reached return to unregister the callback,
pop its identity frames and retain the indexed cancellation event until the
original caller consumes it, releases the lends and gets its Core result. An
unfinished prefix is not delivery; intervening callouts and wait iterations
are outside this suffix theorem.

For ready K2/K3, `CallbackWait.takes_early` follows the permitted early
choice to the same suffix used by resumption, without blocking. The no-cancel
suffixes then pass NONE at K2 or take a reached selected event at K3. K3
decrements the waiter count before the shuffle and takes the event before
retaking the lock and calling Core. The selected event and Core callback return
are separate observations.

`CallbackWait.early_yield_retains` and `early_wait_retains_other` compose the
early choice with the reached Core invocation and preserve the exact tracked
subtask record, not just its resolution code. In K3 this requires selection
of a different arena waitable; the waiter decrement, shuffle and selected
event take still occur. In particular a pending cancellation and its lends
are not consumed by either path. When K3 selects the tracked resolution itself,
`wait_takes_resolution` instead derives the event passed to Core and the cleared
pending event and lender list from the actual take. That is not a reply to the
outer cancellation caller.

`ClosedCallbackPrefix.reaches` composes any finite chain of host-free Core
steps, reached callback returns entering a new K2/K3 loop, and K2 NONE or
other-waitable K3 calls. The early and parked paths share the same suffix.
Non-early park, a reached forced resume, and an actual ready-thread tick
can be included in the prefix; none changes the tracked record. The tick
must select the reached thread, and `CallbackWait.resumes_on_tick` tracks
its original saved occurrence through an intervening parked prefix. The
finite-prefix proof does not assume preservation of Core bytes, eventual
scheduler selection, callback return or outer delivery.

On a reached EXIT, `CallbackCancelImport.delivers_after_closed_prefix`
rechecks the live registration at that cut and unwinds the intervening loop
frames. The exact cancelled record survives until the original Core caller's
separate delivery steps take it, release its lends, and return its status.

`CallbackResume.resumes_tracked` follows the original K2/K3 saved occurrence
through a retaining prefix and a reached forced `Thread.resume`. It restores
the exact suffix above the resumer without a readiness assumption. On a live
empty K3 set with no pending cancellation, `traps_empty` retains the waiter
decrement and shuffle but never reaches the Core callback.

If the caller instead reaches `subtask.cancel` after the return, with a live,
undelivered subtask that has not received a cancel request or joined a set,
`Delivery.LinkedResolution.then_cancel` uses the canonical direct-delivery
branch. It consumes the existing event, releases lends and returns the already
resolved state, without an event buffer or cancellation callback. It does not
cover cancellation requests that precede resolution.

For a resumed worker's first string argument, `CalleeArguments.direct_string_pair`
and `CalleeSpillReturn.spilled_string_pair` execute the canonical string plan on
both session dispatchers. The local interpreter stops at the next allocator
request, and only a return from the marked occurrence advances to the shorter
residual plan. A finite callback may stay suspended or trap. A successful
string passes the flat words or reaches the spill tuple suffix after writing
its descriptor. These cuts classify only the reached callback prefix; they
do not assume that it returns or preserves memory.

`direct_arguments` and `spilled_arguments` iterate those cuts across a
parameter list mixing bool, u32, and strings through arbitrarily nested
tuples, named records, options, dynamic lists, and maps. Direct scalars add their
canonical flat word; spilled scalars do a live width read and bounds-checked
write. The next field uses the reached cursor; in the spill path it starts at
the previous field's ABI end offset. Canonical tuple and record programs
share the field traversal without a premise about individual children. In
memory, a canonical option reads the live ABI width for placement and writes
its discriminant before traversing the selected payload. A later trap or suspension retains
that reached write and any allocator effects. Flat options run the canonical
slot adjustment only after the payload completes. An absent option never
executes its payload; its shape still determines padding and layout. The
string-only theorems specialize the same traversal.
`enter_stackful_after_strings` starts actual Core execution with the computed
flat words or the outer spill pointer when lowering completes. A suspension
or trap does not enter Core. `collection_range_pair` uses the same installed
allocator occurrence for the canonical dynamic list/map range request. At a
selected return it checks alignment and reads the reached memory size; it
neither assumes the callback returns nor restores memory on a later trap.
The list proof continues that cut through the canonical indexed element
stores with allocation-time stride, including recursively allocating elements.
Its structural argument evidence checks the element schema even for an empty
list and does not assert any child execution agreement. Once all elements
finish, the direct path passes the pointer/count operands. The spilled path
reads the reached pointer width and writes the real pointer followed by the
count; a trap on the second write retains the first. Maps share the indexed
loop and descriptor cut. Direct map elements use the actual canonical
record stores. Indirect map elements instead place the key and value using
the allocation-time layout, even when a string key allocates before the
value is written. Map keys in this fragment are bool, u32, or string; an
empty map still supplies both shapes. Variants and results now traverse their
selected, possibly allocating payload in the same induction. Inactive arms
contribute their actual schemas to the layout and joined flat slots but
do not execute. The memory tag is written before the payload can suspend
or trap. The flat path runs canonical coercion (including admissible NaN
choices) and padding only after the payload completes. This is a paired
canonical worker path, not checked schema admission or a proof of agreement
between distinct checked and canonical states. A direct owner-head read
follows the actual caller operand and `Resources.take`, retaining the
nominal identity on success and the slot removal on a later lift trap.
Already reached canonical values can include owner descendants anywhere in
the traversal: the actual handle arena insertion and flat slot or memory
write run against the reached store. A later failure retains earlier
effects. The structural witness does not itself grant transfer permission;
recursive source provenance across the whole argument lift remains separate.
This worker proof does not classify arbitrary component host reentry.

`finish_stackful_after_arguments` continues the reached Core entry along a
selected finite body. Guest-only paths classify without a host premise;
closed paths check the reached dispatch sites, while open paths need site-level
classification. A finite prefix can stop without returning. At an observed
return, the live task decides the unresolved-last-thread trap before any
registration lookup. A valid reached registration takes canonical
unregistration and worker exit, exposing exactly the reached scheduler tail.
The proof does not preserve pre-body records. `finish_stackful_with_delivery`
then composes the reached cut with a finite closed delivery tail. Each poll,
wait, or cancel edge uses the record or event reached at that step, including
consumption followed by an event-buffer trap. This transport does not equate
different open cancellation continuations or compare the full public-give
session.

`Run.give_then_delivery` bridges a successfully compared public give body
to a finite tail across different host journals. The two real reply paths
rejoin the active and blocked activations and the reached store, pending
calls, results and cancellation records. The checked reply records its
completion; the canonical reply does not. The proof then transports the
actual Core, poll, wait (including park and resume), and closed cancel
delivery edges. It derives their journal independence from the edge
constructors. Each take uses its reached event and retains consumption
when a subsequent buffer write traps. This tail does not include another
give, event publication, open cancel requests or readiness-sensitive tick
selection. Typed stopped prefixes still have no canonical reply.

`LiveDispatch.NestedPlan` also composes publication and poll with nested
public gives, including while older allocator continuations are paired.
Publication rechecks registration against the reached journal and compares
the actual emitted handle; a failed comparison stops before that transition,
not at an invented trap. A poll uses the event selected from the reached
store. On an unaligned or out-of-range buffer it consumes the event and
locks down the delivered store without resuming the caller. On success it
writes the event words and rejoins Core with the older frames still paired.
At a wait's actual selection, the same comparison consumes the reached
event and either rejoins the saved Core caller or keeps the delivered store
on a trap. Cancel of an already returned event also uses the reached record
and consumes the event without invoking a cancel callback. These classified
finite edges do not compare wait parking and resumption or open cancellation
requests, and do not imply scheduler progress.

## Checking

```
lake build --wfail Silmaril.Semantics.Accept.Handle.Examples Silmaril.Semantics.Accept.Parse.Examples \
  Silmaril.Formats.SExp.Api.Thms Silmaril.Formats.SExp.Pattern.Examples \
  Silmaril.Formats.SExp.Family.Thms Silmaril.Wasm.Game.HandleAccept.Checkers.Thms \
  Silmaril.Semantics.Accept.Mixed.Chunk.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.Thms \
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take.Examples Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Examples \
  Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Canon \
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Examples \
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Projection \
  Silmaril.Wasm.Game.HandleAccept.MemSound.Exact.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.KwText.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Thms \
  Silmaril.Wasm.Game.HandleAccept.Checkers.RecFull.Thms \
  Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch.Examples Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Thms \
  Silmaril.Wasm.Game.HandleAccept.MemSound.Probe.Thms Silmaril.Wasm.Game.HandleAccept.MemSound.Tab.Thms \
  Silmaril.Wasm.Game.HandleAccept.Families.Matrix Silmaril.Wasm.Game.HandleAccept.Families.Mixed.Examples
scripts/check-layout.sh
```

`make check` builds everything; a library-only build does not run the executable tests.

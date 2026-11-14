# Abstract component semantics: roadmap

This page tracks the abstract model of WebAssembly components: components as
state machines over a game and as trace models, startup, linking, observations
and full abstraction, version comparisons, and the path to HTTP and TCP. Each
requirement maps to the definitions and theorems that address it, their exact
status, and their assumptions. "Proved" means a theorem on `main` with no
`sorry`, built under `--wfail`. "Planned" means nothing is merged yet.

The generic layer lives in the `Games` region under `Silmaril.Games.Abstract`.
Wasm-specific bridges go in the `Wasm` region. HTTP and TCP readings use the
existing `Servers` modules and do not duplicate them.

## Settled conventions

These are conservative choices, recorded so later stages do not reopen them.

1. **Polarity.** `Game.IsO m` means the environment makes the move `m`
   (Opponent). Every other move is the component's (Proponent). For a
   component, Opponent moves are export calls, import answers, stream or future
   events delivered to it, and scheduler choices when scheduling is modelled
   as a move.
2. **Order.** Refinement is inclusion of finite plays: `T ≤ U` means every
   behaviour of `T` is allowed by `U`. Larger means more permissive. `⊤` is
   every legal play ("chaos"), and `⊥` is the component that never moves (only
   Opponent runs).
3. **Closure conditions.** A trace model contains `[]`, is legal,
   prefix-closed and receptive to every legal Opponent move
   (`Game.Closed`). Meets are intersections. Joins are the closure of unions
   (`sSup_eq_generate`); they are plain unions exactly for nonempty families,
   because `sSup ∅ = ⊥` is not empty.
4. **Determinism** means *strategy determinism given the history*: after a
   play, at most one Proponent move can follow (`TraceModel.Det`). Inputs
   remain unconstrained. "Wasm is deterministic" is not asserted. Its sources
   of nondeterminism are handled as follows:
   - host answers and scheduling become Opponent moves, so they do not break
     determinism;
   - NaN bit patterns, relaxed SIMD and `memory.grow` failure are profile
     choices. They are deterministic for a fixed deterministic profile, and
     otherwise either reified as moves or left as genuine nondeterminism;
   - shared-memory threads are not modelled: silmaril's Core 3.0 has no
     threads.

   Finite traces cannot say that a deterministic component *must* move.
5. **Undefined bytes** (planned, stage 4). A partial denotation
   `bytes → WithTop (TraceModel G)` reads `⊤` as "this model makes no claim"
   (unsupported feature, out-of-scope input). That is the most permissive
   point, above chaos. Bytes that fail to decode or validate are **not**
   undefined: they denote a defined behaviour, rejection at startup. The
   down-set reading into `LowerSet (TraceModel G)` (closed subsets of the
   powerset) sends `⊤` to `univ` and therefore identifies "undefined" with
   chaos. That collapse will be proved, with examples, alongside both orders.
6. **Equivalence is not defined as trace equality.** Each program equivalence
   is named after its observation. Agreement with contextual equivalence is a
   theorem with hypotheses (stage 2), never a definition.

## Inventory of existing infrastructure used

| Area | Modules | Role here |
|---|---|---|
| Sequential game `E ↠ F`, strategies, LTS, composition with hiding, category | `Silmaril.Games.{Play,Strategy,LTS,Composition,Category}` | An instance of the abstract game (`sigGame`); strategies are exactly its trace models |
| Instantiation answers, divergence, infinite plays | `Silmaril.Games.{Inst,Div,DivLTS}` | Startup (stage 3), divergence-sensitive observations (stage 2) |
| Wasm scalar game semantics, adequacy, linking as composition, start functions | `Silmaril.Wasm.Game.*` (`ScalarInstance.strategy = Strategy.ofLTS (I.lts P s)`) | Concrete components; the erasure square applies through `strategyIso_ofLTS` (stage 2) |
| NaN, profile and import-oracle determinism | `Silmaril.Wasm.Det.*` | Conditions for `SDet` of Wasm machines (stage 2) |
| Feature lattice and version embeddings | `Silmaril.Wasm.Models.Features` (`v10 ≤ v20 ≤ v30 ≤ wasmFX`, `lime1 ≤ v30`, `lime1 ≰ v20`), `Silmaril.Wasm.Unified.Versions` | Version comparison (stage 8) |
| Component IR, canonical ABI async, streams | `Silmaril.Wasm.Component.{IR,Semantics,Async,Streams}` | Async game (stage 7) |
| wasi:http and server traces | `Silmaril.Servers.{WasiHttp,WasiContext,Core,Observe,Context}` | HTTP reading (stage 10); owned by the Servers work, consumed here |

**Moria audit (hiloopai/moria-lean at `48f528af`).** These are already in
silmaril, with no meaningful difference: `Wasm/FX` (WasmFX, about 10.3k
lines), `Wasm/Versions`, `Lime1ToV1`, `LimeCompile`, `Games` (silmaril is a
superset), `Wasi/Component` and `Wasi/Versions` (P3, `Http3`, sockets), and
the canonical-ABI async modules. "Nucleus" exists in neither repository; no
port is possible until it is located. These are not yet in silmaril and are
queued (stage 6):

- `Semantics/TraceModels`: log monoids, ω-products, partial writer;
- `Semantics/ITree` and `ITreeInterpret`: interaction trees as consistent sets
  of observations, interpreted into Elgot monads;
- `Raw/Semantics/Observational`: observational equivalence as an institution;
- `Sim`: machines with partial views.

**Versions.** WebAssembly 1.0, 2.0 and 3.0 are core specification versions.
`lime1` is the Bytecode Alliance "Lime" feature set (`lime1 ≤ v30` and
`lime1 ≰ v20` are proved). `wasmFX` is the stack-switching extension on top of
3.0. The component model is versioned separately from the core specification.
No "components 1.0" is assumed: component features are `CMFeature` in
`Silmaril.Wasm.Unified.Component.Feat`, and WASI is versioned as P2 and P3.

## Requirements and status

| Requirement | Definitions and theorems | Status |
|---|---|---|
| Generic game; trace sets with closure conditions; complete lattice with correct joins | `Game`, `Game.Closed`, `TraceModel`, `generate`; `generate_le_iff`, `mem_top`, `mem_bot`, `sSup_eq_generate`, `mem_sSup_of_nonempty`, `mem_inf`, `mem_sup` (`Silmaril.Games.Abstract.Game`) | Proved |
| Game maps; pullback and pushforward; functoriality; coarser observational equivalence; hiding | `Game.PHom` (partial morphisms, hiding), `TraceModel.pull`, `hide`, `gc_hide_pull`, `hide_sSup`, `pull_toPHom` (`Silmaril.Games.Abstract.Hiding`); `Game.Hom`, `TraceModel.comap`, `map`; `comap_id`, `comap_comp`, `gc_map_comap`, `comap_sInf`, `obsKer`, `obsKer_le` | Proved. A `Category` instance on games is not yet provided. |
| (a) Components as internal state with interaction transitions, det or nondet | `Machine`, `Run`, `traces`, `denote`, `SDet`, `LDet`, `Bisim` (`Silmaril.Games.Abstract.Machine`) | Defined |
| State erasure; determinism transfers | `SDet.denote_det`, `traces_eq_of_bisim`, `denote_eq_of_bisim`, `coe_denote` | Proved |
| Injectivity on a behavioural quotient | `lDet_bisim_iff_traces`, `lDet_bisim_iff_denote`: erasure is injective on the bisimulation quotient of deterministic, silent-step-free machines | Proved. The case with silent steps (weak bisimulation) is planned. |
| Nondet: trace equality does not determine the machine | `exists_traces_eq_not_bisim` (`a.b + a.c` against `a.(b + c)`) | Proved |
| Generic model agrees with the existing `E ↠ F` strategies; erasure commutes with `Strategy.ofLTS` | `sigGame`, `SigBridge.strategyIso` (order isomorphism), `Machine.ofLTS`, `traces_ofLTS`, `SigBridge.strategyIso_ofLTS`, `strategyIso_sSup`/`sInf` (`Silmaril.Games.Abstract.SigBridge`) | Proved |
| Concrete Wasm instances map to machines and trace models; the square commutes | `Silmaril.Wasm.Abstract.machine`, `strategyIso_strategy`, `machine_tau_free` (`Silmaril.Wasm.Abstract.Instance`) | Proved for scalar Core 3.0 instances |
| Wasm strategy determinism conditional on inputs | `TraceModel.DetUpTo`, `det_iff_detUpTo_false`; `detMod_iff_detUpTo` (the existing `DetMod` is `DetUpTo` of the trap moves); `denote_detUpTo`: a `DetModule` with typed exports denotes a model that is deterministic modulo traps, under every profile | Proved, modulo traps and conditional on `DetModule`. There is no claim of determinism for nondeterministic profiles. |
| Full abstraction: trace equality iff contextual equivalence, with hypotheses; divergence, refusals, counterexamples | `Tests`, `Passes`, `Le`, `Equiv`, `Separates`, `Complete` (`Silmaril.Games.Abstract.Testing`). Proved: `le_of_le` (soundness, no hypothesis); `le_iff_of_complete` and `equiv_iff_of_complete` (full abstraction **under** definability); `single_complete`; `equiv_through_iff` (contexts that observe through a morphism identify equal pullbacks); `Machine.exists_traces_eq_refusal` and `exists_traces_eq_divergence` (equal traces, different refusals, deadlock and divergence) | Generic results proved. Still open: discharging `Complete` for host contexts built with `Games.Composition` in `E ↠ F`, and failures–divergences equivalence. |
| Outcome-tagged traces: trap and divergence distinguished, and the trap ≈ divergence quotient; normal return, still-running prefix, infinite productive run, waiting, deadlock, divergence before and after events | `OMachine` (machine with `Ret`/`Trap` states), `Tag`, `Obs`, `obs`, `collapse`, `cobs`, `TagEquiv`, `CoarseEquiv`, `ObsTests` (`Silmaril.Games.Abstract.Outcome`); `Wasm.Abstract.toTag`, `TagEquiv`, `CoarseEquiv` on call behaviour sets (`Silmaril.Wasm.Abstract.Outcome`). Proved: `fin_run_mem_iff`, `mem_traces_of_fin`, `cobs_mono`, `traces_subset_of_cobs`, `TagEquiv.coarse`, `CoarseEquiv.trace` (tagged ⇒ coarse ⇒ trace); `collapse_eq_iff`, `coarseEquiv_iff` (exactly what the quotient forgets); `may_sound`, `must_sound`, `may_complete`, `mayEquiv_iff_tag`, `mayEquiv_iff_coarse` (contextual equivalence **iff** the contexts are saturated and separating for the chosen observation); examples `exists_coarse_not_tag`, `exists_startup_coarse_not_tag`, `exists_startup_trap_distinct`, `exists_prefix_not_div`, `exists_unfair_div`, `exists_wait_not_div_stuck`. Wasm: `trapDiv_iff`, `tagEquiv_iff` (= `Behaviours.Equiv Eq`), `coarseEquiv_iff` (= `Behaviours.Equiv TrapDiv`), `trap_diverges_coarse_not_tag` | Proved. Divergence is unfair, and fair testing is not modelled. Still open: must-completeness. The instance-level version is the next row. |
| Both trap/divergence notions on Wasm instance traces, where a trap is a move | `Obs.cut T` (cut at the first trap move, tag `abort`), `CutEquiv` (`Silmaril.Games.Abstract.TrapCut`); `omachine I P s` (scalar instance with host-free steps as silent steps), `trapMove I` (`Silmaril.Wasm.Abstract.InstanceOutcome`). Proved: `firstCut_eq_none_iff`, `firstCut_eq_some`, `cut_false` / `cutEquiv_false_iff` (no trap moves: cut = collapse), `TagEquiv.cut`, `exists_cut_not_tag` (trap answer vs silent loop: cut-equivalent, not tag-equivalent); `traces_omachine`, `strategyIso_strategy_omachine` (silent steps change no trace; erasure is still `I.strategy P s`), `div_mem_obs_iff` (`div` = an export call with an infinite host-free run), `tagEquiv_cut` | Proved. Sensitive = `TagEquiv` on `omachine`; trap ≈ divergence = `CutEquiv (trapMove I)`, which drops everything after a trap answer, so it fits only contexts that stop at a trap. Still open: a concrete pair of Core 3.0 modules (trap vs loop) proved by reduction. |
| Abstract functions under module state and environment; observations and quotients; function problems | `AFun E S A B` (call behaviours: import calls with answers, then `ret b s'`, `trap` or `div`), `ObsEquiv κ`, `obsCollapse`, `obsForgetState`, `obsIO`, `seq`, `Det`, `under`, `StatePreserving`, `StateIndependent(On)`, `Pure`, `MayTrap`/`MustTrap`/`MayDiv`/`MustDiv`/`MayAbort`/`MustReturn`, `Callees`, `CallsOn`, `IO`, `outputs`, `trapInputs`, `divInputs`, `detInputs`, `UniquePreimage` (`Silmaril.Games.Abstract.Function`); `wasmFun` (`Silmaril.Wasm.Abstract.Function`). Proved: `ObsEquiv.comp`, `obsEquiv_id_iff`, `seq_obsCollapse` (trap ≈ divergence is a congruence for sequencing), `exists_forgetState_not_congr` (forgetting the final state is not), `Det.under_subsingleton`, `StatePreserving.seq`, `statePreserving_sSup`, `exists_det_sup_not_det` (deterministic functions are not a sublattice), `image_wasmFun` (the projection of Core 3.0 functions agrees with `behaviours`), `obsEquiv_behaviour_iff`, `obsEquiv_trapDiv_iff` (= `Behaviours.Equiv TrapDiv`) | Phase A proved. Host calls of `wasmFun` are internal to `HostSemantics`, and infinite import-call sequences are not represented. Still open: phase B (module shape, lattice, internal-call consistency), C (projection classes, components, congruence of linking), D (versions; block/CFG equivalence interface for the CFG task). |
| Startup-sensitive and startup-erased observations; when they coincide | `Game.phased S G R` (startup in `S`, then `fail r` or `ready` then run in `G`), `Startup.erase` (a partial morphism), `erased`, `startPart`, `StartupIndep` (`Silmaril.Games.Abstract.Startup`). Proved: `eq_iff_startPart_erased`: for startup-independent models, model equality iff equal startup parts and equal erased observations. Counterexamples: `exists_erased_eq_startPart_ne` (erasure forgets failure), `exists_erased_eq_startPart_eq_ne` (erasure forgets dependence on startup inputs; independence is necessary) | Proved. Still open: an instance for `Games.Inst` / `Sig.withInst` and Wasm start functions. |
| Partial map bytes → trace sets; `WithTop` against lower sets; orientation examples | `Denot α G := α → WithTop (TraceModel G)`, `ofPartial`, `toLower`, `realizable` (`Silmaril.Games.Abstract.Denot`). Proved: `ofPartial_le_iff` (`d ≤ e` iff `e` is less defined or larger), `toLower_mono`, `toLower_coe_le_coe_iff`, `toLower_top_eq_coe_top` (lower sets identify undefined with chaos), `coe_top_lt_top` (`WithTop` keeps them apart). Both readings are complete lattices (Mathlib instances). | Proved. Still open: a concrete bytes → phased-model semantics with invalid bytes read as startup failure. |
| Linking with hiding for machines and traces; erasure commutes; agreement with `Games.Composition` and Wasm linking | `LinkSpec` (joint game, component views, external view), `TraceModel.link` (= hide of pull ⊓ pull), `Machine.link` (synchronised product with a legality monitor) (`Silmaril.Games.Abstract.Link`). Proved: `traces_link`, `denote_link_le`, **`denote_link`**: erasure commutes with linking for receptive components; `link_mono` (refinement is a congruence). Reentrancy, async interleaving and incompatible choices are fixed by the legality of the joint game. | Generic theorem proved. Agreement with the existing composition is proved: `sigLink E F G` with `SigBridge.strategyIso_comp` (generic link = `Strategy.comp`), and `Machine.denote_link_ofLTS` (`Silmaril.Games.Abstract.SigLink`). Wasm linking connects through the existing `link_is_composition_profile`. Still open: linking of phased (startup) models; an HTTP reading of erased composites. |
| Moria ports | `Silmaril.Semantics.TraceModels` (continuous logs, durations, the partial-writer monad with its prefix and run observations), `Silmaril.Semantics.ITree` (interaction trees as consistent sets of finite observations), `Silmaril.Semantics.ITreeInterpret` (interpretation of visible events into complete Elgot monads), all from imbrem/thesis `69a8126` (CC0, `NOTICES/imbrem-thesis`) | Ported unchanged except for the namespace. Still open: `Observational` (a Raw module); connecting ITree interpretation to `Machine` and `TraceModel`. |
| Async game (streams and futures); the simple synchronous submodel injects into the full model | `Game.interleave G ι` (concurrent tasks, each playing `G`; the shape of async export calls), `Game.Hom.single i` (the synchronous submodel) (`Silmaril.Games.Abstract.Interleave`). Generic: `comap_map_eq`, `map_injective`, `map_le_map_iff` (pushforward along an injective, Opponent-reflecting morphism is an order embedding). Proved: `single_map_injective`, `single_map_le_iff` (sync embeds, reflecting refinement), `exists_not_single` (with two tasks the async models are strictly richer) | Proved for task interleaving. Still open: stream and future events inside a task, and connecting to `Wasm.Component.Async`. |
| Version and feature comparison of semantic domains (validation and semantics) | Existing, proved (`Silmaril.Wasm.Unified.Versions.Thms`): `v10Emb_reduct`, `v20Emb_reduct`, `lime1Emb_reduct`, `coreEmb_reduct` (equations of models along signature inclusions), `fxEmb_refines` (Core 3.0 → WasmFX is a *refinement*, not an equation), `v10_sat_iff`, `lime1_sat_iff`, `fx_sat_univ`; feature order `v10 ≤ v20 ≤ v30 ≤ wasmFX`, `lime1 ≤ v30`, `lime1 ≰ v20` (`Silmaril.Wasm.Models.Features.Thms`). Open on `main`: `Task.wasmi_refines_loose`. These models run every version's code with Core 3.0, so the own-semantics inclusions are call-level, direction `sub` | No new theorem yet. Still open: transporting these embeddings to `TraceModel` denotations, phased with validation as startup. |
| Module variants: function-only exports, then memory, globals and tables as observable state | Function-only: scalar Core 3.0 instances (`Silmaril.Wasm.Abstract.Instance`). Exported state: `Game.withCells G N V` (`get`/`got`/`set` on named cells next to `G`), `Hom.ops`, `PHom.hideCells` (`Silmaril.Games.Abstract.Cells`). Proved: `map_ops_injective`, `map_ops_le_iff` (function-only models embed), `hide_map_ops` (hiding the cells gives the function-only model back), `exists_hide_eq_ne` (exported state is strictly finer than function-only observation) | Generic layer proved. Still open: Wasm instances with exported globals, memories and tables as `withCells` machines, aliasing between exports, and mutation during calls. |
| HTTP and TCP games; WASI reading agrees with `Servers.WasiHttp`; POSIX and container adapters | consume Servers modules | Stage 10, planned; coordinated with the Servers, UDP and CFG owners |

## Servers seam (stage 10)

The server stack is merged and owned by the Servers, UDP and CFG work. Stage 10
consumes it and redefines none of it:

- `Servers.Transport` (#178, #181): `TEv Addr`, including `TEv.err`;
  `TModel Addr := Set (TTrace Addr)` with `TModel.Refines` (inclusion); and
  partial readings `PMap α β := α → Option β` with `PMap.image` and
  `PMap.pull`.
- `Servers.OpenApi` (#179): the OpenAPI institution.
- `Servers.Tcp` (#183): the partial reading `h1Reading sel alpn p` from TCP
  traces to HTTP/1 traces, and `AtMost`, `AtLeast` and `Exactly` with their
  `mono` and `sat` lemmas. TLS and ALPN are explicit assumptions.
- `Servers.UdpTransport` / `Net.Udp` (#180): the UDP institution and a
  conditional DATAGRAM bridge. There is no refinement from packets to QUIC
  streams.
- `Servers.WasiHttp`, `Servers.WasiContext` and `Servers.Observe`: the wasi:http
  readings and server observations, including `Obs.initFail`.

**Seam.** Read a `TraceModel` (or the outcome-tagged `obs` of an `OMachine`) of
a wasi:http or wasi:sockets game into `Servers.Model` or `TModel` through a
`Context.Reading` or a `PMap`, so that `AtMost`, `AtLeast` and `Exactly` and the
existing lifts apply. The bridges keep the following explicit:

- **Startup.** Startup failure lands on `Obs.initFail`. Startup erasure
  forgets failure (`exists_erased_eq_startPart_ne`), so a reading must keep it.
- **Unions.** `Servers.Hosts.under` is a plain union. It agrees with
  `TraceModel` joins for nonempty host sets (`mem_sSup_of_nonempty`) and
  differs at `∅` (`mem_bot`).
- **Erased composites.** `Servers.WasiContext` keeps import events, so an HTTP
  reading of an erased composite (`Wasi.link`) is a separate theorem, owed by
  the linking stage.
- **Open binary-model tasks.** Concrete or byte-level claims carry the open
  `Task.*` hypotheses on `main` as assumptions: `WasiExamples.Task.wasmRuns`,
  `WasiBinaries.Task.binRuns` and `WasiFs.Static.Task.staticRuns`.
- **Liveness.** `TraceModel`s and `TModel`s are finite-trace safety models.
  "Eventually responds" is not expressible in them. The outcome tags
  (`Silmaril.Games.Abstract.Outcome`) record divergence, waiting and deadlock,
  but without fairness. Liveness claims go through `Servers.Live` and say so.

## What the finite-trace layer does not claim

- Equal trace models do not give equal must-behaviour: deadlock, silent
  divergence and "still computing" are identified (see
  `Silmaril.Games.Abstract.Game.Defs`).
- Equal trace models of nondeterministic machines do not give bisimilarity.
- Trace equality is coarser than equality of the underlying machines, and
  finer than any observation through a non-injective game morphism.

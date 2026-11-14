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
| Startup-sensitive and startup-erased observations; when they coincide | `Game.phased S G R` (startup in `S`, then `fail r` or `ready` then run in `G`), `Startup.erase` (a partial morphism), `erased`, `startPart`, `StartupIndep` (`Silmaril.Games.Abstract.Startup`). Proved: `eq_iff_startPart_erased`: for startup-independent models, model equality iff equal startup parts and equal erased observations. Counterexamples: `exists_erased_eq_startPart_ne` (erasure forgets failure), `exists_erased_eq_startPart_eq_ne` (erasure forgets dependence on startup inputs; independence is necessary) | Proved. Still open: an instance for `Games.Inst` / `Sig.withInst` and Wasm start functions. |
| Partial map bytes → trace sets; `WithTop` against lower sets; orientation examples | see convention 5 | Stage 4, planned |
| Linking with hiding for machines and traces; erasure commutes; agreement with `Games.Composition` and Wasm linking | synchronised product, parallel composition with hiding of trace models, reentrancy and init conditions | Stage 5, planned |
| Moria ports | `Silmaril.Semantics.TraceModels` (continuous logs, durations, the partial-writer monad with its prefix and run observations), `Silmaril.Semantics.ITree` (interaction trees as consistent sets of finite observations), `Silmaril.Semantics.ITreeInterpret` (interpretation of visible events into complete Elgot monads), all from imbrem/thesis `69a8126` (CC0, `NOTICES/imbrem-thesis`) | Ported unchanged except for the namespace. Still open: `Observational` (a Raw module); connecting ITree interpretation to `Machine` and `TraceModel`. |
| Async game (streams and futures); the simple synchronous submodel injects into the full model | non-alternating game, an injective `Game.Hom` (sync into async), `comap ∘ map = id` on the image | Stage 7, planned |
| Version and feature comparison of semantic domains (validation and semantics) | transport of `FeatureSet` order to denotation domains, using `Unified.Versions` embeddings; FX | Stage 8, planned |
| Module variants: function-only exports, then memory, globals and tables as observable state | exported-state moves (read, write, grow), aliasing | Stage 9, planned |
| HTTP and TCP games; WASI reading agrees with `Servers.WasiHttp`; POSIX and container adapters | consume Servers modules | Stage 10, planned; coordinated with the Servers, UDP and CFG owners |

## Servers seam (stage 10)

Notes from the server-side owners (PR #184 discussion). Stage 10 consumes these
and redefines none of them:

- **Seam.** A `Context.Reading` or `Transport.PMap` reads a `TraceModel` of a
  wasi:http or wasi:sockets game into `Servers.Model` or `TTrace`. The existing
  lift and refinement theorems then apply.
- **Startup.** The startup stage lands on `Servers.Observe.Obs.initFail`.
- **Unions.** `Servers.Hosts.under` is a plain union. It agrees with
  `TraceModel` joins for nonempty host sets (`mem_sSup_of_nonempty`) and
  differs at `∅` (`mem_bot`). Each bridge states which one it uses.
- **Erased composites.** `Servers.WasiContext` keeps import events. An HTTP
  reading of an erased composite (`Wasi.link`) needs its own theorem, which the
  linking stage owes.
- **Open hypotheses.** Concrete or byte-level claims carry the open
  hypotheses on `main` as explicit assumptions: `WasiExamples.Task.wasmRuns`,
  `WasiBinaries.Task.binRuns` and `WasiFs.Static.Task.staticRuns`.

## What the finite-trace layer does not claim

- Equal trace models do not give equal must-behaviour: deadlock, silent
  divergence and "still computing" are identified (see
  `Silmaril.Games.Abstract.Game.Defs`).
- Equal trace models of nondeterministic machines do not give bisimilarity.
- Trace equality is coarser than equality of the underlying machines, and
  finer than any observation through a non-injective game morphism.

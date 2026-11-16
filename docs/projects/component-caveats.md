# Wasm components: caveat ledger

What the component developments cover today, ordered by how much they block giving meaning to
real component binaries. Each entry gives the evidence and the next step. Status words:
**wired** (implemented and connected to the public acceptor and consequence APIs),
**unwired** (implemented but not connected), **missing**, **assumption** (a modelling choice)
and **gap** (a verification gap).

## Acceptance of component binaries

| item | status | evidence | next step |
|---|---|---|---|
| `accept(list<u8>)` binaries have meaning, imported or exported `accept` | **wired** on the reference machine (REF) | `Silmaril.Wasi.Accept.Ref`: `Accepted`, `refBytesSystem`, `acceptRun_sound`; `Ref/Examples.lean` decodes and validates a real `accept(list<u8>)` binary in the kernel and runs it (`#guard`), recording `"hi!"`; `AcceptedExport` (REF `exportBehaviours`) for `accept: func(list<u8>) -> bool`, with `#guard`ed runs returning `true`/`false` | see the gaps below; the exported form covers components without root imports, one call after instantiation |
| the component IR reads lists, strings, flags, resources | **missing** | `Binary/Lower/Defs.lean`: `defValTy` rejects them; the IR's `ValTy` has no list type | extend the IR's ABI with linear memory, or keep REF as the semantics of such components |
| an interface (game) denotation of REF components whose plays include **host-function calls** | **missing** (the bridge item 1 means) | REF has an *operational* reading of import calls: `Ref.Accepted`/`AcceptedTyped` observe the host function's arguments in machine runs. The *denotational* side is missing: no map from a REF component to a strategy `Strategy (nsig I) (nsig X)` (a WASI world model, `Layout.compModel`'s codomain) in which a call of a host function is a P-move with its lifted arguments. REF→strategy exists only for import-free `Simple` components (`SessionAdequacy`, `SessionStrat` in review) | define `refModel c : L.world.Model` from REF sessions with host calls, and prove adequacy `AcceptedTypedBytes ft prof c w ↔ w ∈ bytesLang (refModel c) acceptFn` |
| tuple-acceptor bridge (REF ↔ IR on the fragment both read) | **partly done**: prerequisites exposed | `tupleHiBytes` is read by both (kernel); REF passes `accept` a record, so the `list<u8>` notion is empty on it and `AcceptedTypedBytes` (through `bytesOf?`, the IR's `bytes?` reading) is needed; the host must be linked at the component's import type (`acceptLinkedProgAt`); the tuple acceptance is **kernel-checked end to end** (`tupleHi_accepts`) | (P2) `bytesOf? [toRefVal v] = args1 bytes? [v]` on IR values; (P3) an execution-based `CoreSem CoreMod` for lowered core modules (the library has only `topSem`, under which the IR side is not about the core code); (P4) REF↔IR adequacy with imports (`Simple.sound` is import-free). Then `AcceptedTypedBytes ft prof (decodeRef b) w ↔ w ∈ (ComponentAcceptor.ofComp C (lower b)).lang` |
| REF↔IR adequacy beyond `Simple` | **missing** | `Reference.Sound` (`Simple.sound`, numeric, import-free) | (P4) above |
| `RefSimple.ofRef?` (bytes → `Simple`) linked to the acceptor APIs | **unwired** | `JcoTool.RefSimple` | use it to check the two paths agree on scalar components |
| real Core 3.0 instances for the jco wrapper model (`Jco.Real.realInst`) linked to REF | **unwired** | `Jco.Real.Inst`, `Jco.Wrap` (`wrap_correct` for strings and `list<u8>` exports, relational) | prove that REF runs the `wrap md` component of a real module as `md.spec` |

## Verification gaps

| item | status | evidence | next step |
|---|---|---|---|
| end-to-end runs with linear memory over `ByteArray` memories are not kernel-checked | **closed for `acceptHiBytes`** | the run over `ByteArray` memories still exceeds the kernel; the same run over `KMem` memories is kernel-checked (`runHiK_true`) and carried to `core3 neverFail` by the REF machine simulation, giving `Ref.KMem.Examples.hi_mem` with no hypothesis (`docs/projects/wasm-memrep.md`) | other end-to-end runs through `core3K` |
| no proof that a REF component accepts *only* certain bytes | **gap** | `Accepted` is existential; only inclusions are shown | invariants of REF runs (e.g. a component that never calls `accept` accepts nothing) |
| upstream parity suites (wasm-tools, jco, wac, wasmtime) | **gap** | not run by CI (`docs/projects/wasm-components.md`) | run them in a scheduled job |

## Assumptions of `Ref.Accepted` and the typed environment

* **Host.** The host's `accept` is synchronous: it records its arguments and returns no result.
  It is REF's `mk_host_func` pattern. `acceptLinkedProgAt ft` supplies it at type `ft`, and
  REF's import check makes `ft` the component's import type.
* **Untyped environment (`Accepted`, `EnvLabel`): spurious runs.** Invoking an export on
  arguments that do not have its WIT type violates REF's precondition. Usually the machine
  stops with an `internal` fault, but not always: the exported `len == 3` acceptor returns
  `true` on the ill-typed list `[u32 300, u8 1, u8 2]` (`Ref/Typed/Examples.lean`, `#guard`).
* **Typed environment (`AcceptedTyped`, `TypedEnvLabel`), the intended semantics.** The host
  invokes exported functions only on arguments of their WIT type (`Val.HasType`, checked by
  the kernel-reducible `Val.typeCheckList?`), ticks and cancels. `AcceptedTyped → Accepted`,
  and `refTypedBytesSystem ≤ refBytesSystem`. The typed driver refuses ill-typed calls, as the
  tests show. Making the typed notions the default (replacing the untyped `refBytesSystem`) is
  a reviewer decision; both are kept for now.
* **Re-exported `accept`: intended.** A component that re-exports its `accept` import lets a
  typed host call `accept` through it, so it accepts every byte string the host passes. The
  IR reading (`Wasi.Accept.bytesLang`, import calls in plays of the wiring) counts these calls
  too. It is a property of the component's interface, not an ill-typed host (`#guard` test).
* **Validation and engine.** `refBytesSystem` validates at `Features.p2` and runs over the
  executable Core 3.0 engine `core3 neverFail`. `Accepted` itself holds for any core engine
  and any component choice profile.

## Streams, async and jco

Streams, futures, async lifting and lowering, the stream transformer algebra and the jco-style
toolchain are present (`Silmaril.Wasm.Component.Streams`, `Silmaril.Wasm.Jco`,
`Silmaril.Wasm.JcoTool`, the REF runtime `Reference.Runtime.Stream*`). These items are open:

* a concrete stream semantics (`StreamSem`) for generated modules;
* the link between generated or emitted binaries and the transformer models;
* the `DROPPED`-event gap of the `Async` model;
* parts of the jco adaptor against Core 3.0: stores, `memory.copy`, `if`, traps, and
  `latin1+utf16`.

See `docs/projects/wasm-components.md`.

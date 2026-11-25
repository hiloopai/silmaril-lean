module

public import Silmaril.Wasm.Component.Reference.HLinkedLink.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSessionObj.Thms
public import Silmaril.Games.Abstract.StratLegal.Defs
public import Silmaril.Games.Abstract.SessionExt.Defs
public import Silmaril.Games.Abstract.SessionRoute.Defs
public import Silmaril.Games.Abstract.SessionLinkAssoc.Defs
public import Silmaril.Games.Abstract.StratSession.Defs
public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DPair.Defs
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.RealMain

/-!
# Linked components with host imports through the generic session link: theorems

**Scope.** `HLinked2` (`HLinkedSession.Defs`) at core instances `Ie` (exporter) and `Ii`
(importer), every profile `P` unless stated. The generic link `HLinked2.linkO P l Ie Ii =
linkS (serverO P l Ie) (clientH P l Ii)` of `HLinkedLink.Defs`: the client is the importer's own
triple `SimpleI.impTripleS P l.imp l.wireH Ii` (`LinkedGLink`), the server the host passthrough
`SessionRoute.callS id (fun _ n => ExpSpec.sumAns n)` beside the exporter's triple, routed
(`SessionExt.routeS`). The objects of `HLinkedSessionObj`: the open triple `compTripleO` (every
legal host answer an Opponent move) and the host-realizable triple `compTripleS` (refusals since
the last answer `R`, forced refusals hidden).

**Hypotheses.** `l.WireTy` (wired imports to exports of their types, then exactly the host
imports) for the equalities; the session forms also take that `Ie`, `Ii` are instances of the two
core modules (`compSessionO`/`compSession` pick them); the composition forms take `profile o`.
Not needed: `Adequate`, determinism (except for the composition forms).

## Proved

1. **The open triple is the generic link** (`HLinked2.compTripleOR_eq_linkS`): exactly,

   `compTripleOR P l Ie Ii = mapStore storeEquiv (linkS (serverO P l Ie) (clientH P l Ii))`

   (finished behaviours, pending calls and productive streams), where `compTripleOR` is the
   saturated open triple before the legal restriction. An ill-typed question traps at once on
   both sides; a `SessSpec` round is a returning round of the client whose import calls are
   served by the server (`ExpRunH`: wired calls by the exporter's rounds, host calls by one host
   call each, with the same answer), the host calls being the log; the divergences of
   `RoundDivC` are the client's host-free divergence, the exporter's divergence inside a served
   wired call, and chatter (a client stream served with finitely many host calls, the round
   prefix extended to the last host call); the host chatter `RoundInfC` is a client stream served
   with infinitely many host calls. Pending calls: the link is saturated
   (`SessionLink.saturated_linkS`), and a host call the client waits on is a call prefix of the
   open triple, since its refusal traps the importer's core instance at once (`path_refuse`, by
   `fill_trap_reach'`).
2. **The open object** (`HLinked2.compTripleO_eq_linkS`, `HLinked2.compSessionO_eq_threadS`):

   `compTripleO P l Ie Ii = mapStore storeEquiv (StratLegal.restrict (hostLegal l.host) (linkO P l Ie Ii))`,

   `compSessionO P l = threadS (StratLegal.restrict (hostLegal l.host) (linkO P l Ie Ii)) (((), Ie.store), Ii.store)`.

   Generic lemma proved locally: `restrict_mapStore` (the legal restriction commutes with
   `mapStore`).
3. **The host-realizable object is the realizable restriction of the generic link**
   (`HLinked2.compTripleR_eq_realize`, `HLinked2.compTripleR_eq_realize_linkS`,
   `HLinked2.compSession_eq_threadS_realize`):

   `compTripleR P l Ie Ii = realize l.host (mapStore storeEquiv (linkO P l Ie Ii))`,

   `compSession P l = threadS (StratLegal.restrict (hostLegal l.host) (realize l.host (mapStore storeEquiv (linkO P l Ie Ii)))) (Ii.store, Ie.store, [])`.
4. **The difference, precisely** (`HLinked2.forced_not_visible`, `HLinked2.not_visRun_forced`):
   `realize` keeps the behaviours whose host calls are a `VisRun` (no forced refusal visible),
   records the refusals `R` in the store, and keeps a behaviour that refuses a call forced at the
   end of a `VisRun` and then traps with that last call removed from the log. So the realizable
   triple never shows a forced refusal, while the plain passthrough link, like the open triple,
   shows every refusal the importer's core instance makes. The bookkeeping `R` and the hiding are
   not a passthrough: they are the statement that the observing host is deterministic and typed
   (`HLinkedSessionObj`: a refusal keeps the host state).
5. **Sessions compose** (`HLinked2.comp_threadS_linkO`, `HLinked2.threadS_serverO`, `profile o`):
   the session of the generic link is the server's session composed with the client's,

   `(threadS (serverO (profile o) l Ie) ((), π)).comp (threadS (clientH (profile o) l Ii) u) = threadS (linkO (profile o) l Ie Ii) (((), π), u)`,

   and the server's session is the host passthrough handler `callH id sumAns` paired with the
   exporter's session, below the routing handler `SessionExt.routeH l.route`.
6. **The host-realizable object is a generic link with a stateful host**
   (`HLinked2.compTripleR_eq_linkR`, `HLinked2.compTripleS_eq_linkR`,
   `HLinked2.compSession_eq_threadS_linkR`, `WireTy`): with the realizability host
   `hostTripleR l.host` (state `R`; a call forced at `R` answered by a trap with no visible call;
   an unforced call visible, refused (`R := m :: R`) or legally answered when `m ∉ R`
   (`R := []`)) beside the exporter, `serverR := routeS l.route (hostTripleR l.host) expTripleH`,

   `compTripleR P l Ie Ii = mapStore (storeEquivR l.host) (linkS (serverR P l Ie) (clientH P l Ii))`,

   `compTripleS P l Ie Ii = mapStore (storeEquivR l.host) (StratLegal.restrict (hostLegal l.host) (linkR P l Ie Ii))`,

   `compSession P l = threadS (StratLegal.restrict (hostLegal l.host) (linkR P l Ie Ii)) (([], Ie.store), Ii.store)`.

   Exact (finished behaviours, pending calls, streams). Proof: rounds of `serverR` are rounds of
   the passthrough `serverO` with a `VisRun` log, or with a forced refusal hidden; a trap answer
   ends the client's round (`SimpleI.impTripleS_trapAbortsRound`), so a hidden refusal is last and
   the round returns the trap; a pending unforced host call, refused, traps at once
   (`refuse_mem`). At `profile o` (`HLinked2.comp_threadS_linkR`, `HLinked2.threadS_serverR`):
   `(threadS (serverR …) (R, π)).comp (threadS (clientH …) u) = threadS (linkR …) ((R, π), u)`,
   and `threadS (serverR …) (R, π)` is `threadS (hostTripleR l.host) R` paired with the exporter's
   session below `routeH l.route`.

## Not claimed

* **A plain passthrough for the realizable object.** `compTripleS` is not the restricted
  passthrough link `linkO` for any store map: such a link shows forced refusals (item 4); item 6
  is the correct generic form, with the stateful `hostTripleR`, which is not a handler. A
  concrete pair whose realizable objects agree and whose open objects differ is `HLinkedSep`'s
  (`HLinkedSep.compSession_eq`, `HLinkedSep.compSessionO_ne`); it is not used here.
* The composition forms on the legal interface (`linkS` commuting with `StratLegal.restrict`),
  and composition forms at nondeterministic profiles.
* Nested or n-ary components with host imports; the relation to `SessionHost.hostLinkS` (host
  calls answered and hidden), which applies once a host is fixed.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.{Basic, Fin, Inf, Pend, Main,
RealServer, RealMain}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS)
open Silmaril.Games.Abstract.SessionLinkAssoc (mapStore)
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- **The legal restriction commutes with transport along a store equivalence** (proved; a
generic fact, proved in this topic). -/
theorem restrict_mapStore {E : Sig.{0}} {S S' A B : Type} {L : (m : E.Op) → E.Ar m → Prop}
    (e : S ≃ S') (t : ObsTriple E S A B) :
    StratLegal.restrict L (mapStore e t) = mapStore e (StratLegal.restrict L t) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.restrict_mapStore e t

namespace HLinked2

variable {P : Profile} {l : HLinked2} {Ie Ii : ScalarInstance}

/-- **The open triple before restriction is the generic link** of the host passthrough beside the
exporter serving the importer, the stores reordered (proved, `WireTy`). -/
theorem compTripleOR_eq_linkS (hw : l.WireTy) :
    compTripleOR P l Ie Ii = mapStore storeEquiv (linkS (l.serverO P Ie) (l.clientH P Ii)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compTripleOR_eq hw

/-- **The open triple is the legal restriction of the generic link** (proved, `WireTy`). -/
theorem compTripleO_eq_linkS (hw : l.WireTy) :
    compTripleO P l Ie Ii =
      mapStore storeEquiv (StratLegal.restrict (hostLegal l.host) (l.linkO P Ie Ii)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compTripleO_eq_linkS hw

/-- **The open session object is the session of the restricted generic link** (proved,
`WireTy`, at the instances of the two core modules). -/
theorem compSessionO_eq_threadS (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (hw : l.WireTy) :
    compSessionO P l =
      threadS (StratLegal.restrict (hostLegal l.host) (l.linkO P Ie Ii))
        ((PUnit.unit, Ie.store), Ii.store) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compSessionO_eq_threadS hIe hIi hw

/-- **The host-realizable triple is the realizable restriction of the open triple** (proved). -/
theorem compTripleR_eq_realize : compTripleR P l Ie Ii = realize l.host (compTripleOR P l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compTripleR_eq_realize

/-- **The host-realizable triple is the realizable restriction of the generic link** (proved,
`WireTy`). -/
theorem compTripleR_eq_realize_linkS (hw : l.WireTy) :
    compTripleR P l Ie Ii = realize l.host (mapStore storeEquiv (l.linkO P Ie Ii)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compTripleR_eq_realize_linkS hw

/-- **The canonical session object is the session of the legal, realizable restriction of the
generic link** (proved, `WireTy`, at the instances of the two core modules). -/
theorem compSession_eq_threadS_realize (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (hw : l.WireTy) :
    compSession P l =
      threadS (StratLegal.restrict (hostLegal l.host)
          (realize l.host (mapStore storeEquiv (l.linkO P Ie Ii))))
        (Ii.store, Ie.store, []) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compSession_eq_threadS_realize hIe hIi hw

/-- **A forced refusal never continues a visible history** (proved). -/
theorem not_visRun_forced {h : Iface} {R R' R'' : List (sigN h.length).Op}
    {c : List (Call (sigN h.length))} {m : (sigN h.length).Op} {n : Option Payload}
    (hc : VisRun h R c R') (hf : Forced h R' m) : ¬ VisRun h R (c ++ [⟨m, n⟩]) R'' :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.not_visRun_forced hc hf

/-- **The host-realizable triple shows no forced refusal** (proved): in a finished behaviour
whose host calls are `c` followed by `m`, the call `m` is not forced after `c`. -/
theorem forced_not_visible {u π : Store Nat} {R R' : List (sigN l.host.length).Op}
    {q : Nat × Payload} {c : List (Call (sigN l.host.length))} {m : (sigN l.host.length).Op}
    {n : Option Payload} {e : End l.St (Payload ⊕ PUnit.{1})}
    (hx : (c ++ [⟨m, n⟩], e) ∈ (compTripleR P l Ie Ii).1 (u, π, R) q)
    (hc : VisRun l.host R c R') : ¬ Forced l.host R' m :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.forced_not_visible hx hc

/-- **The server's session is the host passthrough beside the exporter's session**, below the
routing handler (proved, `profile o`). -/
theorem threadS_serverO (o : GrowOracle) (π : Store Nat) :
    threadS (l.serverO (profile o) Ie) (PUnit.unit, π) =
      ((DStrategy.ofHandler (SessionRoute.callH (E := sigN l.host.length) id
          fun _ n => ExpSpec.sumAns n)).pair (threadS (l.expTripleH (profile o) Ie) π)).comp
        (DStrategy.ofHandler (SessionExt.routeH l.route)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.threadS_serverO o π

/-- **The session of the generic link is the server's session composed with the client's**
(proved, `profile o`). -/
theorem comp_threadS_linkO (o : GrowOracle) (π u : Store Nat) :
    (threadS (l.serverO (profile o) Ie) (PUnit.unit, π)).comp
        (threadS (l.clientH (profile o) Ii) u) =
      threadS (l.linkO (profile o) Ie Ii) ((PUnit.unit, π), u) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.comp_threadS_linkO o π u

/-! ## The host-realizable object as a generic link -/

/-- **The host-realizable triple is the generic link of the realizability host beside the
exporter serving the importer**, the stores reordered (proved, `WireTy`). -/
theorem compTripleR_eq_linkR (hw : l.WireTy) :
    compTripleR P l Ie Ii =
      mapStore (storeEquivR l.host) (linkS (l.serverR P Ie) (l.clientH P Ii)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compTripleR_eq_linkR hw

/-- **The host-realizable triple on the legal interface** is the legal restriction of the
host-realizable link (proved, `WireTy`). -/
theorem compTripleS_eq_linkR (hw : l.WireTy) :
    compTripleS P l Ie Ii =
      mapStore (storeEquivR l.host) (StratLegal.restrict (hostLegal l.host) (l.linkR P Ie Ii)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compTripleS_eq_linkR hw

/-- **The canonical session object is the session of the restricted host-realizable link**
(proved, `WireTy`, at the instances of the two core modules). -/
theorem compSession_eq_threadS_linkR (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (hw : l.WireTy) :
    compSession P l =
      threadS (StratLegal.restrict (hostLegal l.host) (l.linkR P Ie Ii))
        (([], Ie.store), Ii.store) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.compSession_eq_threadS_linkR hIe hIi hw

/-- **The host-realizable server's session is the realizability host's session beside the
exporter's**, below the routing handler (proved, `profile o`). -/
theorem threadS_serverR (o : GrowOracle) (R : List (sigN l.host.length).Op) (π : Store Nat) :
    threadS (l.serverR (profile o) Ie) (R, π) =
      ((threadS (hostTripleR l.host) R).pair (threadS (l.expTripleH (profile o) Ie) π)).comp
        (DStrategy.ofHandler (SessionExt.routeH l.route)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.threadS_serverR o R π

/-- **The host-realizable link is the server's session composed with the client's** (proved,
`profile o`). -/
theorem comp_threadS_linkR (o : GrowOracle) (R : List (sigN l.host.length).Op)
    (π u : Store Nat) :
    (threadS (l.serverR (profile o) Ie) (R, π)).comp (threadS (l.clientH (profile o) Ii) u) =
      threadS (l.linkR (profile o) Ie Ii) ((R, π), u) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.comp_threadS_linkR o R π u

end HLinked2

end Silmaril.Wasm.Component.Reference

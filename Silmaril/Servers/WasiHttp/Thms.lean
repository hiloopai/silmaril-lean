module

public import Silmaril.Servers.WasiHttp.Defs
public import Silmaril.Servers.Exchange.Thms
public import Silmaril.Servers.Calls.Thms
public import Silmaril.Wasi.Converse.Thms
import Silmaril.Proofs.Servers.WasiHttp.Codec

@[expose] public section

/-!
# The `wasi:http` proxy world: encodings and webs

* `pathOf_pathV`, `octetsOf_map`: a path-with-query encoded as an `option<string>`, and a
  string of octets, are read back.
* `oSet_twice`: once the outparam is set, a second `set` of it makes the response
  unobservable.
* `wasiServerB_refines`: reading request bodies refines the reading without them, so the
  specifications of `wasiServer σ` hold of `wasiServerB σ` (`Refines.sat`).
* `webOf_pathV`: the web of a server answers an outgoing request for an encoded authority and
  path with the status of the server's answer to that `GET`. A client component under the
  outgoing theory `httpTh3 (webOf f)` (`Silmaril.Wasi.Versions.Http3`) is thus specified against
  the server `f`; composing a client with a server component is not yet modelled.

**Linked systems** (`Silmaril.Wasi.link`):

* `linkServer_refines`, `linkServerB_refines`: the server of the component linked over any
  host `η` (any lower interface `Y`) refines the component read as a server; so
  `link_sat_of` and `link_satB_of`: a specification of `wasiServer σ` holds of `linkServer η σ`
  for **every host**.
* `mem_linkServer`: an answered run of a body over a concrete implementation is a trace of the
  body linked over the concrete host of that implementation (the linked server is not
  vacuous).

**Binaries** (`Runs σ h`: every play of `σ` is a play of the body `h`):

* `runs_refines`, `runs_refinesB`, `runs_link`: a strategy that runs `h` refines `h` as a
  server, alone and linked over any host, so a component binary whose denotation runs `h`
  satisfies every specification of `h`.
-/

namespace Silmaril.Servers.WasiHttp

open Silmaril.Servers.Exchange
open Silmaril.Wasi Silmaril.Servers.Calls
open Silmaril.Net.Http (Request Response)

/-- A path read back. -/
theorem pathOf_pathV (p : Option (List UInt8)) : pathOf (some [pathV p]) = p :=
  Proofs.Servers.WasiHttp.pathOf_pathV p

/-- A string of octets read back. -/
theorem octetsOf_map (p : List UInt8) :
    octetsOf (p.map fun b => Silmaril.Wasm.Component.Val.char (Char.ofNat b.toNat)) = p :=
  Proofs.Servers.WasiHttp.octetsOf_map p

/-- **`set` may be called once**: a second `set` of the outparam fails the reading. -/
theorem oSet_twice (o : BitVec 32) {st : OSt} (hs : st.set.isSome = true) (rh : BitVec 32) :
    oSet o st [.u32 o, .variant 0 (some (.u32 rh))] (some []) = none := by
  simp [oSet, hs]

/-- **The web of a server** on encoded requests. -/
theorem webOf_pathV (f : Request → Response) (a p : Option (List UInt8)) :
    webOf f (pathV a) (pathV p) = .status (BitVec.ofNat 16 (f (getAt a p)).status) := by
  simp only [webOf, pathOf_pathV]

/-- **Reading request bodies refines** the reading without them. -/
theorem wasiServerB_refines {X : Set FnName}
    (σ : Silmaril.Games.Strategy (Silmaril.Wasi.nsig proxyImports) (Silmaril.Wasi.nsig X)) :
    Refines (wasiServerB σ) (wasiServer σ) :=
  fun _ ⟨s, hs, hT, hF⟩ => ⟨s, hs, hT, hF.imp fun _ _ h => h.1⟩

/-! ## Linked systems -/

section Link

variable {Y : Silmaril.Games.Sig.{0}} {X : Set FnName}

/-- **The server of a linked system refines the component read as a server.** -/
theorem linkServer_refines (η : Host Y proxyImports)
    (σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)) :
    Refines (linkServer η σ) (wasiServer σ) :=
  fun _ ⟨_, _, u, hu, _, _, hF⟩ => ⟨u, hu, fun _ _ => trivial, hF⟩

/-- The same, reading request bodies. -/
theorem linkServerB_refines (η : Host Y proxyImports)
    (σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)) :
    Refines (linkServerB η σ) (wasiServerB σ) :=
  fun _ ⟨_, _, u, hu, _, _, hF⟩ => ⟨u, hu, fun _ _ => trivial, hF⟩

/-- **Correct over every host**: a specification of the component holds of its link over any
host. -/
theorem link_sat_of {σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)}
    {φ : Exchange.Sen httpIface} (h : Sat (wasiServer σ) φ) (η : Host Y proxyImports) :
    Sat (linkServer η σ) φ :=
  (linkServer_refines η σ).sat h

/-- The same, reading request bodies. -/
theorem link_satB_of {σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)}
    {φ : Exchange.Sen httpIface} (h : Sat (wasiServerB σ) φ) (η : Host Y proxyImports) :
    Sat (linkServerB η σ) φ :=
  (linkServerB_refines η σ).sat h

/-- **The linked server is not vacuous**: an answered run of a body over an implementation is a
trace of the body linked over the concrete host of the implementation. -/
theorem mem_linkServer {h : Body proxyImports X} {q : (nsig X).Op} {impl : Impl}
    (ha : answered ⟨q.1.1, q.2, (runP impl [] (h q)).1, (runP impl [] (h q)).2⟩ = true)
    {x : Exch httpIface} (hx : Obs ⟨q.1.1, q.2, (runP impl [] (h q)).1, (runP impl [] (h q)).2⟩ x) :
    [x] ∈ linkServer (Y := Y) (concrete impl) (ofBody h) := by
  obtain ⟨s, hs, hc, ht⟩ := exists_play (leads_runP impl [] (h q))
  refine ⟨hplay s, hplay_mem_ofPred (prefixClosed_follows impl) hs ?_, s, hs, xplay s,
    zip_split s, ?_⟩
  · rw [ht, hostView_events]
    simpa using follows_runP impl (h q) [] (prefixClosed_follows impl).1
  · rw [hc, List.filter_cons_of_pos ha, List.filter_nil]
    exact .cons hx .nil

/-! ## Binaries -/

/-- **A strategy that runs a body refines it** as a server. -/
theorem runs_refines {σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)}
    {h : Body proxyImports X} (hr : Runs σ h) : Refines (wasiServer σ) (wasiServer (ofBody h)) :=
  fun _ ⟨s, hs, hT, hF⟩ => ⟨s, hr s hs, hT, hF⟩

/-- The same, reading request bodies. -/
theorem runs_refinesB {σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)}
    {h : Body proxyImports X} (hr : Runs σ h) :
    Refines (wasiServerB σ) (wasiServerB (ofBody h)) :=
  fun _ ⟨s, hs, hT, hF⟩ => ⟨s, hr s hs, hT, hF⟩

/-- Linked over any host, a strategy that runs a body refines the body read as a server. -/
theorem runs_link {σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)}
    {h : Body proxyImports X} (hr : Runs σ h) (η : Host Y proxyImports) :
    Refines (linkServer η σ) (wasiServer (ofBody h)) :=
  fun _ ht => runs_refines hr (linkServer_refines η σ ht)

end Link

end Silmaril.Servers.WasiHttp
